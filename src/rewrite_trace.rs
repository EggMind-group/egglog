use crate::prelude::Action;
use crate::{
    Command, CommandOutput, DefaultCost, EGraph, Error, Parser, ReportLevel, Schedule,
};
use serde::Serialize;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug)]
pub struct RewriteTraceConfig {
    pub round_iters: usize,
    pub max_rounds: usize,
    pub ruleset: Option<String>,
    pub with_proofs: bool,
    pub strict_mode: bool,
    pub seminaive: bool,
    pub report_level: ReportLevel,
    pub fact_directory: Option<PathBuf>,
    pub term_encoding: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct RewriteTraceRound {
    pub round_index: usize,
    pub cost_delta: i128,
    pub compressed_rule_chain_text: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct RewriteTraceReport {
    pub initial_cost: DefaultCost,
    pub rounds: Vec<RewriteTraceRound>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct RoundMotifInput {
    round_index: usize,
    compressed_rule_chain: Vec<CompressedChainItem>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct CompressedChainItem {
    pub kind: String,
    pub rules: Vec<String>,
    pub repeat: usize,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct RepeatedMotifSummary {
    pub rules: Vec<String>,
    pub occurrences: usize,
    pub rounds: usize,
}

pub fn run_rewrite_trace_from_path(
    egg_path: &Path,
    config: &RewriteTraceConfig,
) -> Result<RewriteTraceReport, Error> {
    let program_text =
        fs::read_to_string(egg_path).map_err(|err| Error::BackendError(err.to_string()))?;
    run_rewrite_trace(
        Some(egg_path.to_string_lossy().into_owned()),
        &program_text,
        config,
    )
}

pub fn run_rewrite_trace(
    filename: Option<String>,
    program_text: &str,
    config: &RewriteTraceConfig,
) -> Result<RewriteTraceReport, Error> {
    if config.round_iters == 0 {
        return Err(Error::BackendError(
            "rewrite trace requires --rewrite-trace-iters > 0".to_string(),
        ));
    }
    if config.max_rounds == 0 {
        return Err(Error::BackendError(
            "rewrite trace requires --rewrite-trace-rounds > 0".to_string(),
        ));
    }

    let mut parser = Parser::default();
    let commands = parser.get_program_from_string(filename.clone(), program_text)?;
    let _initial_expr = extract_seed_expr(&commands)?;
    let ruleset = config
        .ruleset
        .clone()
        .or_else(|| extract_default_ruleset(&commands))
        .unwrap_or_default();
    let mut base_program = render_base_program(&commands, filename.as_deref());
    if !ruleset.is_empty() && !ruleset_is_declared(&commands, &ruleset) {
        base_program = format!("(ruleset {ruleset})\n{base_program}");
    }

    let initial_extract_program = build_initial_extract_program(&base_program);
    let initial_outputs = run_program(&initial_extract_program, filename.clone(), config, false)?;
    let (_initial_best_expr, initial_cost) = extract_best_output(&initial_outputs)?;

    let mut rounds = Vec::with_capacity(config.max_rounds);
    let mut previous_cost = initial_cost;
    for round_index in 1..=config.max_rounds {
        let cumulative_iters = round_index * config.round_iters;
        let snapshot_program = build_extract_program(&base_program, &ruleset, cumulative_iters);
        let snapshot_outputs =
            run_program(&snapshot_program, filename.clone(), config, false)?;
        let (best_expr, best_cost) = extract_best_output(&snapshot_outputs)?;

        let (proof_available, proof_error, raw_rule_trace) = if config.with_proofs {
            let proof_program =
                build_proof_program(&base_program, &ruleset, cumulative_iters, &best_expr);
            match run_program(&proof_program, filename.clone(), config, true) {
                Ok(outputs) => (true, None, extract_rule_trace_from_outputs(&outputs)),
                Err(err) => (false, Some(err.to_string()), Vec::new()),
            }
        } else {
            (false, None, Vec::new())
        };
        let compressed_rule_chain = compress_rule_trace(&raw_rule_trace, 4);
        let compressed_rule_chain_text = format_compressed_rule_chain(&compressed_rule_chain);
        let cost_delta = previous_cost as i128 - best_cost as i128;

        rounds.push(RewriteTraceRound {
            round_index,
            cost_delta,
            compressed_rule_chain_text,
        });
        let _ = (proof_available, proof_error);
        let _ = compressed_rule_chain;
        previous_cost = best_cost;
    }

    Ok(RewriteTraceReport {
        initial_cost,
        rounds,
    })
}

fn configured_egraph(config: &RewriteTraceConfig, force_proofs: bool) -> EGraph {
    let mut egraph = EGraph::default();
    if config.term_encoding {
        egraph = egraph.with_term_encoding_enabled();
    }
    if config.with_proofs || force_proofs {
        egraph = egraph.with_proofs_enabled();
        egraph = egraph.with_proof_rule_trace_only();
    }
    egraph.fact_directory.clone_from(&config.fact_directory);
    egraph.seminaive = config.seminaive;
    egraph.set_report_level(config.report_level);
    if config.strict_mode {
        egraph.set_strict_mode(true);
    }
    egraph
}

fn run_program(
    program: &str,
    filename: Option<String>,
    config: &RewriteTraceConfig,
    force_proofs: bool,
) -> Result<Vec<CommandOutput>, Error> {
    let mut egraph = configured_egraph(config, force_proofs);
    egraph.parse_and_run_program(filename, program)
}

fn extract_seed_expr(commands: &[Command]) -> Result<String, Error> {
    for command in commands {
        if let Command::Action(Action::Let(_, name, expr)) = command {
            if name == "$expr" {
                return Ok(expr.to_string());
            }
        }
    }
    Err(Error::BackendError(
        "rewrite trace requires a global `(let $expr ...)` seed expression".to_string(),
    ))
}

fn extract_default_ruleset(commands: &[Command]) -> Option<String> {
    for command in commands {
        if let Command::RunSchedule(Schedule::Run(_, config)) = command {
            return Some(config.ruleset.clone());
        }
    }
    None
}

fn render_base_program(commands: &[Command], filename: Option<&str>) -> String {
    let parent_dir = filename
        .and_then(|path| Path::new(path).parent().map(Path::to_path_buf));
    commands
        .iter()
        .filter(|command| !is_runtime_command(command))
        .map(|command| match command {
            Command::Include(_span, path) => {
                let include_path = Path::new(path);
                if include_path.is_absolute() {
                    format!("(include {:?})", include_path.to_string_lossy())
                } else if let Some(parent) = &parent_dir {
                    let absolute = parent.join(include_path);
                    format!("(include {:?})", absolute.to_string_lossy())
                } else {
                    command.to_string()
                }
            }
            _ => command.to_string(),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn ruleset_is_declared(commands: &[Command], ruleset: &str) -> bool {
    commands.iter().any(|command| match command {
        Command::AddRuleset(_, name) => name == ruleset,
        Command::UnstableCombinedRuleset(_, name, _) => name == ruleset,
        _ => false,
    })
}

fn is_runtime_command(command: &Command) -> bool {
    matches!(
        command,
        Command::RunSchedule(_)
            | Command::Extract(..)
            | Command::PrintOverallStatistics(..)
            | Command::Check(..)
            | Command::Prove(..)
            | Command::ProveExists(..)
            | Command::PrintFunction(..)
            | Command::PrintSize(..)
            | Command::Output { .. }
            | Command::Push(..)
            | Command::Pop(..)
            | Command::Fail(..)
    )
}

fn build_extract_program(base_program: &str, ruleset: &str, cumulative_iters: usize) -> String {
    if ruleset.is_empty() {
        format!("{base_program}\n(run {cumulative_iters})\n(extract $expr)\n")
    } else {
        format!(
            "{base_program}\n(run {ruleset} {cumulative_iters})\n(extract $expr)\n"
        )
    }
}

fn build_initial_extract_program(base_program: &str) -> String {
    format!("{base_program}\n(extract $expr)\n")
}

fn build_proof_program(
    base_program: &str,
    ruleset: &str,
    cumulative_iters: usize,
    best_expr: &str,
) -> String {
    if ruleset.is_empty() {
        format!(
            "{base_program}\n(run {cumulative_iters})\n(let $to {best_expr})\n(prove (= $expr $to))\n"
        )
    } else {
        format!(
            "{base_program}\n(run {ruleset} {cumulative_iters})\n(let $to {best_expr})\n(prove (= $expr $to))\n"
        )
    }
}

fn extract_best_output(outputs: &[CommandOutput]) -> Result<(String, DefaultCost), Error> {
    for output in outputs.iter().rev() {
        if let CommandOutput::ExtractBest(termdag, cost, term) = output {
            return Ok((termdag.to_string(*term), *cost));
        }
    }
    Err(Error::BackendError(
        "rewrite trace expected an extract result but none was produced".to_string(),
    ))
}

fn extract_rule_trace_from_outputs(outputs: &[CommandOutput]) -> Vec<String> {
    for output in outputs.iter().rev() {
        if let CommandOutput::ProveExistsRuleTrace(rule_trace) = output {
            return rule_trace.clone();
        }
        if let CommandOutput::ProveExists { proof_store, proof_id } = output {
            return proof_store.rule_trace(*proof_id);
        }
    }
    Vec::new()
}

fn compress_rule_trace(rule_trace: &[String], max_window: usize) -> Vec<CompressedChainItem> {
    let mut items = Vec::new();
    let mut i = 0usize;
    while i < rule_trace.len() {
        let mut same_rule_repeat = 1usize;
        while i + same_rule_repeat < rule_trace.len()
            && rule_trace[i + same_rule_repeat] == rule_trace[i]
        {
            same_rule_repeat += 1;
        }
        if same_rule_repeat >= 2 {
            items.push(CompressedChainItem {
                kind: "rule".to_string(),
                rules: vec![rule_trace[i].clone()],
                repeat: same_rule_repeat,
            });
            i += same_rule_repeat;
            continue;
        }

        let max_len = usize::min(max_window, rule_trace.len() - i);
        let mut chosen_len = 1usize;
        let mut chosen_repeat = 1usize;

        for len in (2..=max_len).rev() {
            let slice = &rule_trace[i..i + len];
            let mut repeat = 1usize;
            while i + (repeat + 1) * len <= rule_trace.len()
                && &rule_trace[i + repeat * len..i + (repeat + 1) * len] == slice
            {
                repeat += 1;
            }
            if repeat >= 2 {
                chosen_len = len;
                chosen_repeat = repeat;
                break;
            }
        }

        let rules = rule_trace[i..i + chosen_len].to_vec();
        let kind = if chosen_len == 1 {
            "rule".to_string()
        } else {
            "motif".to_string()
        };
        items.push(CompressedChainItem {
            kind,
            rules,
            repeat: chosen_repeat,
        });
        i += chosen_len * chosen_repeat;
    }
    items
}

fn format_compressed_rule_chain(items: &[CompressedChainItem]) -> String {
    items
        .iter()
        .map(|item| {
            let body = if item.rules.len() == 1 {
                item.rules[0].clone()
            } else {
                format!("({})", item.rules.join(" -> "))
            };
            if item.repeat > 1 {
                format!("{body} x{}", item.repeat)
            } else {
                body
            }
        })
        .collect::<Vec<_>>()
        .join(" -> ")
}

#[allow(dead_code)]
fn build_repeated_motif_catalog(rounds: &[RoundMotifInput]) -> Vec<RepeatedMotifSummary> {
    use std::collections::{BTreeMap, BTreeSet};

    let mut counts: BTreeMap<Vec<String>, usize> = BTreeMap::new();
    let mut round_support: BTreeMap<Vec<String>, BTreeSet<usize>> = BTreeMap::new();
    for round in rounds {
        for item in &round.compressed_rule_chain {
            if item.rules.len() <= 1 {
                continue;
            }
            *counts.entry(item.rules.clone()).or_insert(0) += item.repeat;
            round_support
                .entry(item.rules.clone())
                .or_default()
                .insert(round.round_index);
        }
    }
    let mut summaries: Vec<_> = counts
        .into_iter()
        .map(|(rules, occurrences)| RepeatedMotifSummary {
            rounds: round_support.get(&rules).map_or(0, |s| s.len()),
            rules,
            occurrences,
        })
        .collect();
    summaries.sort_by(|a, b| {
        b.rounds
            .cmp(&a.rounds)
            .then_with(|| b.occurrences.cmp(&a.occurrences))
            .then_with(|| b.rules.len().cmp(&a.rules.len()))
            .then_with(|| a.rules.cmp(&b.rules))
    });
    summaries
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config(with_proofs: bool) -> RewriteTraceConfig {
        RewriteTraceConfig {
            round_iters: 1,
            max_rounds: 2,
            ruleset: Some("opt".to_string()),
            with_proofs,
            strict_mode: false,
            seminaive: true,
            report_level: ReportLevel::TimeOnly,
            fact_directory: None,
            term_encoding: false,
        }
    }

    #[test]
    fn trace_report_extracts_round_snapshots() {
        let program = r#"
            (datatype Math
              (Num i64)
              (Add Math Math)
            )
            (ruleset opt)
            (rewrite (Add ?a (Num 0)) ?a :ruleset opt)
            (let $expr (Add (Num 7) (Num 0)))
        "#;

        let report = run_rewrite_trace(None, program, &config(false)).unwrap();
        assert_eq!(report.initial_cost, 5);
        assert_eq!(report.rounds.len(), 2);
        assert_eq!(report.rounds[0].cost_delta, 3);
        assert_eq!(
            report.rounds[0].compressed_rule_chain_text,
            ""
        );
    }

    #[test]
    fn trace_report_can_request_cumulative_proofs() {
        let program = r#"
            (datatype Math
              (Num i64)
              (Add Math Math)
            )
            (ruleset opt)
            (rewrite (Add ?a (Num 0)) ?a :ruleset opt)
            (let $expr (Add (Num 7) (Num 0)))
        "#;

        let report = run_rewrite_trace(None, program, &config(true)).unwrap();
        assert_eq!(report.rounds.len(), 2);
        assert_eq!(report.initial_cost, 5);
        assert_eq!(report.rounds[0].cost_delta, 3);
        assert_eq!(
            report.rounds[0].compressed_rule_chain_text,
            "(rewrite (Add ?a (Num 0)) ?a :ruleset opt)"
        );
    }

    #[test]
    fn compress_rule_trace_collapses_repeated_rules_and_motifs() {
        let trace = vec![
            "A".to_string(),
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
            "B".to_string(),
            "C".to_string(),
            "D".to_string(),
        ];
        let compressed = compress_rule_trace(&trace, 4);
        assert_eq!(
            compressed,
            vec![
                CompressedChainItem {
                    kind: "rule".to_string(),
                    rules: vec!["A".to_string()],
                    repeat: 2,
                },
                CompressedChainItem {
                    kind: "motif".to_string(),
                    rules: vec!["B".to_string(), "C".to_string()],
                    repeat: 2,
                },
                CompressedChainItem {
                    kind: "rule".to_string(),
                    rules: vec!["D".to_string()],
                    repeat: 1,
                },
            ]
        );
        assert_eq!(format_compressed_rule_chain(&compressed), "A x2 -> (B -> C) x2 -> D");
    }

    #[test]
    fn compress_rule_trace_prefers_single_rule_runs_over_degenerate_motifs() {
        let trace = vec![
            "swap".to_string(),
            "swap".to_string(),
            "swap".to_string(),
            "swap".to_string(),
        ];
        assert_eq!(
            compress_rule_trace(&trace, 4),
            vec![CompressedChainItem {
                kind: "rule".to_string(),
                rules: vec!["swap".to_string()],
                repeat: 4,
            }]
        );
    }

    #[test]
    fn repeated_motif_catalog_tracks_cross_round_support() {
        let rounds = vec![
            RoundMotifInput {
                round_index: 1,
                compressed_rule_chain: vec![
                    CompressedChainItem {
                        kind: "motif".to_string(),
                        rules: vec!["B".to_string(), "C".to_string()],
                        repeat: 1,
                    },
                    CompressedChainItem {
                        kind: "rule".to_string(),
                        rules: vec!["D".to_string()],
                        repeat: 2,
                    },
                ],
            },
            RoundMotifInput {
                round_index: 2,
                compressed_rule_chain: vec![CompressedChainItem {
                    kind: "motif".to_string(),
                    rules: vec!["B".to_string(), "C".to_string()],
                    repeat: 2,
                }],
            },
        ];

        assert_eq!(
            build_repeated_motif_catalog(&rounds),
            vec![RepeatedMotifSummary {
                rules: vec!["B".to_string(), "C".to_string()],
                occurrences: 3,
                rounds: 2,
            }]
        );
    }
}
