//! The state behind the prompt: definitions, settings and commands.

use std::time::Instant;

use levy_core::dot::to_dot;
use levy_core::script::statements;
use levy_core::translate::translate;
use levy_core::{Definitions, Halt, Machine, ParseError, Rule, Statement, Term, reference};

/// Work allowed per evaluation unless `:fuel` says otherwise, in steps of the
/// machine's walk. This is a few seconds, and bounds the memory as well.
const DEFAULT_FUEL: u64 = 100_000_000;
/// Terms larger than this many nodes are summarized instead of printed.
const PRINT_LIMIT: usize = 2_000;
/// Beta-steps `:trace` prints before it stops.
const TRACE_LIMIT: u64 = 100;

const HELP: &str = "\
Enter a term to reduce it to normal form, or `name = term` to define a name.

  \\x. body  or  λx. body    abstraction; `\\x y. body` binds several names
  f a b                      application, associating to the left
  3                          the Church numeral for 3
  -- text                    comment

Commands:
  :compare TERM   reduce TERM both optimally and in normal order
  :trace TERM     show the term after each β-step
  :dot TERM       print the net of TERM in Graphviz format
  :load FILE      run the statements of a file
  :defs           list the definitions
  :fuel [N]       show or set the limit on the work of one evaluation
  :help           show this text
  :quit           leave";

/// What the session answers to one input.
#[derive(Debug, Default)]
pub struct Reply {
    pub lines: Vec<String>,
    pub quit: bool,
}

pub struct Session {
    definitions: Definitions,
    fuel: u64,
}

impl Session {
    pub fn new() -> Session {
        Session {
            definitions: Definitions::new(),
            fuel: DEFAULT_FUEL,
        }
    }

    /// Runs one line of input: a command, a definition or a term.
    pub fn execute(&mut self, input: &str) -> Reply {
        let mut reply = Reply::default();
        let input = input.trim();
        match input.strip_prefix(':') {
            Some(command) => {
                let (name, argument) = command
                    .split_once(char::is_whitespace)
                    .unwrap_or((command, ""));
                reply.quit = self.command(name, argument.trim(), &mut reply.lines);
            }
            None => self.statement(input, &mut reply.lines),
        }
        reply
    }

    /// Runs a command and reports whether it asks to quit.
    fn command(&mut self, name: &str, argument: &str, out: &mut Vec<String>) -> bool {
        match name {
            "q" | "quit" | "exit" => return true,
            "h" | "help" | "?" => out.push(HELP.to_owned()),
            "defs" => self.list_definitions(out),
            "fuel" => self.set_fuel(argument, out),
            "load" => self.load(argument, out),
            "compare" | "trace" | "dot" => match self.definitions.parse(argument) {
                Ok(term) => match name {
                    "compare" => self.compare(&term, out),
                    "trace" => self.trace(&term, out),
                    _ => self.dot(&term, out),
                },
                Err(error) => out.push(describe(argument, &error)),
            },
            _ => out.push(format!("unknown command `:{name}`; try `:help`")),
        }
        false
    }

    fn statement(&mut self, source: &str, out: &mut Vec<String>) {
        match self.definitions.statement(source) {
            Ok(None) => {}
            Ok(Some(Statement::Define(name, term))) => {
                let free = term.free_names();
                if !free.is_empty() {
                    out.push(format!(
                        "note: `{name}` has free variables: {}",
                        free.join(", ")
                    ));
                }
                self.definitions.define(name, term);
            }
            Ok(Some(Statement::Evaluate(term))) => self.evaluate(&term, out),
            Err(error) => out.push(describe(source, &error)),
        }
    }

    fn evaluate(&self, term: &Term, out: &mut Vec<String>) {
        let Some(mut machine) = load(term, out) else {
            return;
        };
        let started = Instant::now();
        let outcome = machine.normalize(self.fuel);
        let elapsed = started.elapsed();
        let stats = machine.stats();
        match outcome {
            Ok(normal) => {
                out.push(show(&normal));
                out.extend(numeral(&normal));
                out.push(format!(
                    "{} β-steps, {} bookkeeping steps, {elapsed:.1?}",
                    stats.beta,
                    stats.bookkeeping()
                ));
            }
            Err(halt) => out.push(self.explain(halt, &machine)),
        }
    }

    fn compare(&self, term: &Term, out: &mut Vec<String>) {
        let Some(mut machine) = load(term, out) else {
            return;
        };
        let optimal = machine.normalize(self.fuel);
        let stats = machine.stats();
        match &optimal {
            Ok(normal) => {
                out.push(show(normal));
                out.extend(numeral(normal));
                out.push(format!(
                    "optimal:      {} β-steps, {} bookkeeping steps",
                    stats.beta,
                    stats.bookkeeping()
                ));
            }
            Err(halt) => out.push(format!("optimal:      {}", self.explain(*halt, &machine))),
        }
        match reference::normalize(term, self.fuel) {
            Ok(outcome) => {
                out.push(format!(
                    "normal order: {} β-steps in {} families",
                    outcome.beta_steps, outcome.families
                ));
                if optimal.is_ok_and(|normal| normal != outcome.normal_form) {
                    out.push("internal error: the two normal forms differ".to_owned());
                }
            }
            Err(_) => out.push(format!(
                "normal order: gave up after {} units of work",
                self.fuel
            )),
        }
    }

    fn trace(&self, term: &Term, out: &mut Vec<String>) {
        let Some(mut machine) = load(term, out) else {
            return;
        };
        out.push(format!("  {}", show(term)));
        loop {
            let stats = machine.stats();
            if stats.interactions() >= self.fuel {
                out.push(self.explain(Halt::OutOfFuel, &machine));
                return;
            }
            if stats.beta >= TRACE_LIMIT {
                out.push(format!("stopped after {TRACE_LIMIT} β-steps"));
                return;
            }
            match machine.step() {
                Ok(None) => break,
                Ok(Some(Rule::Beta)) => match machine.readback() {
                    Ok(reduct) => out.push(format!("β {}", show(&reduct))),
                    Err(halt) => {
                        out.push(self.explain(halt, &machine));
                        return;
                    }
                },
                Ok(Some(_)) => {}
                Err(halt) => {
                    out.push(self.explain(halt, &machine));
                    return;
                }
            }
        }
        let stats = machine.stats();
        out.push(format!(
            "{} β-steps, {} bookkeeping steps",
            stats.beta,
            stats.bookkeeping()
        ));
    }

    fn dot(&self, term: &Term, out: &mut Vec<String>) {
        match translate(term) {
            Ok(net) => out.push(to_dot(&net).trim_end().to_owned()),
            Err(error) => out.push(format!("error: {error}")),
        }
    }

    fn load(&mut self, path: &str, out: &mut Vec<String>) {
        if path.is_empty() {
            out.push("usage: :load FILE".to_owned());
            return;
        }
        let script = match std::fs::read_to_string(path) {
            Ok(script) => script,
            Err(error) => {
                out.push(format!("error: cannot read `{path}`: {error}"));
                return;
            }
        };
        let before = self.definitions.len();
        for (line, source) in statements(&script) {
            match self.definitions.statement(source) {
                Ok(None) => {}
                Ok(Some(Statement::Define(name, term))) => self.definitions.define(name, term),
                Ok(Some(Statement::Evaluate(term))) => self.evaluate(&term, out),
                Err(error) => {
                    out.push(format!("{path}:{line}: error: {}", error.message));
                    return;
                }
            }
        }
        let added = self.definitions.len() - before;
        out.push(format!("loaded `{path}`: {added} new definitions"));
    }

    fn list_definitions(&self, out: &mut Vec<String>) {
        if self.definitions.is_empty() {
            out.push("no definitions yet".to_owned());
        }
        for (name, term) in self.definitions.iter() {
            out.push(format!("{name} = {}", show(term)));
        }
    }

    fn set_fuel(&mut self, argument: &str, out: &mut Vec<String>) {
        if argument.is_empty() {
            out.push(format!("{} steps per evaluation", self.fuel));
            return;
        }
        match argument.replace('_', "").parse() {
            Ok(fuel) => self.fuel = fuel,
            Err(_) => out.push(format!("error: `{argument}` is not a number")),
        }
    }

    fn explain(&self, halt: Halt, machine: &Machine) -> String {
        match halt {
            Halt::OutOfFuel => format!(
                "no normal form within {} steps ({} interactions, {} β-steps); \
                 raise the limit with `:fuel`",
                self.fuel,
                machine.stats().interactions(),
                machine.stats().beta
            ),
            Halt::Interrupted => "interrupted".to_owned(),
            Halt::Malformed(reason) => format!("internal error: malformed net: {reason}"),
        }
    }
}

fn load(term: &Term, out: &mut Vec<String>) -> Option<Machine> {
    match Machine::new(term) {
        Ok(machine) => Some(machine),
        Err(error) => {
            out.push(format!("error: {error}"));
            None
        }
    }
}

fn show(term: &Term) -> String {
    term.abbreviated(PRINT_LIMIT)
}

fn numeral(term: &Term) -> Option<String> {
    term.as_church()
        .map(|value| format!("church numeral {value}"))
}

/// A parse error as a message, with a caret under the offending place when
/// the source fits on one line.
fn describe(source: &str, error: &ParseError) -> String {
    let message = format!("error: {}", error.message);
    if source.contains('\n') {
        return message;
    }
    let column = source
        .char_indices()
        .take_while(|(offset, _)| *offset < error.offset)
        .count();
    format!("{message}\n  {source}\n  {}^", " ".repeat(column))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(session: &mut Session, input: &str) -> Vec<String> {
        session.execute(input).lines
    }

    #[test]
    fn evaluates_terms() {
        let mut session = Session::new();
        let lines = run(&mut session, r"(\x. x) y");
        assert_eq!(lines[0], "y");
        assert!(lines[1].starts_with("1 β-steps, "), "{lines:?}");
    }

    #[test]
    fn recognizes_church_numerals() {
        let mut session = Session::new();
        let lines = run(&mut session, "2 2 2");
        assert_eq!(lines[1], "church numeral 16");
    }

    #[test]
    fn definitions_persist() {
        let mut session = Session::new();
        assert!(run(&mut session, r"twice = \f x. f (f x)").is_empty());
        assert_eq!(run(&mut session, "twice twice")[1], "church numeral 4");
        assert_eq!(run(&mut session, ":defs"), ["twice = λf x. f (f x)"]);
    }

    #[test]
    fn free_variables_in_definitions_are_noted() {
        let mut session = Session::new();
        let lines = run(&mut session, r"k = \x. y z");
        assert_eq!(lines, ["note: `k` has free variables: y, z"]);
    }

    #[test]
    fn parse_errors_point_at_the_problem() {
        let mut session = Session::new();
        let lines = run(&mut session, r"(λx. x");
        assert_eq!(
            lines,
            ["error: expected `)`, found end of input\n  (λx. x\n        ^"]
        );
    }

    #[test]
    fn divergence_stops_at_the_fuel_limit() {
        let mut session = Session::new();
        assert!(run(&mut session, ":fuel 1_000").is_empty());
        assert_eq!(run(&mut session, ":fuel"), ["1000 steps per evaluation"]);
        let lines = run(&mut session, r"(\x. x x) (\x. x x)");
        assert!(
            lines[0].starts_with("no normal form within 1000 steps ("),
            "{lines:?}"
        );
    }

    #[test]
    fn compare_reports_both_strategies() {
        let mut session = Session::new();
        let lines = run(&mut session, r":compare (\x. f x x) ((\y. y) a)");
        assert_eq!(lines[0], "f a a");
        assert!(lines[1].starts_with("optimal:      2 β-steps"), "{lines:?}");
        assert_eq!(lines[2], "normal order: 3 β-steps in 2 families");
    }

    #[test]
    fn trace_shows_each_beta_step() {
        let mut session = Session::new();
        let lines = run(&mut session, r":trace (\x. x) ((\y. y) a)");
        assert_eq!(lines[0], "  (λx. x) ((λy. y) a)");
        assert_eq!(lines[1], "β (λy. y) a");
        assert_eq!(lines[2], "β a");
        assert!(lines[3].starts_with("2 β-steps"), "{lines:?}");
    }

    #[test]
    fn dot_prints_a_graph() {
        let mut session = Session::new();
        let lines = run(&mut session, r":dot \x. x");
        assert!(lines[0].starts_with("graph net {"), "{lines:?}");
        assert!(lines[0].ends_with('}'), "{lines:?}");
    }

    #[test]
    fn large_results_are_summarized() {
        let mut session = Session::new();
        let lines = run(&mut session, "3 10");
        assert_eq!(lines[0], "<a term of 2003 nodes>");
        assert_eq!(lines[1], "church numeral 1000");
    }

    #[test]
    fn commands_can_quit_or_be_unknown() {
        let mut session = Session::new();
        assert!(session.execute(":quit").quit);
        assert!(!session.execute(":help").quit);
        assert_eq!(
            run(&mut session, ":frobnicate"),
            ["unknown command `:frobnicate`; try `:help`"]
        );
    }

    #[test]
    fn loading_reports_problems() {
        let mut session = Session::new();
        let lines = run(&mut session, ":load /nonexistent/levy.lam");
        assert!(lines[0].starts_with("error: cannot read"), "{lines:?}");
        assert_eq!(run(&mut session, ":load"), ["usage: :load FILE"]);
    }
}
