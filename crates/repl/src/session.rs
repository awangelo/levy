//! The state behind the prompt: definitions, settings and commands.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use levy_core::dot::to_dot;
use levy_core::parse::{MAX_NUMERAL, position};
use levy_core::reference::{self, GaveUp};
use levy_core::script::statements;
use levy_core::term::Nodes;
use levy_core::translate::translate;
use levy_core::{Definitions, Halt, Machine, ParseError, Rule, ScriptError, Statement, Term};

/// Work allowed per evaluation unless `:fuel` says otherwise, in steps of the
/// machine's walk: a few seconds for ordinary terms.
const DEFAULT_FUEL: u64 = 100_000_000;
/// Terms larger than this many nodes are summarized instead of printed.
const PRINT_LIMIT: usize = 2_000;
/// Beta-steps `:trace` prints before it stops.
const TRACE_LIMIT: u64 = 100;
/// Work allowed for reading back one term of a trace. A term that takes
/// more is too large to be worth printing.
const TRACE_READ_FUEL: u64 = 40_000;

/// Where the session writes.
pub trait Output {
    /// A line of results.
    fn line(&mut self, text: &str);

    /// A line about something that went wrong or deserves a remark.
    fn remark(&mut self, text: &str);

    /// Whether nobody reads the results any more, so that long work can be
    /// cut short.
    fn is_closed(&self) -> bool {
        false
    }
}

/// What became of one input.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Outcome {
    /// The input asks to leave.
    pub quit: bool,
    /// Something in the input could not be done.
    pub failed: bool,
}

impl Outcome {
    /// The outcome of an input that does not ask to leave.
    fn of<T>(result: Result<T, Failed>) -> Outcome {
        Outcome {
            quit: false,
            failed: result.is_err(),
        }
    }
}

/// Something could not be done, and the session has said what.
struct Failed;

/// Reports a problem.
fn fail<T>(out: &mut dyn Output, message: &str) -> Result<T, Failed> {
    out.remark(message);
    Err(Failed)
}

pub struct Session {
    definitions: Definitions,
    fuel: u64,
    /// Set from outside to stop the evaluation under way.
    interrupt: Arc<AtomicBool>,
}

/// Where a statement comes from: the file and the line it starts on.
#[derive(Clone, Copy)]
struct Origin<'a> {
    path: &'a str,
    line: usize,
}

impl Session {
    /// A session with no definitions. Setting `interrupt` stops the
    /// evaluation under way; the session never clears it.
    pub fn new(interrupt: Arc<AtomicBool>) -> Session {
        Session {
            definitions: Definitions::new(),
            fuel: DEFAULT_FUEL,
            interrupt,
        }
    }

    /// Runs one line of input: a command, a definition or a term.
    pub fn execute(&mut self, input: &str, out: &mut dyn Output) -> Outcome {
        let input = input.trim();
        let Some(command) = input.strip_prefix(':') else {
            return Outcome::of(self.statement(input, None, out));
        };
        let (name, argument) = command
            .split_once(char::is_whitespace)
            .unwrap_or((command, ""));
        if matches!(name, "q" | "quit" | "exit") {
            return Outcome {
                quit: true,
                failed: false,
            };
        }
        Outcome::of(self.command(name, argument.trim(), out))
    }

    /// Runs the statements of a file.
    pub fn load(&mut self, path: &str, out: &mut dyn Output) -> Outcome {
        Outcome::of(self.load_file(path, out))
    }

    fn interrupted(&self) -> bool {
        self.interrupt.load(Ordering::Relaxed)
    }

    /// Runs a command other than the one to quit.
    fn command(&mut self, name: &str, argument: &str, out: &mut dyn Output) -> Result<(), Failed> {
        match name {
            "h" | "help" | "?" => {
                out.line(&help());
                Ok(())
            }
            "defs" => {
                self.list_definitions(out);
                Ok(())
            }
            "fuel" => self.set_fuel(argument, out),
            "load" => self.load_file(argument, out),
            "compare" => self.compare(&self.term(argument, out)?, out),
            "trace" => self.trace(&self.term(argument, out)?, out),
            "dot" => self.dot(&self.term(argument, out)?, out),
            _ => fail(out, &format!("unknown command `:{name}`; try `:help`")),
        }
    }

    /// Parses the term a command is given.
    fn term(&self, source: &str, out: &mut dyn Output) -> Result<Term, Failed> {
        self.definitions
            .parse(source)
            .or_else(|error| fail(out, &describe(source, &error)))
    }

    /// Runs one statement, typed at the prompt or read from a file. Returns
    /// whether it was a definition.
    fn statement(
        &mut self,
        source: &str,
        origin: Option<Origin>,
        out: &mut dyn Output,
    ) -> Result<bool, Failed> {
        match self.definitions.statement(source) {
            Ok(None) => Ok(false),
            Ok(Some(Statement::Define(name, term))) => {
                let free = term.free_names();
                if !free.is_empty() {
                    let itself = if free.contains(&name.as_str()) {
                        "; a definition cannot refer to itself, \
                         recursion needs a fixed-point combinator"
                    } else {
                        ""
                    };
                    let place = origin
                        .map(|Origin { path, line }| format!("{path}:{line}: "))
                        .unwrap_or_default();
                    out.remark(&format!(
                        "{place}note: `{name}` has free variables: {}{itself}",
                        free.join(", ")
                    ));
                }
                self.definitions.define(name, term);
                Ok(true)
            }
            Ok(Some(Statement::Evaluate(term))) => self.evaluate(&term, out).map(|()| false),
            Err(error) => {
                // In a file, a problem is reported with the place it is at.
                let message = match origin {
                    Some(Origin { path, line }) => {
                        let ScriptError {
                            line,
                            column,
                            message,
                        } = ScriptError::new(line, source, error);
                        format!("{path}:{line}:{column}: error: {message}")
                    }
                    None => describe(source, &error),
                };
                fail(out, &message)
            }
        }
    }

    fn evaluate(&self, term: &Term, out: &mut dyn Output) -> Result<(), Failed> {
        let mut machine = self.machine(term, out)?;
        let started = Instant::now();
        let outcome = machine.normalize_unless(self.fuel, &|| self.interrupted());
        let elapsed = started.elapsed();
        match outcome {
            Ok(normal) => {
                result(&normal, out);
                out.line(&format!("{}, {elapsed:.1?}", steps(&machine)));
                Ok(())
            }
            Err(halt) => fail(out, &self.explain(halt, &machine)),
        }
    }

    fn compare(&self, term: &Term, out: &mut dyn Output) -> Result<(), Failed> {
        let mut machine = self.machine(term, out)?;
        let optimal = machine.normalize_unless(self.fuel, &|| self.interrupted());
        let reported = match &optimal {
            Ok(normal) => {
                result(normal, out);
                out.line(&format!("optimal:      {}", steps(&machine)));
                Ok(())
            }
            Err(halt) => {
                let message = format!("optimal:      {}", self.explain(*halt, &machine));
                fail(out, &message)
            }
        };
        if self.interrupted() {
            return reported;
        }
        match reference::normalize_unless(term, self.fuel, &|| self.interrupted()) {
            Ok(outcome) => {
                out.line(&format!(
                    "normal order: {} β-steps in {} families",
                    outcome.beta_steps, outcome.families
                ));
                if optimal.is_ok_and(|normal| normal != outcome.normal_form) {
                    return fail(out, "internal error: the two normal forms differ");
                }
                reported
            }
            Err(GaveUp::Interrupted) => fail(out, "normal order: interrupted"),
            Err(GaveUp::OutOfBudget) => {
                let message = format!("normal order: gave up after {} units of work", self.fuel);
                fail(out, &message)
            }
        }
    }

    fn trace(&self, term: &Term, out: &mut dyn Output) -> Result<(), Failed> {
        let mut machine = self.machine(term, out)?;
        out.line(&format!("  {}", show(term)));
        let mut shown = 0;
        // What stopped the reduction, if it was not its end.
        let halt = loop {
            if out.is_closed() {
                return Ok(());
            }
            // One interaction at a time, so that the fuel given bounds the
            // call, and all the calls together spend no more than the limit.
            let left = self.fuel.saturating_sub(machine.spent());
            match machine.advance_unless(1, false, left, &|| self.interrupted()) {
                Ok(None) => break None,
                Ok(Some(Rule::Beta)) => {
                    if shown == TRACE_LIMIT {
                        out.line(&format!("stopped after {TRACE_LIMIT} β-steps"));
                        return Ok(());
                    }
                    shown += 1;
                    match machine.readback_within(TRACE_READ_FUEL) {
                        Ok(Some(reduct)) => out.line(&format!("β {}", show(&reduct))),
                        Ok(None) => out.line("β <a term too large to show>"),
                        Err(halt) => break Some(halt),
                    }
                }
                Ok(Some(_)) => {}
                Err(halt) => break Some(halt),
            }
        };
        match halt {
            Some(halt) => fail(out, &self.explain(halt, &machine)),
            None => {
                out.line(&steps(&machine));
                Ok(())
            }
        }
    }

    fn load_file(&mut self, path: &str, out: &mut dyn Output) -> Result<(), Failed> {
        if path.is_empty() {
            return fail(out, "usage: :load FILE");
        }
        let script = std::fs::read_to_string(path)
            .or_else(|error| fail(out, &format!("error: cannot read `{path}`: {error}")))?;
        // Some editors put a byte-order mark in front, which is no part of
        // the first statement.
        let script = script.strip_prefix('\u{feff}').unwrap_or(&script);
        // The file goes on after a statement that fails: one slip should not
        // hide everything below it.
        let (mut definitions, mut failures) = (0, 0);
        for (line, source) in statements(script) {
            if out.is_closed() {
                break;
            }
            if self.interrupted() {
                let message = format!("{path}:{line}: interrupted, the rest is not loaded");
                return fail(out, &message);
            }
            let ran = match source.trim_start().strip_prefix(':') {
                Some(command) => {
                    let name = command.split_whitespace().next().unwrap_or_default();
                    let message = format!(
                        "{path}:{line}: error: `:{name}` is a command, for the prompt only"
                    );
                    fail(out, &message)
                }
                None => self.statement(source, Some(Origin { path, line }), out),
            };
            match ran {
                Ok(defined) => definitions += usize::from(defined),
                Err(Failed) => failures += 1,
            }
        }
        let plural = |count: usize| if count == 1 { "" } else { "s" };
        let mut summary = format!(
            "loaded `{path}`: {definitions} definition{}",
            plural(definitions)
        );
        if failures > 0 {
            summary += &format!(", {failures} statement{} failed", plural(failures));
        }
        out.line(&summary);
        if failures == 0 { Ok(()) } else { Err(Failed) }
    }

    fn list_definitions(&self, out: &mut dyn Output) {
        if self.definitions.is_empty() {
            out.line("no definitions yet");
        }
        for (name, term) in self.definitions.iter() {
            out.line(&format!("{name} = {}", show(term)));
        }
    }

    fn set_fuel(&mut self, argument: &str, out: &mut dyn Output) -> Result<(), Failed> {
        if argument.is_empty() {
            out.line(&format!("{} steps per evaluation", self.fuel));
            return Ok(());
        }
        match argument.replace('_', "").parse() {
            Ok(fuel) => {
                self.fuel = fuel;
                Ok(())
            }
            Err(_) => fail(out, &format!("error: `{argument}` is not a number")),
        }
    }

    /// Loads a term into a machine.
    fn machine(&self, term: &Term, out: &mut dyn Output) -> Result<Machine, Failed> {
        self.admit(term, out)?;
        Machine::new(term).or_else(|error| fail(out, &format!("error: {error}")))
    }

    fn dot(&self, term: &Term, out: &mut dyn Output) -> Result<(), Failed> {
        self.admit(term, out)?;
        let net = translate(term).or_else(|error| fail(out, &format!("error: {error}")))?;
        out.line(to_dot(&net).trim_end());
        Ok(())
    }

    /// Refuses a term whose net would have more nodes than the fuel allows
    /// steps. Definitions are expanded, so a line of a few words can stand
    /// for a term too large to build, and building it comes before any fuel
    /// is spent.
    fn admit(&self, term: &Term, out: &mut dyn Output) -> Result<(), Failed> {
        let size = term.size();
        if u64::try_from(size).is_ok_and(|size| size <= self.fuel) {
            return Ok(());
        }
        let message = format!(
            "error: the term has {} with its definitions expanded, \
             more than the limit of {} steps; raise it with `:fuel`",
            Nodes(size),
            self.fuel
        );
        fail(out, &message)
    }

    fn explain(&self, halt: Halt, machine: &Machine) -> String {
        let stats = machine.stats();
        let done = format!(
            "{} interactions, {} β-steps",
            stats.interactions(),
            stats.beta
        );
        match halt {
            Halt::OutOfFuel => format!(
                "no normal form within {} steps ({done}); raise the limit with `:fuel`",
                self.fuel
            ),
            Halt::Interrupted => format!("interrupted ({done})"),
            Halt::Malformed(reason) => format!("internal error: malformed net: {reason}"),
        }
    }
}

/// Writes a normal form, and the number it is if it is a Church numeral.
fn result(normal: &Term, out: &mut dyn Output) {
    out.line(&show(normal));
    if let Some(value) = normal.as_church() {
        out.line(&format!("church numeral {value}"));
    }
}

/// How many interactions a machine has fired, as the session counts them.
fn steps(machine: &Machine) -> String {
    let stats = machine.stats();
    format!(
        "{} β-steps, {} bookkeeping steps",
        stats.beta,
        stats.bookkeeping()
    )
}

fn help() -> String {
    format!(
        "\
Enter a term to reduce it to normal form, or `name = term` to define a name.

  \\x. body  or  λx. body    abstraction; `\\x y. body` binds several names
  f a b                      application, associating to the left
  3                          the Church numeral for 3, up to {MAX_NUMERAL}
  -- text                    comment

Commands:
  :compare TERM   reduce TERM both optimally and in normal order
  :trace TERM     show the term after each β-step, up to {TRACE_LIMIT} of them
  :dot TERM       print the net of TERM in Graphviz format
  :load FILE      run the statements of a file
  :defs           list the definitions
  :fuel [N]       show or set the limit on the work of one evaluation
  :help, :h       show this text
  :quit, :q       leave

Ctrl-C stops an evaluation and keeps the session. A term of more than
{PRINT_LIMIT} nodes is shown as its size. In a file, a statement runs on over
the indented lines that follow it."
    )
}

fn show(term: &Term) -> String {
    term.abbreviated(PRINT_LIMIT)
}

/// A parse error as a message, with a caret under the offending place when
/// the source fits on one line, and with the line and the column otherwise.
fn describe(source: &str, error: &ParseError) -> String {
    if source.contains('\n') {
        let (line, column) = position(source, error.offset);
        return format!("error: {} (line {line}, column {column})", error.message);
    }
    // Tabs are kept, so that the caret lines up however wide a tab is shown.
    let indent: String = source
        .char_indices()
        .take_while(|(offset, _)| *offset < error.offset)
        .map(|(_, c)| if c == '\t' { '\t' } else { ' ' })
        .collect();
    format!("error: {}\n  {source}\n  {indent}^", error.message)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Collects everything the session writes, remarks included, in order.
    #[derive(Default)]
    struct Transcript(Vec<String>);

    impl Output for Transcript {
        fn line(&mut self, text: &str) {
            self.0.push(text.to_owned());
        }

        fn remark(&mut self, text: &str) {
            self.0.push(text.to_owned());
        }
    }

    fn session() -> Session {
        Session::new(Arc::new(AtomicBool::new(false)))
    }

    fn run(session: &mut Session, input: &str) -> Vec<String> {
        let mut transcript = Transcript::default();
        session.execute(input, &mut transcript);
        transcript.0
    }

    fn failed(session: &mut Session, input: &str) -> bool {
        session.execute(input, &mut Transcript::default()).failed
    }

    /// A file in the temporary directory, removed when dropped.
    struct Script(std::path::PathBuf);

    impl Script {
        fn new(name: &str, text: &str) -> Script {
            let path = std::env::temp_dir().join(format!("levy-{}-{name}.lam", std::process::id()));
            std::fs::write(&path, text).unwrap();
            Script(path)
        }

        fn path(&self) -> &str {
            self.0.to_str().unwrap()
        }
    }

    impl Drop for Script {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }

    #[test]
    fn evaluates_terms() {
        let mut session = session();
        let lines = run(&mut session, r"(\x. x) y");
        assert_eq!(lines[0], "y");
        assert!(lines[1].starts_with("1 β-steps, "), "{lines:?}");
        assert!(!failed(&mut session, r"(\x. x) y"));
    }

    #[test]
    fn recognizes_church_numerals() {
        let mut session = session();
        let lines = run(&mut session, "2 2 2");
        assert_eq!(lines[1], "church numeral 16");
    }

    #[test]
    fn definitions_persist() {
        let mut session = session();
        assert!(run(&mut session, r"twice = \f x. f (f x)").is_empty());
        assert_eq!(run(&mut session, "twice twice")[1], "church numeral 4");
        assert_eq!(run(&mut session, ":defs"), ["twice = λf x. f (f x)"]);
    }

    #[test]
    fn free_variables_in_definitions_are_noted() {
        let mut session = session();
        let lines = run(&mut session, r"k = \x. y z");
        assert_eq!(lines, ["note: `k` has free variables: y, z"]);
        // A note is not a failure.
        assert!(!failed(&mut session, r"k = \x. y z"));
        let lines = run(&mut session, r"loop = \x. loop x");
        assert!(lines[0].contains("cannot refer to itself"), "{lines:?}");
    }

    #[test]
    fn parse_errors_point_at_the_problem() {
        let mut session = session();
        let lines = run(&mut session, r"(λx. x");
        assert_eq!(
            lines,
            ["error: expected `)`, found end of input\n  (λx. x\n        ^"]
        );
        assert!(failed(&mut session, r"(λx. x"));
        // The caret is indented by the tabs of the line above it.
        let lines = run(&mut session, "f\t\t)");
        assert!(lines[0].ends_with("\n  f\t\t)\n   \t\t^"), "{lines:?}");
    }

    #[test]
    fn divergence_stops_at_the_fuel_limit() {
        let mut session = session();
        assert!(run(&mut session, ":fuel 1_000").is_empty());
        assert_eq!(run(&mut session, ":fuel"), ["1000 steps per evaluation"]);
        let lines = run(&mut session, r"(\x. x x) (\x. x x)");
        assert!(
            lines[0].starts_with("no normal form within 1000 steps ("),
            "{lines:?}"
        );
        assert!(failed(&mut session, r"(\x. x x) (\x. x x)"));
        assert!(failed(&mut session, ":fuel much"));
    }

    #[test]
    fn an_interrupt_stops_the_evaluation_and_keeps_the_session() {
        let interrupt = Arc::new(AtomicBool::new(false));
        let mut session = Session::new(Arc::clone(&interrupt));
        assert!(run(&mut session, r"omega = (\x. x x) (\x. x x)").is_empty());
        interrupt.store(true, Ordering::Relaxed);
        for input in ["omega", ":compare omega", ":trace omega"] {
            let lines = run(&mut session, input);
            let last = lines.last().unwrap();
            assert!(last.contains("interrupted"), "{input}: {lines:?}");
            assert!(failed(&mut session, input), "{input}");
        }
        interrupt.store(false, Ordering::Relaxed);
        assert_eq!(run(&mut session, r"(\x. x) y")[0], "y");
        assert_eq!(run(&mut session, ":defs").len(), 1);
    }

    #[test]
    fn compare_reports_both_strategies() {
        let mut session = session();
        let lines = run(&mut session, r":compare (\x. f x x) ((\y. y) a)");
        assert_eq!(lines[0], "f a a");
        assert!(lines[1].starts_with("optimal:      2 β-steps"), "{lines:?}");
        assert_eq!(lines[2], "normal order: 3 β-steps in 2 families");
    }

    #[test]
    fn compare_survives_a_term_that_grows_for_ever() {
        // Normal order uncovers one more binder at every step.
        let mut session = session();
        assert!(run(&mut session, ":fuel 200_000").is_empty());
        let lines = run(&mut session, r":compare (\x y. x x) (\x y. x x)");
        assert!(
            lines[0].starts_with("optimal:      no normal form"),
            "{lines:?}"
        );
        assert!(lines[1].starts_with("normal order: gave up"), "{lines:?}");
    }

    #[test]
    fn trace_shows_each_beta_step() {
        let mut session = session();
        let lines = run(&mut session, r":trace (\x. x) ((\y. y) a)");
        assert_eq!(lines[0], "  (λx. x) ((λy. y) a)");
        assert_eq!(lines[1], "β (λy. y) a");
        assert_eq!(lines[2], "β a");
        assert!(lines[3].starts_with("2 β-steps"), "{lines:?}");
    }

    #[test]
    fn trace_finishes_when_its_fuel_is_just_enough() {
        // What evaluating the term spends, which is what tracing it spends
        // as well.
        let source = r"(\x. x) a";
        let mut machine = Machine::new(&levy_core::parse(source).unwrap()).unwrap();
        machine.normalize(u64::MAX).unwrap();
        let needed = machine.spent();
        let mut session = session();
        assert!(run(&mut session, &format!(":fuel {needed}")).is_empty());
        let lines = run(&mut session, &format!(":trace {source}"));
        assert_eq!(lines[1..], ["β a", "1 β-steps, 2 bookkeeping steps"]);
        // One unit less is not enough, and is not exceeded.
        let short = needed - 1;
        assert!(run(&mut session, &format!(":fuel {short}")).is_empty());
        let lines = run(&mut session, &format!(":trace {source}"));
        assert_eq!(lines[1], "β a");
        assert!(
            lines[2].starts_with(&format!("no normal form within {short} steps")),
            "{lines:?}"
        );
        assert!(failed(&mut session, &format!(":trace {source}")));
    }

    #[test]
    fn trace_needs_no_more_fuel_than_evaluation() {
        // Reading on past the pair a step stopped at is not paid twice.
        let mut session = session();
        assert!(run(&mut session, ":fuel 51").is_empty());
        let source = r"(\x. x x) (\x. x) ((\y. y) (\z. z)) w";
        assert_eq!(run(&mut session, source)[0], "w");
        let lines = run(&mut session, &format!(":trace {source}"));
        assert_eq!(lines[5], "β w", "{lines:?}");
        assert!(lines[6].starts_with("5 β-steps"), "{lines:?}");
        assert!(run(&mut session, ":fuel 50").is_empty());
        assert!(failed(&mut session, source));
        assert!(failed(&mut session, &format!(":trace {source}")));
    }

    #[test]
    fn trace_shows_no_more_than_a_hundred_beta_steps() {
        // A hundred beta-steps, the most a trace shows: two to apply the
        // numeral 98, and one per identity.
        let mut session = session();
        assert!(run(&mut session, ":fuel 1_000_000").is_empty());
        let lines = run(&mut session, r":trace 98 (\x. x) a");
        assert_eq!(lines[100], "β a");
        assert!(lines[101].starts_with("100 β-steps"), "{lines:?}");
        let lines = run(&mut session, r":trace 99 (\x. x) a");
        assert_eq!(lines[101], "stopped after 100 β-steps");
    }

    #[test]
    fn trace_stops_at_the_fuel_limit_when_the_result_is_too_large_to_read() {
        // Forty doublings: a net of a few hundred nodes for a term of 2^41.
        // The interactions are soon over, and the walk to the end of such a
        // term never is.
        let mut session = session();
        assert!(run(&mut session, ":fuel 300_000").is_empty());
        let lines = run(&mut session, r":trace 40 (\x. f x x) a");
        assert_eq!(lines.len(), 44, "{lines:?}");
        assert_eq!(lines[42], "β <a term too large to show>");
        assert!(
            lines[43]
                .starts_with("no normal form within 300000 steps (247 interactions, 42 β-steps)"),
            "{lines:?}"
        );
        // The same term evaluated stops at the same limit.
        assert_eq!(run(&mut session, r"40 (\x. f x x) a"), lines[43..]);
    }

    #[test]
    fn definitions_that_double_are_quick_to_make() {
        // Each uses the one before twice: 2^63 nodes as a tree, which only
        // looking at each shared term once can get through.
        let mut session = session();
        assert!(run(&mut session, r"d0 = \x. x").is_empty());
        for n in 1..=63 {
            let lines = run(&mut session, &format!("d{n} = d{} d{}", n - 1, n - 1));
            assert!(lines.is_empty(), "{lines:?}");
        }
        assert_eq!(run(&mut session, "d2")[0], "λx. x");
        // Listing them measures each shared term once.
        let lines = run(&mut session, ":defs");
        assert_eq!(lines[10], "d10 = <a term of 3071 nodes>");
        assert_eq!(lines[40], "d40 = <a term of 3298534883327 nodes>");
        assert_eq!(
            lines[63],
            format!("d63 = <a term of {} nodes or more>", usize::MAX)
        );
        // Nothing builds a net of trillions of nodes.
        for input in ["d40", ":compare d40", ":trace d40", ":dot d40"] {
            let lines = run(&mut session, input);
            assert_eq!(
                lines,
                [
                    "error: the term has 3298534883327 nodes with its definitions expanded, \
                     more than the limit of 100000000 steps; raise it with `:fuel`"
                ],
                "{input}"
            );
            assert!(failed(&mut session, input), "{input}");
        }
        assert!(run(&mut session, ":fuel 22").is_empty());
        assert!(failed(&mut session, "d3"));
        assert!(run(&mut session, ":fuel 23").is_empty());
        assert!(!failed(&mut session, ":dot d3"));
    }

    #[test]
    fn dot_prints_a_graph() {
        let mut session = session();
        let lines = run(&mut session, r":dot \x. x");
        assert!(lines[0].starts_with("graph net {"), "{lines:?}");
        assert!(lines[0].ends_with('}'), "{lines:?}");
    }

    #[test]
    fn large_results_are_summarized() {
        let mut session = session();
        let lines = run(&mut session, "3 10");
        assert_eq!(lines[0], "<a term of 2003 nodes>");
        assert_eq!(lines[1], "church numeral 1000");
    }

    #[test]
    fn deep_results_need_no_deep_stack() {
        // A numeral nested a quarter of a million deep, on the stack of a
        // test thread.
        let mut session = session();
        let lines = run(&mut session, "9 4");
        assert_eq!(lines[0], "<a term of 524291 nodes>");
        assert_eq!(lines[1], "church numeral 262144");
    }

    #[test]
    fn commands_can_quit_or_be_unknown() {
        let mut session = session();
        let mut transcript = Transcript::default();
        assert!(session.execute(":quit", &mut transcript).quit);
        assert!(!session.execute(":help", &mut transcript).quit);
        assert_eq!(
            run(&mut session, ":frobnicate"),
            ["unknown command `:frobnicate`; try `:help`"]
        );
        assert!(failed(&mut session, ":frobnicate"));
    }

    #[test]
    fn loading_reports_problems() {
        let mut session = session();
        let lines = run(&mut session, ":load /nonexistent/levy.lam");
        assert!(lines[0].starts_with("error: cannot read"), "{lines:?}");
        assert_eq!(run(&mut session, ":load"), ["usage: :load FILE"]);
        assert!(failed(&mut session, ":load"));
    }

    #[test]
    fn loading_goes_on_after_a_bad_statement_and_says_where_it_is() {
        let script = Script::new(
            "errors",
            "a = \\x. x\nb = \\x.\n  (x\nc = \\x. x x\n:fuel 3\na c\n",
        );
        let path = script.path();
        let mut session = session();
        let mut transcript = Transcript::default();
        let outcome = session.load(path, &mut transcript);
        let lines = transcript.0;
        assert!(outcome.failed);
        // The error is on the second line of the statement, past its end.
        assert_eq!(
            lines[0],
            format!("{path}:4:1: error: expected `)`, found end of input")
        );
        assert_eq!(
            lines[1],
            format!("{path}:5: error: `:fuel` is a command, for the prompt only")
        );
        assert_eq!(lines[2], "λx. x x");
        assert_eq!(
            lines[4],
            format!("loaded `{path}`: 2 definitions, 2 statements failed")
        );
        assert_eq!(run(&mut session, ":defs").len(), 2);
    }

    #[test]
    fn loading_notes_names_that_are_not_defined_yet() {
        let script = Script::new(
            "forward",
            "\u{feff}fact = \\n. n (\\x. fact x) 1\nuses = later 1\nlater = \\x. x\n",
        );
        let path = script.path();
        let mut session = session();
        let lines = run(&mut session, &format!(":load {path}"));
        assert!(
            lines[0].starts_with(&format!("{path}:1: note: `fact` has free variables: fact;")),
            "{lines:?}"
        );
        assert_eq!(
            lines[1],
            format!("{path}:2: note: `uses` has free variables: later")
        );
        assert_eq!(lines[2], format!("loaded `{path}`: 3 definitions"));
        // Notes are not failures.
        assert!(!failed(&mut session, &format!(":load {path}")));
    }

    #[test]
    fn the_prelude_loads_and_computes() {
        let prelude = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/prelude.lam");
        let mut session = session();
        let mut transcript = Transcript::default();
        let outcome = session.load(prelude, &mut transcript);
        assert_eq!(
            transcript.0,
            [format!("loaded `{prelude}`: 27 definitions")],
            "the prelude loads without a remark"
        );
        assert!(!outcome.failed);
        for (source, value) in [
            ("succ 0", 1),
            ("plus 3 4", 7),
            ("times 3 4", 12),
            ("power 2 10", 1024),
            ("power 3 0", 1),
            ("power 0 0", 1),
            ("pred 0", 0),
            ("pred 5", 4),
            ("minus 5 3", 2),
            ("minus 3 5", 0),
            ("fact 0", 1),
            ("fact 4", 24),
            ("fib 0", 0),
            ("fib 12", 144),
            ("compose succ succ 1", 3),
            ("const 2 3", 2),
            ("id 7", 7),
            ("fst (pair 1 2)", 1),
            ("snd (pair 1 2)", 2),
            ("iszero 0 1 2", 1),
            ("iszero 3 1 2", 2),
            ("not true 1 2", 2),
            ("and true false 1 2", 2),
            ("and true true 1 2", 1),
            ("or false true 1 2", 1),
            ("or false false 1 2", 2),
            ("leq 2 5 1 2", 1),
            ("leq 5 2 1 2", 2),
            ("leq 4 4 1 2", 1),
            ("eq 0 0 1 2", 1),
            ("eq 3 3 1 2", 1),
            ("eq 3 4 1 2", 2),
            ("eq 4 3 1 2", 2),
            ("geq 5 2 1 2", 1),
            ("geq 2 5 1 2", 2),
            ("geq 4 4 1 2", 1),
            ("lt 2 5 1 2", 1),
            ("lt 5 2 1 2", 2),
            ("lt 4 4 1 2", 2),
            ("gt 5 2 1 2", 1),
            ("gt 2 5 1 2", 2),
            ("gt 4 4 1 2", 2),
            ("neq 3 4 1 2", 1),
            ("neq 3 3 1 2", 2),
        ] {
            let lines = run(&mut session, source);
            assert_eq!(
                lines.get(1).map(String::as_str),
                Some(format!("church numeral {value}").as_str()),
                "{source}: {lines:?}"
            );
        }
    }
}
