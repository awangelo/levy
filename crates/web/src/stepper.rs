//! A reduction that can be stepped forwards and backwards, and what it looks
//! like at each point.

use levy_core::layout::layout;
use levy_core::net::{Kind, Net, NodeId};
use levy_core::script::statements;
use levy_core::{Definitions, Halt, Machine, Rule, Statement, Term};
use serde::Serialize;

/// Terms larger than this many nodes are summarized instead of printed.
const PRINT_LIMIT: usize = 600;
/// Past states kept for stepping back.
const HISTORY_LIMIT: usize = 5_000;

/// One node of the picture.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct NodeView {
    /// Stable across frames: the same node keeps the same identifier.
    pub id: u64,
    pub kind: &'static str,
    /// The name of an abstraction or of a free variable.
    pub label: String,
    /// The level of a fan or of a delimiter.
    pub level: Option<u32>,
    pub column: f32,
    pub row: u32,
}

/// One wire of the picture, between port `a_port` of node `a` and port
/// `b_port` of node `b`. Port 0 is the principal port.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WireView {
    pub a: u64,
    pub a_port: u8,
    pub b: u64,
    pub b_port: u8,
    /// Whether the wire belongs to the tree the layout follows.
    pub tree: bool,
}

/// The pair of nodes the next step rewrites.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NextView {
    pub upper: u64,
    pub lower: u64,
    pub rule: &'static str,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct StatsView {
    pub beta: u64,
    pub annihilations: u64,
    pub commutations: u64,
    pub dissolutions: u64,
    pub collected: u64,
}

/// Everything the page shows about one point of the reduction.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Frame {
    /// Interactions fired so far.
    pub step: u64,
    /// The term the net stands for.
    pub term: String,
    pub stats: StatsView,
    pub nodes: Vec<NodeView>,
    pub wires: Vec<WireView>,
    /// `None` once the net is in normal form.
    pub next: Option<NextView>,
    /// Whether stepping back is possible.
    pub can_go_back: bool,
    /// Set if the net stopped making sense, which would be a bug.
    pub error: Option<String>,
}

pub fn rule_name(rule: Rule) -> &'static str {
    match rule {
        Rule::Beta => "beta",
        Rule::Annihilate => "annihilate",
        Rule::Commute => "commute",
        Rule::Dissolve => "dissolve",
    }
}

/// A reduction with its past.
pub struct Stepper {
    /// The machine before any step, for starting over.
    initial: Machine,
    current: Machine,
    /// Earlier states, oldest first.
    history: Vec<Machine>,
}

impl Stepper {
    /// Loads a script: definitions, then the term to reduce. If the script
    /// holds several terms, the last one is reduced.
    pub fn load(script: &str) -> Result<Stepper, String> {
        let mut definitions = Definitions::new();
        let mut term: Option<Term> = None;
        for (line, source) in statements(script) {
            match definitions.statement(source) {
                Ok(None) => {}
                Ok(Some(Statement::Define(name, body))) => definitions.define(name, body),
                Ok(Some(Statement::Evaluate(body))) => term = Some(body),
                Err(error) => return Err(format!("line {line}: {}", error.message)),
            }
        }
        let term = term.ok_or("the script has no term to reduce")?;
        let machine = Machine::new(&term).map_err(|error| error.to_string())?;
        Ok(Stepper {
            initial: machine.clone(),
            current: machine,
            history: Vec::new(),
        })
    }

    /// Fires the next interaction and collects the garbage it leaves.
    /// Returns its rule, or `None` if the net is in normal form.
    pub fn step(&mut self) -> Result<Option<Rule>, Halt> {
        let before = self.current.clone();
        let fired = self.current.step()?;
        if fired.is_some() {
            self.current.collect();
            if self.history.len() == HISTORY_LIMIT {
                self.history.remove(0);
            }
            self.history.push(before);
        }
        Ok(fired)
    }

    /// Undoes the last step. Returns whether there was one to undo.
    pub fn back(&mut self) -> bool {
        match self.history.pop() {
            Some(previous) => {
                self.current = previous;
                true
            }
            None => false,
        }
    }

    /// Goes back to the term as it was loaded.
    pub fn reset(&mut self) {
        self.current = self.initial.clone();
        self.history.clear();
    }

    /// The current point of the reduction, ready to be drawn.
    pub fn frame(&self) -> Frame {
        let net = self.current.net();
        let stats = self.current.stats();
        let (term, read_error) = match self.current.readback() {
            Ok(term) => (term.abbreviated(PRINT_LIMIT), None),
            Err(halt) => (String::new(), Some(halt.to_string())),
        };
        let (next, next_error) = match self.current.next() {
            Ok(next) => (next, None),
            Err(halt) => (None, Some(halt.to_string())),
        };
        let diagram = layout(net);
        Frame {
            step: stats.interactions(),
            term,
            stats: StatsView {
                beta: stats.beta,
                annihilations: stats.annihilations,
                commutations: stats.commutations,
                dissolutions: stats.dissolutions,
                collected: stats.collected,
            },
            nodes: diagram
                .placements
                .iter()
                .map(|placement| node_view(net, placement.node, placement.column, placement.row))
                .collect(),
            wires: diagram
                .wires
                .iter()
                .map(|wire| {
                    let [a, b] = wire.ends;
                    WireView {
                        a: net.serial(a.node),
                        a_port: a.slot,
                        b: net.serial(b.node),
                        b_port: b.slot,
                        tree: wire.in_tree,
                    }
                })
                .collect(),
            next: next.map(|redex| NextView {
                upper: net.serial(redex.upper),
                lower: net.serial(redex.lower),
                rule: rule_name(redex.rule),
            }),
            can_go_back: !self.history.is_empty(),
            error: read_error.or(next_error),
        }
    }
}

fn node_view(net: &Net, node: NodeId, column: f32, row: u32) -> NodeView {
    let (kind, label, level) = match net.kind(node) {
        Kind::Root => ("root", "", None),
        Kind::Lam { name } => ("lam", net.name(name), None),
        Kind::App => ("app", "", None),
        Kind::Fan { level } => ("fan", "", Some(level)),
        Kind::Delim { level } => ("delim", "", Some(level)),
        Kind::Eraser => ("eraser", "", None),
        Kind::Free { name } => ("free", net.name(name), None),
    };
    NodeView {
        id: net.serial(node),
        kind,
        label: label.to_owned(),
        level,
        column,
        row,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SCRIPT: &str = "-- two applied to itself\ntwo = \\f x. f (f x)\ntwo two\n";

    fn run_to_end(stepper: &mut Stepper) -> u64 {
        let mut steps = 0;
        while stepper.step().unwrap().is_some() {
            steps += 1;
        }
        steps
    }

    #[test]
    fn loads_definitions_and_the_last_term() {
        let stepper = Stepper::load(SCRIPT).unwrap();
        let frame = stepper.frame();
        assert_eq!(frame.term, "(λf x. f (f x)) (λf x. f (f x))");
        assert_eq!(frame.step, 0);
        assert!(!frame.can_go_back);
        assert_eq!(frame.next.map(|next| next.rule), Some("beta"));
        assert_eq!(frame.error, None);
    }

    #[test]
    fn reports_script_errors_with_their_line() {
        assert_eq!(
            Stepper::load("id = \\x. x\nid (").err(),
            Some("line 2: expected a term, found end of input".to_owned())
        );
        assert_eq!(
            Stepper::load("id = \\x. x\n").err(),
            Some("the script has no term to reduce".to_owned())
        );
    }

    #[test]
    fn steps_to_the_normal_form() {
        let mut stepper = Stepper::load(SCRIPT).unwrap();
        let steps = run_to_end(&mut stepper);
        let frame = stepper.frame();
        assert_eq!(frame.term, "λx x1. x (x (x (x x1)))");
        assert_eq!(frame.step, steps);
        assert_eq!(frame.next, None);
        assert!(frame.can_go_back);
    }

    #[test]
    fn stepping_back_restores_the_frame() {
        let mut stepper = Stepper::load(SCRIPT).unwrap();
        let start = stepper.frame();
        stepper.step().unwrap();
        let after_one = stepper.frame();
        stepper.step().unwrap();
        assert!(stepper.back());
        assert_eq!(stepper.frame(), after_one);
        assert!(stepper.back());
        assert_eq!(stepper.frame(), start);
        assert!(!stepper.back());
    }

    #[test]
    fn reset_returns_to_the_start() {
        let mut stepper = Stepper::load(SCRIPT).unwrap();
        let start = stepper.frame();
        run_to_end(&mut stepper);
        stepper.reset();
        assert_eq!(stepper.frame(), start);
    }

    #[test]
    fn frames_are_consistent_pictures() {
        let mut stepper = Stepper::load(SCRIPT).unwrap();
        loop {
            let frame = stepper.frame();
            let ids: Vec<u64> = frame.nodes.iter().map(|node| node.id).collect();
            for wire in &frame.wires {
                assert!(ids.contains(&wire.a) && ids.contains(&wire.b));
            }
            if let Some(next) = &frame.next {
                assert!(ids.contains(&next.upper) && ids.contains(&next.lower));
            }
            // Garbage is collected after every step, so only the term is left.
            let roots = frame.nodes.iter().filter(|node| node.row == 0).count();
            assert_eq!(roots, 1, "step {}", frame.step);
            if stepper.step().unwrap().is_none() {
                break;
            }
        }
    }

    #[test]
    fn frames_serialize_to_json() {
        let stepper = Stepper::load("\\x. x").unwrap();
        let json = serde_json::to_string(&stepper.frame()).unwrap();
        assert!(json.contains(r#""kind":"lam""#), "{json}");
        assert!(json.contains(r#""next":null"#), "{json}");
    }
}
