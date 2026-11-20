//! A reduction that can be stepped forwards and backwards, and what it looks
//! like at each point.

use std::collections::VecDeque;

use levy_core::net::{Kind, Net, NodeId};
use levy_core::term::Nodes;
use levy_core::{Definitions, Halt, Machine, Rule};
use serde::Serialize;

use crate::layout::{Diagram, layout};

/// Terms larger than this many nodes are summarized instead of printed.
const PRINT_LIMIT: usize = 600;
/// Work allowed for reading back the term of one frame. A net of a few
/// nodes can stand for a term of millions, which nobody would read.
const READ_FUEL: u64 = 10_000;
/// What the frame says in place of a term that takes more than that.
const TOO_LARGE: &str = "<a term too large to show>";
/// Work allowed for one interaction and the walk from it to the next, or to
/// the end of the term if there is none. Past the last interaction that is
/// the whole term, which is too much to walk if the term is too large.
const SEARCH_FUEL: u64 = 1_000_000;
/// The most nodes a term may have, its definitions expanded, for the page to
/// load it. Definitions are expanded, so a script of a few lines can stand
/// for a term too large to build, and building it comes before any fuel is
/// spent.
const LARGEST_TERM: usize = 1_000_000;
/// How many operations lie between two of the states kept for stepping back.
const OPERATIONS_PER_SNAPSHOT: usize = 32;
/// How many places for nodes the kept states may hold between them, the
/// contexts of their walks counted in the same unit. At some 60 bytes a
/// place this is around 100 MB.
const SNAPSHOT_SLOTS: usize = 2_000_000;
/// How many interactions before the state gone back to another state is
/// kept, if none is nearer, so that going further back stays cheap.
const NEARBY: u64 = 64;
/// Identifiers of erasers start here, above the serial of any other node
/// and still within what JavaScript counts exactly.
const ERASER_IDS: u64 = 1 << 50;

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
    /// How many delimiters of that level the node stands for.
    pub height: Option<u32>,
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
    /// How many nodes the net has, drawn or not.
    pub size: usize,
    /// The picture. Empty if the net has more nodes than were asked for.
    pub nodes: Vec<NodeView>,
    pub wires: Vec<WireView>,
    /// `None` if the net is in normal form, and also if its next
    /// interaction is out of reach: `normal` tells which.
    pub next: Option<NextView>,
    /// Whether the net is in normal form. With neither this nor `next`, the
    /// stepper stops: it has looked as far as it looks for an interaction,
    /// or for the end of the term, and has found neither.
    pub normal: bool,
    /// Whether stepping back is possible.
    pub can_go_back: bool,
    /// Set if the net stopped making sense, which would be a bug.
    pub error: Option<String>,
}

/// A reduction with its past.
///
/// Going back does not need a copy of the machine per step. Reduction is
/// deterministic, so it is enough to keep a state now and then, and the
/// sizes of the operations done since: an earlier state is the one kept
/// before it with those operations done again.
pub struct Stepper {
    /// The machine before any step, for starting over.
    initial: Machine,
    current: Machine,
    /// States the reduction went through, oldest first. Stepping back ends
    /// at the first.
    snapshots: VecDeque<Machine>,
    /// For each snapshot but the last, the operations that lead from it to
    /// the next.
    stretches: VecDeque<Vec<u64>>,
    /// The operations that lead from the last snapshot to the current state,
    /// each as the number of interactions it fired.
    since: Vec<u64>,
    /// How many places for nodes the snapshots may hold between them, as
    /// [`Machine::slots`] counts them.
    snapshot_slots: usize,
    /// What a step found wrong with the net, if one did. The machine cannot
    /// go on from there, so nothing fires until the reduction goes back.
    failure: Option<Halt>,
}

/// The definitions every script starts with: those of the REPL's prelude,
/// built into the package because the page cannot read files beside it.
const PRELUDE: &str = include_str!("../../../examples/prelude.lam");

/// The definitions of [`PRELUDE`].
fn prelude() -> Definitions {
    let mut definitions = Definitions::new();
    // A test makes sure that the prelude loads, and that it only defines.
    let _ = definitions.load(PRELUDE);
    definitions
}

impl Stepper {
    /// Loads a script: definitions, then the term to reduce. If the script
    /// holds several terms, the last one is reduced. The definitions of the
    /// prelude come first, so the script can use them or define them anew.
    pub fn load(script: &str) -> Result<Stepper, String> {
        let terms = prelude().load(script).map_err(|error| error.to_string())?;
        let term = terms.last().ok_or("the script has no term to reduce")?;
        let size = term.size();
        if size > LARGEST_TERM {
            return Err(format!(
                "the term has {} with its definitions expanded, \
                 more than the {LARGEST_TERM} the page takes",
                Nodes(size)
            ));
        }
        let mut machine = Machine::new(term).map_err(|error| error.to_string())?;
        // Every state the stepper keeps stands in front of the pair it
        // rewrites next, and so must the first. If that pair is out of
        // reach, there is nothing to step through.
        match machine.advance(0, false, SEARCH_FUEL) {
            Ok(_) | Err(Halt::OutOfFuel) => {}
            Err(halt) => return Err(halt.to_string()),
        }
        Ok(Stepper {
            snapshots: VecDeque::from([machine.clone()]),
            initial: machine.clone(),
            current: machine,
            stretches: VecDeque::new(),
            since: Vec::new(),
            snapshot_slots: SNAPSHOT_SLOTS,
            failure: None,
        })
    }

    /// Interactions fired so far.
    pub fn steps(&self) -> u64 {
        self.current.stats().interactions()
    }

    /// Fires the next interaction and collects the garbage it leaves.
    /// Returns its rule, or `None` if none fired: see
    /// [`advance`](Stepper::advance).
    pub fn step(&mut self) -> Result<Option<Rule>, Halt> {
        self.advance(1, false)
    }

    /// Fires up to `interactions` interactions as one operation, stopping
    /// after the first beta among them if `until_beta`, and collects the
    /// garbage they leave. Returns the rule fired last, or `None` if none
    /// fired: the net is in normal form, or its next interaction is out of
    /// reach. Once the net is found malformed, says so again on every call
    /// until the reduction goes back.
    pub fn advance(&mut self, interactions: u64, until_beta: bool) -> Result<Option<Rule>, Halt> {
        if let Some(halt) = self.failure {
            return Err(halt);
        }
        let before = self.steps();
        let outcome = run(&mut self.current, interactions, until_beta);
        let fired = self.steps() - before;
        if fired > 0 {
            self.current.collect();
            self.since.push(fired);
            if self.since.len() >= OPERATIONS_PER_SNAPSHOT {
                self.snapshot();
            }
        }
        if let Err(halt) = outcome {
            self.failure = Some(halt);
        }
        outcome
    }

    /// Keeps the current state, and forgets the oldest ones if all of them
    /// together have grown too large.
    fn snapshot(&mut self) {
        let stretch = std::mem::take(&mut self.since);
        self.keep(self.current.clone(), stretch);
    }

    /// Keeps `state`, which `stretch` leads to from the last state kept.
    fn keep(&mut self, state: Machine, stretch: Vec<u64>) {
        self.snapshots.push_back(state);
        self.stretches.push_back(stretch);
        let mut slots: usize = self.snapshots.iter().map(|machine| machine.slots()).sum();
        while slots > self.snapshot_slots && self.snapshots.len() > 1 {
            if let Some(oldest) = self.snapshots.pop_front() {
                slots -= oldest.slots();
            }
            self.stretches.pop_front();
        }
    }

    /// Whether there is an interaction to undo.
    pub fn can_go_back(&self) -> bool {
        !(self.since.is_empty() && self.stretches.is_empty())
    }

    /// Undoes the last interaction. Returns whether there was one to undo.
    pub fn back(&mut self) -> bool {
        if self.since.is_empty() {
            // The current state is the last one kept: go back into the
            // stretch that led to it.
            let Some(stretch) = self.stretches.pop_back() else {
                return false;
            };
            self.snapshots.pop_back();
            self.since = stretch;
        }
        // Undoing an interaction of an operation that fired several leaves
        // an operation that fires one less.
        match self.since.pop() {
            Some(last) if last > 1 => self.since.push(last - 1),
            _ => {}
        }
        let mut machine = self
            .snapshots
            .back()
            .expect("the oldest state is never forgotten")
            .clone();
        // After a long run the last state kept can be thousands of
        // interactions back. Doing them all again for every step backwards
        // would be slow, so a state close to the target is kept on the way.
        let total: u64 = self.since.iter().sum();
        if total > 2 * NEARBY {
            let (far, near) = split(&self.since, total - NEARBY);
            replay(&mut machine, &far);
            self.keep(machine.clone(), far);
            self.since = near;
        }
        replay(&mut machine, &self.since);
        self.current = machine;
        self.failure = None;
        true
    }

    /// Goes back to the term as it was loaded.
    pub fn reset(&mut self) {
        self.current = self.initial.clone();
        self.snapshots = VecDeque::from([self.initial.clone()]);
        self.stretches.clear();
        self.since.clear();
        self.failure = None;
    }

    /// The current point of the reduction, ready to be drawn. The picture is
    /// left out if the net has more than `max_nodes` nodes.
    pub fn frame(&self, max_nodes: usize) -> Frame {
        let net = self.current.net();
        let stats = self.current.stats();
        let (term, error) = match self.current.readback_within(READ_FUEL) {
            Ok(Some(term)) => (term.abbreviated(PRINT_LIMIT), None),
            Ok(None) => (TOO_LARGE.to_owned(), None),
            Err(halt) => (String::new(), Some(halt.to_string())),
        };
        let diagram = if net.len() <= max_nodes {
            layout(net)
        } else {
            Diagram::default()
        };
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
            size: net.len(),
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
                        a: id(net, a.node),
                        a_port: a.slot,
                        b: id(net, b.node),
                        b_port: b.slot,
                        tree: wire.in_tree,
                    }
                })
                .collect(),
            next: self.current.next().map(|redex| NextView {
                upper: id(net, redex.upper),
                lower: id(net, redex.lower),
                rule: redex.rule.name(),
            }),
            normal: self.current.is_normal(),
            can_go_back: self.can_go_back(),
            error: self.failure.map(|halt| halt.to_string()).or(error),
        }
    }
}

/// Fires up to `interactions` interactions of `machine`, stopping after the
/// first beta among them if `until_beta`. Returns the rule fired last, if
/// any fired.
///
/// Each interaction has `SEARCH_FUEL` of its own. Where the machine stands
/// after an interaction then depends on that interaction alone, not on how
/// many were asked for at once, so going back can do them again in batches
/// of any size.
fn run(machine: &mut Machine, interactions: u64, until_beta: bool) -> Result<Option<Rule>, Halt> {
    // With no pair in front there is nothing to fire: the net is in normal
    // form, or the pair that comes next is out of reach. Looking further
    // would move the machine without a step to go back over.
    if machine.next().is_none() {
        return Ok(None);
    }
    machine.advance(interactions, until_beta, SEARCH_FUEL)
}

/// Does again the operations of `stretch`, each with the collection that
/// followed it.
fn replay(machine: &mut Machine, stretch: &[u64]) {
    for &fired in stretch {
        // What worked once works again, the machine being the same.
        if run(machine, fired, false).is_err() {
            break;
        }
        machine.collect();
    }
}

/// Cuts a stretch in two after `interactions` interactions, splitting the
/// operation the cut falls in.
fn split(stretch: &[u64], interactions: u64) -> (Vec<u64>, Vec<u64>) {
    let (mut before, mut after) = (Vec::new(), Vec::new());
    let mut left = interactions;
    for &fired in stretch {
        let taken = fired.min(left);
        left -= taken;
        if taken > 0 {
            before.push(taken);
        }
        if fired > taken {
            after.push(fired - taken);
        }
    }
    (before, after)
}

/// The identifier of a node in the picture, the same in every frame the
/// node is in.
///
/// For most nodes that is their serial. An eraser is named after the port
/// it plugs instead: when exactly garbage is removed, and erasers are put
/// where it was, depends on how the reduction is driven, and the picture
/// should not.
fn id(net: &Net, node: NodeId) -> u64 {
    match (net.kind(node), net.wire(node.principal())) {
        (Kind::Eraser, Some(plugged)) => {
            ERASER_IDS + net.serial(plugged.node) * 4 + u64::from(plugged.slot)
        }
        _ => net.serial(node),
    }
}

fn node_view(net: &Net, node: NodeId, column: f32, row: u32) -> NodeView {
    let (kind, label, level, height) = match net.kind(node) {
        Kind::Root => ("root", "", None, None),
        Kind::Lam { name } => ("lam", net.name(name), None, None),
        Kind::App => ("app", "", None, None),
        Kind::Fan { level } => ("fan", "", Some(level), None),
        Kind::Delim { level, count } => ("delim", "", Some(level), Some(count)),
        Kind::Eraser => ("eraser", "", None, None),
        Kind::Free { name } => ("free", net.name(name), None, None),
    };
    NodeView {
        id: id(net, node),
        kind,
        label: label.to_owned(),
        level,
        height,
        column,
        row,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SCRIPT: &str = "-- two applied to itself\ntwo = \\f x. f (f x)\ntwo two\n";
    /// Two to the fourth, applied to two identities: a few hundred steps.
    const EXPONENT: &str = "2 2 2 (\\x. x) (\\x. x)";
    /// More nodes than any net of these tests has.
    const ALL: usize = usize::MAX;

    fn run_to_end(stepper: &mut Stepper) -> u64 {
        let mut steps = 0;
        while stepper.step().unwrap().is_some() {
            steps += 1;
        }
        steps
    }

    #[test]
    fn the_prelude_is_built_in() {
        // It loads, and holds no term to evaluate.
        assert_eq!(Definitions::new().load(PRELUDE), Ok(Vec::new()));
        assert!(prelude().get("fact").is_some());
        // A script can use the prelude without defining anything...
        let mut stepper = Stepper::load("eq (fact 3) (plus 2 4) yes no").unwrap();
        run_to_end(&mut stepper);
        assert_eq!(stepper.frame(ALL).term, "yes");
        // ...and replace a definition of it.
        let mut stepper = Stepper::load("id = \\x. x x\nid y").unwrap();
        run_to_end(&mut stepper);
        assert_eq!(stepper.frame(ALL).term, "y y");
    }

    #[test]
    fn loads_definitions_and_the_last_term() {
        let stepper = Stepper::load(SCRIPT).unwrap();
        let frame = stepper.frame(ALL);
        assert_eq!(frame.term, "(λf x. f (f x)) (λf x. f (f x))");
        assert_eq!(frame.step, 0);
        assert!(!frame.can_go_back);
        assert_eq!(frame.next.map(|next| next.rule), Some("beta"));
        assert!(!frame.normal);
        assert_eq!(frame.error, None);
    }

    #[test]
    fn reports_script_errors_with_their_place() {
        assert_eq!(
            Stepper::load("id = \\x. x\nid (").err(),
            Some("line 2, column 5: expected a term, found end of input".to_owned())
        );
        assert_eq!(
            Stepper::load("id = \\x. x\ntwo = \\f x.\n  f (f x))\ntwo").err(),
            Some("line 3, column 10: unexpected `)`".to_owned())
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
        let frame = stepper.frame(ALL);
        assert_eq!(frame.term, "λx x1. x (x (x (x x1)))");
        assert_eq!(frame.step, steps);
        assert_eq!(frame.next, None);
        assert!(frame.normal);
        assert!(frame.can_go_back);
    }

    #[test]
    fn stepping_back_restores_the_frame() {
        let mut stepper = Stepper::load(SCRIPT).unwrap();
        let start = stepper.frame(ALL);
        stepper.step().unwrap();
        let after_one = stepper.frame(ALL);
        stepper.step().unwrap();
        assert!(stepper.back());
        assert_eq!(stepper.frame(ALL), after_one);
        assert!(stepper.back());
        assert_eq!(stepper.frame(ALL), start);
        assert!(!stepper.back());
    }

    #[test]
    fn stepping_back_restores_every_frame_of_a_long_run() {
        // Long enough to go through several snapshots.
        let mut stepper = Stepper::load(EXPONENT).unwrap();
        let mut frames = vec![stepper.frame(ALL)];
        while stepper.step().unwrap().is_some() {
            frames.push(stepper.frame(ALL));
        }
        assert!(stepper.snapshots.len() > 5, "{}", stepper.snapshots.len());
        while let Some(frame) = frames.pop() {
            assert_eq!(stepper.frame(ALL), frame, "step {}", frame.step);
            assert_eq!(stepper.back(), !frames.is_empty());
        }
        // Forwards again gives the same frames as the first time.
        stepper.step().unwrap();
        stepper.step().unwrap();
        assert!(stepper.back());
        assert_eq!(stepper.frame(ALL).step, 1);
    }

    #[test]
    fn a_batch_can_be_undone_one_interaction_at_a_time() {
        let script = EXPONENT;
        let mut stepper = Stepper::load(script).unwrap();
        assert_eq!(
            stepper.advance(10, false).unwrap(),
            stepper_rule_at(script, 10)
        );
        assert_eq!(stepper.steps(), 10);
        // To the end in batches that stop at each beta.
        let mut betas = stepper.frame(ALL).stats.beta;
        while let Some(rule) = stepper.advance(u64::MAX, true).unwrap() {
            betas += u64::from(rule == Rule::Beta);
        }
        let end = stepper.frame(ALL);
        assert_eq!(end.next, None);
        assert_eq!(end.stats.beta, betas);
        let mut stepped = Stepper::load(script).unwrap();
        let total = run_to_end(&mut stepped);
        assert_eq!(end.step, total);
        assert_eq!(end.term, stepped.frame(ALL).term);
        // Going back into a batch keeps the picture: the nodes that are in
        // both frames have the same identifiers in both.
        let ids = |frame: &Frame| -> Vec<u64> { frame.nodes.iter().map(|node| node.id).collect() };
        assert!(stepper.back());
        let before = stepper.frame(ALL);
        let common = ids(&before)
            .iter()
            .filter(|id| ids(&end).contains(id))
            .count();
        assert!(
            common * 2 > end.nodes.len(),
            "{common} of {}",
            end.nodes.len()
        );
        assert!(stepper.step().unwrap().is_some());
        assert_eq!(ids(&stepper.frame(ALL)), ids(&end));
        // Back through the batches, one interaction at a time.
        for step in (0..total).rev() {
            assert!(stepper.back(), "step {step}");
            assert_eq!(stepper.steps(), step);
            if step % 64 == 0 {
                assert_eq!(stepper.frame(ALL).error, None, "step {step}");
            }
        }
        assert!(!stepper.back());
        let start = Stepper::load(script).unwrap().frame(ALL);
        assert_eq!(stepper.frame(ALL).term, start.term);
    }

    /// The rule a single-stepped reduction of `script` fires as its
    /// `count`th interaction.
    fn stepper_rule_at(script: &str, count: u64) -> Option<Rule> {
        let mut stepper = Stepper::load(script).unwrap();
        let mut rule = None;
        for _ in 0..count {
            rule = stepper.step().unwrap();
        }
        rule
    }

    #[test]
    fn old_states_are_forgotten_before_they_take_too_much_room() {
        let mut stepper = Stepper::load(EXPONENT).unwrap();
        stepper.snapshot_slots = 300;
        let total = run_to_end(&mut stepper);
        let slots: usize = stepper
            .snapshots
            .iter()
            .map(|machine| machine.slots())
            .sum();
        assert!(slots <= 300, "{slots}");
        // What is left of the past can still be gone back through, down to
        // the oldest state kept.
        let mut undone = 0;
        while stepper.back() {
            undone += 1;
            assert_eq!(stepper.steps(), total - undone);
        }
        assert!(undone > 0 && undone < total, "{undone} of {total}");
        assert!(!stepper.frame(ALL).can_go_back);
        // Starting over is always possible.
        stepper.reset();
        assert_eq!(stepper.steps(), 0);
    }

    #[test]
    fn reset_returns_to_the_start() {
        let mut stepper = Stepper::load(SCRIPT).unwrap();
        let start = stepper.frame(ALL);
        run_to_end(&mut stepper);
        stepper.reset();
        assert_eq!(stepper.frame(ALL), start);
        assert!(!stepper.back());
    }

    #[test]
    fn frames_are_consistent_pictures() {
        for script in [
            SCRIPT.to_owned(),
            "fact 2".to_owned(),
            "2 2 2 (\\x. x) (\\x. x)".to_owned(),
            "\\x. (\\f. f f) (\\g. x (\\y. g y))".to_owned(),
        ] {
            let mut stepper = Stepper::load(&script).unwrap();
            loop {
                let frame = stepper.frame(ALL);
                let ids: Vec<u64> = frame.nodes.iter().map(|node| node.id).collect();
                assert_eq!(frame.size, ids.len());
                for wire in &frame.wires {
                    assert!(ids.contains(&wire.a) && ids.contains(&wire.b));
                }
                if let Some(next) = &frame.next {
                    assert!(ids.contains(&next.upper) && ids.contains(&next.lower));
                }
                // Garbage is collected after every step, so only the term is
                // left: one tree, hanging from the root.
                let top: Vec<&str> = frame
                    .nodes
                    .iter()
                    .filter(|node| node.row == 0 && node.kind != "eraser")
                    .map(|node| node.kind)
                    .collect();
                assert_eq!(top, ["root"], "step {}", frame.step);
                // No two nodes are drawn on the same spot.
                let mut spots: Vec<(u32, u32)> = frame
                    .nodes
                    .iter()
                    .map(|node| (node.column.to_bits(), node.row))
                    .collect();
                spots.sort_unstable();
                spots.dedup();
                assert_eq!(spots.len(), ids.len(), "step {}", frame.step);
                if stepper.step().unwrap().is_none() {
                    break;
                }
            }
        }
    }

    #[test]
    fn large_nets_and_large_terms_are_left_out_of_the_frame() {
        // Two to the sixteenth: the net stays small while the term it stands
        // for grows to a hundred thousand nodes.
        let mut stepper = Stepper::load("2 2 2 2").unwrap();
        let mut too_large = 0;
        while stepper.advance(200, false).unwrap().is_some() {
            too_large += usize::from(stepper.frame(ALL).term == TOO_LARGE);
        }
        assert!(too_large > 0);
        let frame = stepper.frame(10);
        assert!(frame.size > 10);
        assert!(frame.nodes.is_empty() && frame.wires.is_empty());
        // A result of 131,075 nodes is within reach: it was read to its end.
        assert_eq!(frame.next, None);
        assert!(frame.normal);
    }

    #[test]
    fn a_result_too_large_to_read_stops_the_stepper() {
        // Forty doublings: a net of a few hundred nodes for a term of 2^41.
        // After the last interaction only reading all of it would tell that
        // it was the last.
        let mut stepper = Stepper::load("40 (\\x. f x x) a").unwrap();
        while stepper.advance(1 << 20, false).unwrap().is_some() {}
        let end = stepper.frame(ALL);
        assert_eq!((end.next.as_ref(), end.normal), (None, false));
        assert_eq!(end.stats.beta, 42);
        assert_eq!(end.term, TOO_LARGE);
        assert_eq!(end.error, None);
        // Nothing more fires, and asking again changes nothing.
        assert_eq!(stepper.step(), Ok(None));
        assert_eq!(stepper.advance(u64::MAX, true), Ok(None));
        assert_eq!(stepper.frame(ALL), end);
        // The way back is open, and leads here again.
        assert!(stepper.back());
        let before = stepper.frame(ALL);
        assert_eq!(before.step, end.step - 1);
        assert!(before.next.is_some());
        assert!(stepper.step().unwrap().is_some());
        assert_eq!(stepper.frame(ALL), end);
    }

    #[test]
    fn a_malformed_net_stops_the_stepper_until_it_goes_back() {
        // No rule makes a malformed net, so the halt is put in by hand.
        let mut stepper = Stepper::load(SCRIPT).unwrap();
        stepper.step().unwrap();
        let before = stepper.frame(ALL);
        stepper.failure = Some(Halt::Malformed("a test"));
        let broken = Some("malformed net: a test".to_owned());
        assert_eq!(stepper.frame(ALL).error, broken);
        for _ in 0..2 {
            assert_eq!(stepper.step(), Err(Halt::Malformed("a test")));
            assert_eq!(stepper.frame(ALL).error, broken);
        }
        assert!(stepper.back());
        assert_eq!(stepper.frame(ALL).error, None);
        assert!(stepper.step().unwrap().is_some());
        assert_eq!(stepper.frame(ALL), before);
        stepper.failure = Some(Halt::Malformed("a test"));
        stepper.reset();
        assert_eq!(stepper.frame(ALL).error, None);
    }

    #[test]
    fn a_term_too_large_to_build_is_refused() {
        // Each definition uses the one before twice: 3 × 2^n - 1 nodes.
        let mut script = "d0 = \\x. x\n".to_owned();
        for n in 1..=40 {
            script += &format!("d{n} = d{} d{}\n", n - 1, n - 1);
        }
        assert!(Stepper::load(&format!("{script}d18")).is_ok());
        assert_eq!(
            Stepper::load(&format!("{script}d19")).err(),
            Some(
                "the term has 1572863 nodes with its definitions expanded, \
                 more than the 1000000 the page takes"
                    .to_owned()
            )
        );
        assert!(Stepper::load(&format!("{script}d40")).is_err());
    }

    #[test]
    fn the_counters_do_not_depend_on_how_a_step_was_reached() {
        // Many nodes are discarded on the way, so when garbage is collected
        // differs a lot between one step at a time and one run to the end.
        let script = "fact 3";
        let mut stepped = Stepper::load(script).unwrap();
        let mut stats = vec![stepped.frame(ALL).stats];
        while stepped.step().unwrap().is_some() {
            stats.push(stepped.frame(ALL).stats);
        }
        assert!(stats.last().unwrap().collected > 100);
        let mut batched = Stepper::load(script).unwrap();
        while batched.advance(1 << 20, false).unwrap().is_some() {}
        while let Some(expected) = stats.pop() {
            let frame = batched.frame(0);
            assert_eq!(frame.stats, expected, "step {}", frame.step);
            assert_eq!(batched.back(), !stats.is_empty());
        }
    }

    #[test]
    fn frames_serialize_to_json() {
        let stepper = Stepper::load("\\x. x").unwrap();
        let json = serde_json::to_string(&stepper.frame(ALL)).unwrap();
        assert!(json.contains(r#""kind":"lam""#), "{json}");
        assert!(json.contains(r#""next":null"#), "{json}");
        assert!(json.contains(r#""size":2"#), "{json}");
    }
}
