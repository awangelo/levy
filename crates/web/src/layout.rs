//! Placement of a net on a grid, for drawing.
//!
//! The net is laid out the way the term it stands for would be: the root at
//! the top, each node above what a reading reaches from it, leaves spread
//! from left to right. Wires that follow the reading form a tree. The others,
//! which lead back to binders or into nodes that are shared, are left for the
//! drawing to route as it likes.

use std::collections::HashSet;

use levy_core::gc;
use levy_core::net::{Kind, Net, NodeId, Port, slot};

/// Where a node goes.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Placement {
    /// The node that is placed.
    pub node: NodeId,
    /// Horizontal position, in columns. Leaves take whole columns and inner
    /// nodes sit halfway between their outermost children.
    pub column: f32,
    /// Vertical position, in rows from the top.
    pub row: u32,
}

/// A wire between two ports.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Wire {
    /// The two ports the wire joins.
    pub ends: [Port; 2],
    /// Whether the wire is part of the tree that the placement follows.
    pub in_tree: bool,
}

/// A net as a picture: where its nodes go, and the wires between them.
#[derive(Clone, Debug, Default)]
pub struct Diagram {
    /// One place per node, in the order of the nodes in the net.
    pub placements: Vec<Placement>,
    /// Every wire once.
    pub wires: Vec<Wire>,
}

/// Places every node of `net` and lists its wires.
pub fn layout(net: &Net) -> Diagram {
    let mut planner = Planner {
        net,
        entered: gc::entries(net),
        placed: vec![None; net.slots()],
        tree: HashSet::new(),
        next_column: 0.0,
    };
    planner.place(net.root(), slot::PRINCIPAL, 0);
    // Garbage, if it has not been collected, goes to the right of the term.
    for (id, kind) in net.nodes() {
        if planner.placed[id.index()].is_none() && kind != Kind::Eraser {
            let entered = if kind == Kind::App {
                slot::RESULT
            } else {
                slot::PRINCIPAL
            };
            planner.place(id, entered, 0);
        }
    }
    // Erasers hang beside the port they plug, moved further aside if the
    // place is taken.
    let mut taken: HashSet<(u32, u32)> = planner
        .placed
        .iter()
        .flatten()
        .map(|&(column, row)| (column.to_bits(), row))
        .collect();
    for (id, kind) in net.nodes() {
        if kind != Kind::Eraser {
            continue;
        }
        let plugged = net
            .wire(id.principal())
            .and_then(|plugged| Some((plugged, planner.placed[plugged.node.index()]?)));
        let (mut column, row, aside) = match plugged {
            Some((plugged, (column, row))) => {
                let (aside, below) = beside(net.kind(plugged.node), plugged.slot);
                let row = if below {
                    row + 1
                } else {
                    row.saturating_sub(1)
                };
                (column + aside, row, aside)
            }
            None => (0.0, 0, 0.5),
        };
        while !taken.insert((column.to_bits(), row)) {
            column += aside / 2.0;
        }
        planner.placed[id.index()] = Some((column, row));
    }

    let placements = net
        .nodes()
        .filter_map(|(node, _)| {
            let (column, row) = planner.placed[node.index()]?;
            Some(Placement { node, column, row })
        })
        .collect();
    let wires = net
        .wires()
        .map(|ends| Wire {
            ends,
            in_tree: ends.iter().any(|end| planner.tree.contains(end)),
        })
        .collect();
    Diagram { placements, wires }
}

/// Where the eraser that plugs a port goes, seen from the node of the port:
/// how many columns aside, and whether a row below it or a row above.
///
/// The ports of one node get different places, so that two erasers on one
/// node start out apart.
fn beside(kind: Kind, plugged: u8) -> (f32, bool) {
    let upward = match kind {
        // An application hangs from its result port, the others from their
        // principal port.
        Kind::App => plugged == slot::RESULT,
        Kind::Root => false,
        _ => plugged == slot::PRINCIPAL,
    };
    if upward {
        return (0.5, false);
    }
    let leftward = match kind {
        Kind::App => plugged == slot::PRINCIPAL,
        Kind::Lam { .. } => plugged == slot::BODY,
        Kind::Fan { .. } => plugged == slot::BRANCHES[0],
        _ => false,
    };
    (if leftward { -0.5 } else { 0.5 }, true)
}

struct Planner<'a> {
    net: &'a Net,
    /// Per node index, the ports by which a reading from the root comes in.
    entered: Vec<[bool; 3]>,
    /// Column and row of each node placed so far, by node index.
    placed: Vec<Option<(f32, u32)>>,
    /// The upper ends of the wires the placement followed.
    tree: HashSet<Port>,
    next_column: f32,
}

/// A node whose subtree is being placed.
struct Visit {
    node: NodeId,
    row: u32,
    /// The ports that lead further down, and how many were followed so far.
    exits: Vec<Port>,
    followed: usize,
    /// The columns of the first and of the last child placed.
    span: Option<(f32, f32)>,
}

impl Planner<'_> {
    /// The ports by which a reading goes on from `node`.
    ///
    /// A node that a reading can come into by several ports is placed once,
    /// so this takes all of them together. A node no reading reaches is
    /// garbage, and is read as if it had been come into by `entered`.
    fn exits(&self, node: NodeId, entered: u8) -> Vec<Port> {
        let kind = self.net.kind(node);
        let known = self.entered[node.index()];
        let mut exits: Vec<Port> = Vec::new();
        for slot in 0..kind.ports() {
            let comes_in = if known.contains(&true) {
                known[usize::from(slot)]
            } else {
                slot == entered
            };
            if comes_in {
                for &exit in kind.exits(slot) {
                    if !exits.contains(&node.port(exit)) {
                        exits.push(node.port(exit));
                    }
                }
            }
        }
        exits
    }

    /// Whether to leave `entry.node` for another wire to bring into the tree.
    ///
    /// A wire that ends at the variable port of an abstraction, or at an
    /// application from below, is a way back up: nothing can be read on from
    /// there. If a reading also comes into the node the proper way, the node
    /// belongs under that wire, with its subterms below it.
    fn is_way_back(&self, entry: Port) -> bool {
        let kind = self.net.kind(entry.node);
        let known = self.entered[entry.node.index()];
        kind.exits(entry.slot).is_empty()
            && (0..kind.ports())
                .any(|slot| known[usize::from(slot)] && !kind.exits(slot).is_empty())
    }

    /// Places `node`, come into by the port `entered`, and everything below
    /// it that is not placed yet.
    ///
    /// A net can be as deep as it is large, so the nodes whose subtrees are
    /// under way are kept in a list, not in recursive calls.
    fn place(&mut self, node: NodeId, entered: u8, row: u32) {
        // A node is claimed before its subtree is placed, so that cycles
        // stop there.
        self.placed[node.index()] = Some((0.0, row));
        let mut under_way = vec![Visit {
            node,
            row,
            exits: self.exits(node, entered),
            followed: 0,
            span: None,
        }];
        while let Some(visit) = under_way.last_mut() {
            if let Some(&exit) = visit.exits.get(visit.followed) {
                visit.followed += 1;
                let row = visit.row + 1;
                let Some(entry) = self.net.wire(exit) else {
                    continue;
                };
                if self.placed[entry.node.index()].is_some() || self.is_way_back(entry) {
                    continue;
                }
                self.tree.insert(exit);
                self.placed[entry.node.index()] = Some((0.0, row));
                under_way.push(Visit {
                    node: entry.node,
                    row,
                    exits: self.exits(entry.node, entry.slot),
                    followed: 0,
                    span: None,
                });
                continue;
            }
            let column = match visit.span {
                Some((first, last)) => (first + last) / 2.0,
                None => {
                    self.next_column += 1.0;
                    self.next_column - 1.0
                }
            };
            self.placed[visit.node.index()] = Some((column, visit.row));
            under_way.pop();
            if let Some(parent) = under_way.last_mut() {
                parent.span = Some((parent.span.map_or(column, |(first, _)| first), column));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use levy_core::translate::translate;
    use levy_core::{Machine, Term, parse};

    fn diagram(source: &str) -> (Net, Diagram) {
        let net = translate(&parse(source).unwrap()).unwrap();
        let diagram = layout(&net);
        (net, diagram)
    }

    fn position(diagram: &Diagram, node: NodeId) -> (f32, u32) {
        let placement = diagram
            .placements
            .iter()
            .find(|placement| placement.node == node)
            .expect("every node is placed");
        (placement.column, placement.row)
    }

    #[test]
    fn every_node_and_wire_appears_once() {
        for source in [r"\x. x", r"(\x. x x) (\y. f y y)", r"\x. \y. \z. x z (y z)"] {
            let (net, diagram) = diagram(source);
            assert_eq!(diagram.placements.len(), net.len(), "{source}");
            let ports: usize = net.nodes().map(|(_, kind)| usize::from(kind.ports())).sum();
            assert_eq!(diagram.wires.len() * 2, ports, "{source}");
        }
    }

    #[test]
    fn children_sit_below_and_around_their_parent() {
        let (net, diagram) = diagram("f a");
        let app = net.peer(net.root().principal()).node;
        let func = net.peer(app.principal()).node;
        let arg = net.peer(app.port(slot::ARG)).node;
        assert_eq!(position(&diagram, net.root()), (0.5, 0));
        assert_eq!(position(&diagram, app), (0.5, 1));
        assert_eq!(position(&diagram, func), (0.0, 2));
        assert_eq!(position(&diagram, arg), (1.0, 2));
        assert!(diagram.wires.iter().all(|wire| wire.in_tree));
    }

    #[test]
    fn wires_back_to_binders_are_not_in_the_tree() {
        let (net, diagram) = diagram(r"\x. x");
        let lam = net.peer(net.root().principal()).node;
        let back: Vec<&Wire> = diagram.wires.iter().filter(|wire| !wire.in_tree).collect();
        assert_eq!(back.len(), 1);
        assert_eq!(back[0].ends, [lam.port(slot::BODY), lam.port(slot::VAR)]);
    }

    /// The nodes that sit in the top row although they are not the root:
    /// subterms the placement failed to hang under anything.
    fn detached(net: &Net, diagram: &Diagram) -> Vec<Kind> {
        diagram
            .placements
            .iter()
            .filter(|placement| placement.row == 0 && placement.node != net.root())
            .map(|placement| net.kind(placement.node))
            .filter(|kind| *kind != Kind::Eraser)
            .collect()
    }

    #[test]
    fn a_reduction_stays_one_tree_with_no_two_nodes_on_one_spot() {
        let two = r"(\f x. f (f x))";
        let fact = r"(\n. n (\p. p (\a b s. s (\f x. f (a f x)) (\f. a (b f)))) (\s. s (\f x. x) (\f x. f x)) (\a b. b))";
        for source in [
            format!("{two} {two}"),
            format!("{two} {two} {two}"),
            format!("{fact} {two}"),
            r"(\x. \y. x) a ((\x. x x) (\x. x x))".to_owned(),
        ] {
            let mut machine = Machine::new(&parse(&source).unwrap()).unwrap();
            loop {
                machine.collect();
                let net = machine.net();
                let diagram = layout(net);
                let step = machine.stats().interactions();
                assert_eq!(detached(net, &diagram), [], "{source}, step {step}");
                assert_eq!(diagram.placements.len(), net.len(), "{source}, step {step}");
                let mut spots: Vec<(u32, u32)> = diagram
                    .placements
                    .iter()
                    .map(|placement| (placement.column.to_bits(), placement.row))
                    .collect();
                spots.sort_unstable();
                spots.dedup();
                assert_eq!(spots.len(), net.len(), "{source}, step {step}");
                if machine.step().unwrap().is_none() {
                    break;
                }
            }
        }
    }

    #[test]
    fn deep_nets_need_no_deep_stack() {
        let net = translate(&Term::church(100_000)).unwrap();
        let diagram = layout(&net);
        assert_eq!(diagram.placements.len(), net.len());
        assert_eq!(detached(&net, &diagram), []);
    }

    #[test]
    fn a_net_with_nothing_but_its_root_has_one_node_and_no_wires() {
        let diagram = layout(&Net::new());
        assert_eq!(diagram.placements.len(), 1);
        assert!(diagram.wires.is_empty());
    }

    #[test]
    fn two_erasers_on_one_node_keep_apart() {
        // An abstraction that nothing uses any more, plugged on both sides.
        let mut net = Net::new();
        let name = net.intern("x");
        let lam = net.add(Kind::Lam { name });
        let free = net.add(Kind::Free { name });
        net.link(net.root().principal(), free.principal());
        let (above, below) = (net.add(Kind::Eraser), net.add(Kind::Eraser));
        net.link(lam.principal(), above.principal());
        net.link(lam.port(slot::VAR), below.principal());
        net.link(lam.port(slot::BODY), free.principal());
        net.link(net.root().principal(), free.principal());
        let body = net.add(Kind::Eraser);
        net.link(lam.port(slot::BODY), body.principal());
        let diagram = layout(&net);
        let spots = [above, below, body].map(|eraser| position(&diagram, eraser));
        assert_ne!(spots[0], spots[1]);
        assert_ne!(spots[0], spots[2]);
        assert_ne!(spots[1], spots[2]);
    }

    #[test]
    fn erasers_hang_beside_what_they_plug() {
        let (net, diagram) = diagram(r"\x. y");
        let lam = net.peer(net.root().principal()).node;
        let eraser = net.peer(lam.port(slot::VAR)).node;
        let (column, row) = position(&diagram, lam);
        assert_eq!(position(&diagram, eraser), (column + 0.5, row + 1));
    }
}
