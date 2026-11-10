//! Placement of a net on a grid, for drawing.
//!
//! The net is laid out the way the term it stands for would be: the root at
//! the top, each node above what a reading reaches from it, leaves spread
//! from left to right. Wires that follow the reading form a tree. The others,
//! which lead back to binders or into nodes that are shared, are left for the
//! drawing to route as it likes.
//!
//! The placement recurses as deep as the net, so it is meant for nets small
//! enough to look at.

use std::collections::HashSet;

use crate::net::{Kind, Net, NodeId, Port, slot};

/// Where a node goes.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Placement {
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
    pub ends: [Port; 2],
    /// Whether the wire is part of the tree that the placement follows.
    pub in_tree: bool,
}

#[derive(Clone, Debug, Default)]
pub struct Diagram {
    pub placements: Vec<Placement>,
    pub wires: Vec<Wire>,
}

/// Places every node of `net` and lists its wires.
pub fn layout(net: &Net) -> Diagram {
    let size = net.nodes().map(|(id, _)| id.index() + 1).max().unwrap_or(0);
    let mut planner = Planner {
        net,
        placed: vec![None; size],
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
    // Erasers hang beside the port they plug.
    for (id, kind) in net.nodes() {
        if kind == Kind::Eraser {
            let plugged = net.peer(id.principal()).node;
            let (column, row) = planner.placed[plugged.index()].unwrap_or((0.0, 0));
            planner.placed[id.index()] = Some((column + 0.5, row + 1));
        }
    }

    let placements = net
        .nodes()
        .filter_map(|(node, _)| {
            let (column, row) = planner.placed[node.index()]?;
            Some(Placement { node, column, row })
        })
        .collect();
    let mut wires = Vec::new();
    for (id, kind) in net.nodes() {
        for slot in 0..kind.ports() {
            let port = id.port(slot);
            let peer = net.peer(port);
            if (peer.node, peer.slot) >= (port.node, port.slot) {
                wires.push(Wire {
                    ends: [port, peer],
                    in_tree: planner.tree.contains(&port) || planner.tree.contains(&peer),
                });
            }
        }
    }
    Diagram { placements, wires }
}

struct Planner<'a> {
    net: &'a Net,
    /// Column and row of each node placed so far, by node index.
    placed: Vec<Option<(f32, u32)>>,
    /// The upper ends of the wires the placement followed.
    tree: HashSet<Port>,
    next_column: f32,
}

impl Planner<'_> {
    /// Places `node`, entered by the port `entered`, and everything below it
    /// that is not placed yet. Returns the column of the node.
    fn place(&mut self, node: NodeId, entered: u8, row: u32) -> f32 {
        // Claim the node before going down, so that cycles stop here.
        self.placed[node.index()] = Some((0.0, row));
        let mut children = Vec::new();
        for &slot in self.net.kind(node).exits(entered) {
            let exit = node.port(slot);
            let entry = self.net.peer(exit);
            if self.placed[entry.node.index()].is_none() {
                self.tree.insert(exit);
                children.push(self.place(entry.node, entry.slot, row + 1));
            }
        }
        let column = match (children.first(), children.last()) {
            (Some(first), Some(last)) => (first + last) / 2.0,
            _ => {
                self.next_column += 1.0;
                self.next_column - 1.0
            }
        };
        self.placed[node.index()] = Some((column, row));
        column
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;
    use crate::translate::translate;

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

    #[test]
    fn erasers_hang_beside_what_they_plug() {
        let (net, diagram) = diagram(r"\x. y");
        let lam = net.peer(net.root().principal()).node;
        let eraser = net.peer(lam.port(slot::VAR)).node;
        let (column, row) = position(&diagram, lam);
        assert_eq!(position(&diagram, eraser), (column + 0.5, row + 1));
    }
}
