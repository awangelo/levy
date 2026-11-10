//! The interaction net: an arena of nodes wired port to port.
//!
//! Every node has a principal port (slot 0) and up to two auxiliary ports.
//! Two nodes interact only when their principal ports face each other. Nodes
//! refer to each other by index, so the net is a plain vector and rewiring
//! never fights the borrow checker.

use std::collections::HashMap;

/// Slot numbers of the ports of each kind of node.
pub mod slot {
    /// The principal port of any node.
    pub const PRINCIPAL: u8 = 0;
    /// Abstraction: the body.
    pub const BODY: u8 = 1;
    /// Abstraction: the bound variable.
    pub const VAR: u8 = 2;
    /// Application: where the result goes, that is, the parent.
    pub const RESULT: u8 = 1;
    /// Application: the argument.
    pub const ARG: u8 = 2;
    /// Delimiter: the side that lies inside the scope.
    pub const INSIDE: u8 = 1;
    /// Fan: the two branches.
    pub const BRANCHES: [u8; 2] = [1, 2];
}

/// Identifies a node of a [`Net`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(u32);

impl NodeId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn port(self, slot: u8) -> Port {
        Port { node: self, slot }
    }

    pub fn principal(self) -> Port {
        self.port(slot::PRINCIPAL)
    }
}

/// One port of one node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Port {
    pub node: NodeId,
    pub slot: u8,
}

impl Port {
    pub fn is_principal(self) -> bool {
        self.slot == slot::PRINCIPAL
    }
}

/// An interned name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

/// What a node is. The principal port is listed first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// The entry point of the net. Ports: the term.
    Root,
    /// An abstraction. Ports: parent, body, variable.
    Lam { name: Symbol },
    /// An application. Ports: function, result, argument.
    App,
    /// A fan, which shares what its principal port sees between two branches.
    /// Ports: shared side, first branch, second branch.
    Fan { level: u32 },
    /// A delimiter, which marks the border of a scope. Ports: outside, inside.
    Delim { level: u32 },
    /// A plug for a port nothing uses. Ports: the unused side.
    Eraser,
    /// A free variable. Ports: parent.
    Free { name: Symbol },
}

impl Kind {
    /// The number of ports, the principal one included.
    pub fn ports(self) -> u8 {
        match self {
            Kind::Root | Kind::Eraser | Kind::Free { .. } => 1,
            Kind::Delim { .. } => 2,
            Kind::Lam { .. } | Kind::App | Kind::Fan { .. } => 3,
        }
    }
}

#[derive(Clone, Debug)]
struct Node {
    kind: Kind,
    links: [Option<Port>; 3],
}

#[derive(Clone, Debug, Default)]
struct Symbols {
    names: Vec<String>,
    index: HashMap<String, Symbol>,
}

/// An interaction net.
#[derive(Clone, Debug)]
pub struct Net {
    cells: Vec<Option<Node>>,
    vacant: Vec<NodeId>,
    symbols: Symbols,
    root: NodeId,
}

impl Default for Net {
    fn default() -> Self {
        Net::new()
    }
}

impl Net {
    /// A net holding only its root, whose port is not linked yet.
    pub fn new() -> Net {
        let mut net = Net {
            cells: Vec::new(),
            vacant: Vec::new(),
            symbols: Symbols::default(),
            root: NodeId(0),
        };
        net.root = net.add(Kind::Root);
        net
    }

    pub fn root(&self) -> NodeId {
        self.root
    }

    /// The number of nodes in the net.
    pub fn len(&self) -> usize {
        self.cells.len() - self.vacant.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn intern(&mut self, name: &str) -> Symbol {
        if let Some(&symbol) = self.symbols.index.get(name) {
            return symbol;
        }
        let index = u32::try_from(self.symbols.names.len()).expect("fewer than 2^32 names");
        let symbol = Symbol(index);
        self.symbols.names.push(name.to_owned());
        self.symbols.index.insert(name.to_owned(), symbol);
        symbol
    }

    pub fn name(&self, symbol: Symbol) -> &str {
        &self.symbols.names[symbol.0 as usize]
    }

    /// Adds a node with all its ports unlinked.
    pub fn add(&mut self, kind: Kind) -> NodeId {
        let node = Node {
            kind,
            links: [None; 3],
        };
        if let Some(id) = self.vacant.pop() {
            self.cells[id.index()] = Some(node);
            id
        } else {
            let index = u32::try_from(self.cells.len()).expect("fewer than 2^32 nodes");
            self.cells.push(Some(node));
            NodeId(index)
        }
    }

    /// Removes a node. Ports that were linked to it are left dangling, so the
    /// caller must have rewired them already.
    pub fn remove(&mut self, id: NodeId) {
        let cell = self.cells[id.index()].take();
        assert!(cell.is_some(), "node {id:?} was already removed");
        self.vacant.push(id);
    }

    fn node(&self, id: NodeId) -> &Node {
        self.cells[id.index()]
            .as_ref()
            .unwrap_or_else(|| panic!("node {id:?} is not in the net"))
    }

    pub fn kind(&self, id: NodeId) -> Kind {
        self.node(id).kind
    }

    /// The port at the other end of the wire attached to `port`.
    pub fn peer(&self, port: Port) -> Port {
        self.node(port.node).links[usize::from(port.slot)]
            .unwrap_or_else(|| panic!("{port:?} is not linked"))
    }

    /// Connects two ports with a wire, forgetting their previous wires.
    pub fn link(&mut self, a: Port, b: Port) {
        self.set_link(a, b);
        self.set_link(b, a);
    }

    fn set_link(&mut self, from: Port, to: Port) {
        let node = self.cells[from.node.index()]
            .as_mut()
            .unwrap_or_else(|| panic!("node {:?} is not in the net", from.node));
        node.links[usize::from(from.slot)] = Some(to);
    }

    /// Makes `new` take over the wire attached to `old`.
    ///
    /// The link stored at `old` goes stale, which is fine for a port whose
    /// node is about to be removed.
    pub fn transfer(&mut self, old: Port, new: Port) {
        self.link(new, self.peer(old));
    }

    /// Joins the wires attached to `a` and `b` into one, bypassing both.
    pub fn splice(&mut self, a: Port, b: Port) {
        let (beyond_a, beyond_b) = (self.peer(a), self.peer(b));
        if beyond_a != b {
            self.link(beyond_a, beyond_b);
        }
    }

    /// All nodes, in index order.
    pub fn nodes(&self) -> impl Iterator<Item = (NodeId, Kind)> + '_ {
        (0u32..)
            .zip(&self.cells)
            .filter_map(|(index, cell)| cell.as_ref().map(|node| (NodeId(index), node.kind)))
    }

    /// Verifies that every port is linked to a port that links back.
    pub fn check(&self) -> Result<(), String> {
        if !matches!(self.kind(self.root), Kind::Root) {
            return Err("the root is not a root node".to_owned());
        }
        for (id, kind) in self.nodes() {
            for slot in 0..3u8 {
                let port = id.port(slot);
                let link = self.node(id).links[usize::from(slot)];
                if slot >= kind.ports() {
                    if link.is_some() {
                        return Err(format!("{port:?} of {kind:?} should not exist"));
                    }
                    continue;
                }
                let Some(peer) = link else {
                    return Err(format!("{port:?} of {kind:?} is not linked"));
                };
                let Some(Some(target)) = self.cells.get(peer.node.index()) else {
                    return Err(format!("{port:?} links to a removed node"));
                };
                if target.links[usize::from(peer.slot)] != Some(port) {
                    return Err(format!(
                        "{port:?} links to {peer:?}, which does not link back"
                    ));
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linking_is_symmetric() {
        let mut net = Net::new();
        let eraser = net.add(Kind::Eraser);
        net.link(net.root().principal(), eraser.principal());
        assert_eq!(net.peer(net.root().principal()), eraser.principal());
        assert_eq!(net.peer(eraser.principal()), net.root().principal());
        assert_eq!(net.check(), Ok(()));
    }

    #[test]
    fn check_reports_unlinked_ports() {
        let mut net = Net::new();
        let fan = net.add(Kind::Fan { level: 0 });
        net.link(net.root().principal(), fan.principal());
        assert!(net.check().is_err());
    }

    #[test]
    fn removed_slots_are_reused() {
        let mut net = Net::new();
        let first = net.add(Kind::Eraser);
        net.remove(first);
        assert_eq!(net.len(), 1);
        assert_eq!(net.add(Kind::App), first);
        assert_eq!(net.len(), 2);
    }

    #[test]
    fn splice_joins_wires_and_drops_closed_loops() {
        let mut net = Net::new();
        let delim = net.add(Kind::Delim { level: 0 });
        let free = {
            let name = net.intern("y");
            net.add(Kind::Free { name })
        };
        net.link(net.root().principal(), delim.principal());
        net.link(delim.port(slot::INSIDE), free.principal());
        net.splice(delim.principal(), delim.port(slot::INSIDE));
        net.remove(delim);
        assert_eq!(net.peer(net.root().principal()), free.principal());
        assert_eq!(net.check(), Ok(()));

        let (a, b) = (
            net.add(Kind::Fan { level: 0 }),
            net.add(Kind::Fan { level: 0 }),
        );
        net.link(a.principal(), b.principal());
        net.link(a.port(1), b.port(2));
        net.link(a.port(2), b.port(1));
        net.splice(a.port(1), b.port(1));
        net.splice(a.port(2), b.port(2));
        net.remove(a);
        net.remove(b);
        assert_eq!(net.len(), 2);
        assert_eq!(net.check(), Ok(()));
    }

    #[test]
    fn names_are_interned_once() {
        let mut net = Net::new();
        let x = net.intern("x");
        assert_eq!(net.intern("x"), x);
        assert_ne!(net.intern("y"), x);
        assert_eq!(net.name(x), "x");
    }
}
