//! The interaction net: an arena of nodes wired port to port.
//!
//! Every node has a principal port (slot 0) and up to two auxiliary ports.
//! Two nodes interact only when their principal ports face each other. Nodes
//! refer to each other by index, so the net is a plain vector and rewiring
//! never fights the borrow checker.

use std::collections::HashMap;
use std::sync::Arc;

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
    /// The position of the node in the net's arena.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// The port of this node in the given slot.
    pub fn port(self, slot: u8) -> Port {
        Port { node: self, slot }
    }

    /// The principal port of this node.
    pub fn principal(self) -> Port {
        self.port(slot::PRINCIPAL)
    }
}

/// One port of one node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Port {
    /// The node the port belongs to.
    pub node: NodeId,
    /// Which port of the node it is: see [`slot`].
    pub slot: u8,
}

impl Port {
    /// Whether this is the principal port of its node.
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
    Lam {
        /// The name of the variable, kept as a hint for printing.
        name: Symbol,
    },
    /// An application. Ports: function, result, argument.
    App,
    /// A fan, which shares what its principal port sees between two branches.
    /// Ports: shared side, first branch, second branch.
    Fan {
        /// How many scopes the fan is inside of, counted from the scope of
        /// what it shares.
        level: u32,
    },
    /// A delimiter, which marks the border of a scope. Ports: outside, inside.
    ///
    /// One node stands for `count` delimiters of the same level stacked on
    /// each other, that is, for the borders of that many nested scopes.
    Delim {
        /// How many scopes lie between the delimiter and the scope it
        /// borders.
        level: u32,
        /// The height of the stack.
        count: u32,
    },
    /// A plug for a port nothing uses. Ports: the unused side.
    Eraser,
    /// A free variable. Ports: parent.
    Free {
        /// The name of the variable.
        name: Symbol,
    },
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

    /// The ports through which a reading of the term goes on after it has
    /// come into a node of this kind by the port `entered`.
    ///
    /// A reading goes down: from an abstraction to its body, from an
    /// application to its function and argument, and through fans and
    /// delimiters to whatever lies on their other side. It stops at
    /// variables. Without a context it cannot tell which branch of a fan to
    /// take from the shared side, so both are listed.
    pub fn exits(self, entered: u8) -> &'static [u8] {
        match (self, entered) {
            (Kind::Root, _) => &[slot::PRINCIPAL],
            (Kind::Lam { .. }, slot::PRINCIPAL) => &[slot::BODY],
            (Kind::App, slot::RESULT) => &[slot::PRINCIPAL, slot::ARG],
            (Kind::Fan { .. }, slot::PRINCIPAL) => &slot::BRANCHES,
            (Kind::Delim { .. }, slot::PRINCIPAL) => &[slot::INSIDE],
            (Kind::Fan { .. } | Kind::Delim { .. }, _) => &[slot::PRINCIPAL],
            _ => &[],
        }
    }
}

#[derive(Clone, Debug)]
struct Node {
    kind: Kind,
    links: [Option<Port>; 3],
    serial: u64,
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
    /// Shared between the copies of a net, which rarely learn new names.
    symbols: Arc<Symbols>,
    root: NodeId,
    next_serial: u64,
    next_plug_serial: u64,
}

/// Where the serials of the erasers added by [`Net::plug`] start.
const PLUG_SERIALS: u64 = 1 << 63;

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
            symbols: Arc::default(),
            root: NodeId(0),
            next_serial: 0,
            next_plug_serial: PLUG_SERIALS,
        };
        net.root = net.add(Kind::Root);
        net
    }

    /// The node the term hangs from.
    pub fn root(&self) -> NodeId {
        self.root
    }

    /// The number of nodes in the net.
    pub fn len(&self) -> usize {
        self.cells.len() - self.vacant.len()
    }

    /// The bytes one place for a node takes.
    pub const SLOT_BYTES: usize = size_of::<Option<Node>>();

    /// The number of places for nodes the net holds, in use or not: what a
    /// copy of the net costs.
    pub fn slots(&self) -> usize {
        self.cells.len()
    }

    /// Gives up the unused places at the end of the net, so that a net that
    /// was large once does not stay large.
    pub fn trim(&mut self) {
        let used = self
            .cells
            .iter()
            .rposition(Option::is_some)
            .map_or(0, |last| last + 1);
        if used < self.cells.len() {
            self.cells.truncate(used);
            self.vacant.retain(|id| id.index() < used);
        }
    }

    /// Whether the net has no nodes. It never is: the root is always there.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The symbol for `name`, the same one every time.
    pub fn intern(&mut self, name: &str) -> Symbol {
        if let Some(&symbol) = self.symbols.index.get(name) {
            return symbol;
        }
        let index = u32::try_from(self.symbols.names.len()).expect("fewer than 2^32 names");
        let symbol = Symbol(index);
        let symbols = Arc::make_mut(&mut self.symbols);
        symbols.names.push(name.to_owned());
        symbols.index.insert(name.to_owned(), symbol);
        symbol
    }

    /// The name a symbol of this net stands for.
    pub fn name(&self, symbol: Symbol) -> &str {
        &self.symbols.names[symbol.0 as usize]
    }

    /// Adds a node with all its ports unlinked.
    pub fn add(&mut self, kind: Kind) -> NodeId {
        let serial = self.next_serial;
        self.next_serial += 1;
        self.insert(kind, serial)
    }

    /// Adds an eraser on `port`, which was left open when what it led to
    /// was removed.
    ///
    /// Such an eraser is numbered apart from the other nodes. Garbage can be
    /// removed sooner or later, and this keeps the serials of the nodes a
    /// reduction creates the same either way.
    pub fn plug(&mut self, port: Port) -> NodeId {
        let serial = self.next_plug_serial;
        self.next_plug_serial += 1;
        let eraser = self.insert(Kind::Eraser, serial);
        self.link(eraser.principal(), port);
        eraser
    }

    fn insert(&mut self, kind: Kind, serial: u64) -> NodeId {
        let node = Node {
            kind,
            links: [None; 3],
            serial,
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

    /// What the node is.
    pub fn kind(&self, id: NodeId) -> Kind {
        self.node(id).kind
    }

    /// Changes what a node is. The new kind must have as many ports.
    pub fn set_kind(&mut self, id: NodeId, kind: Kind) {
        let node = self.cells[id.index()]
            .as_mut()
            .unwrap_or_else(|| panic!("node {id:?} is not in the net"));
        assert_eq!(node.kind.ports(), kind.ports(), "a node keeps its ports");
        node.kind = kind;
    }

    /// A number that tells this node apart from every node the net has ever
    /// held. Identifiers are reused once a node is removed; serials are not.
    pub fn serial(&self, id: NodeId) -> u64 {
        self.node(id).serial
    }

    /// Whether `id` names a node that is currently in the net.
    pub fn contains(&self, id: NodeId) -> bool {
        matches!(self.cells.get(id.index()), Some(Some(_)))
    }

    /// The port at the other end of the wire attached to `port`.
    ///
    /// Panics if the port is not linked, which it always is once a net is
    /// built. Use [`wire`](Net::wire) on a net that may be half built.
    pub fn peer(&self, port: Port) -> Port {
        self.wire(port)
            .unwrap_or_else(|| panic!("{port:?} is not linked"))
    }

    /// The port at the other end of the wire attached to `port`, if there is
    /// a wire.
    pub fn wire(&self, port: Port) -> Option<Port> {
        self.node(port.node).links[usize::from(port.slot)]
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
        let delim = net.add(Kind::Delim { level: 0, count: 1 });
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
    fn trimming_gives_up_the_unused_end() {
        let mut net = Net::new();
        let nodes: Vec<NodeId> = (0..4).map(|_| net.add(Kind::Eraser)).collect();
        net.remove(nodes[0]);
        net.remove(nodes[2]);
        net.remove(nodes[3]);
        assert_eq!(net.slots(), 5);
        net.trim();
        // The hole in the middle stays, and is the next place used.
        assert_eq!((net.slots(), net.len()), (3, 2));
        assert_eq!(net.add(Kind::App), nodes[0]);
        assert_eq!(net.add(Kind::App), nodes[2]);
        assert_eq!((net.slots(), net.len()), (4, 4));
    }

    #[test]
    fn serials_are_never_reused() {
        let mut net = Net::new();
        let first = net.add(Kind::Eraser);
        let serial = net.serial(first);
        net.remove(first);
        assert!(!net.contains(first));
        let second = net.add(Kind::Eraser);
        assert_eq!(second, first);
        assert_ne!(net.serial(second), serial);
    }

    #[test]
    fn plugs_leave_the_numbering_of_other_nodes_alone() {
        let mut net = Net::new();
        let first = net.add(Kind::App);
        let plug = net.plug(first.port(slot::ARG));
        let second = net.add(Kind::App);
        assert_eq!(net.kind(plug), Kind::Eraser);
        assert_eq!(net.peer(first.port(slot::ARG)), plug.principal());
        assert_eq!(net.serial(second), net.serial(first) + 1);
        let other = net.plug(second.port(slot::ARG));
        assert_ne!(net.serial(plug), net.serial(other));
    }

    #[test]
    fn readings_go_down() {
        let lam = Kind::Lam {
            name: Net::new().intern("x"),
        };
        assert_eq!(lam.exits(slot::PRINCIPAL), [slot::BODY]);
        assert!(lam.exits(slot::VAR).is_empty());
        assert_eq!(Kind::App.exits(slot::RESULT), [slot::PRINCIPAL, slot::ARG]);
        assert_eq!(Kind::Fan { level: 0 }.exits(slot::PRINCIPAL), [1, 2]);
        assert_eq!(Kind::Fan { level: 0 }.exits(2), [slot::PRINCIPAL]);
        assert_eq!(
            Kind::Delim { level: 0, count: 1 }.exits(slot::INSIDE),
            [slot::PRINCIPAL]
        );
        assert!(Kind::Eraser.exits(slot::PRINCIPAL).is_empty());
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
