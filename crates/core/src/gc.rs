//! Garbage collection.
//!
//! The machine never reduces what the result does not need, so discarded
//! arguments stay in the net as garbage. Collection finds what a reading of
//! the term can still reach from the root and removes the rest. Ports left
//! open by the removal are plugged with erasers.
//!
//! Reachability ignores contexts and follows both branches of a fan entered
//! from its shared side, so it may keep a node that no reading will visit,
//! but it never drops one that some reading needs.

use crate::net::{Kind, Net, NodeId, Port};

/// For each node index and each port of the node, whether a reading from the
/// root can come into the node by that port.
pub fn entries(net: &Net) -> Vec<[bool; 3]> {
    let mut entered = vec![[false; 3]; net.slots()];
    let mut pending: Vec<Port> = vec![net.root().principal()];
    while let Some(exit) = pending.pop() {
        // A port without a wire, as in a net still being built, leads nowhere.
        let Some(entry) = net.wire(exit) else {
            continue;
        };
        let node = entry.node;
        let seen = &mut entered[node.index()][usize::from(entry.slot)];
        if !std::mem::replace(seen, true) {
            let exits = net.kind(node).exits(entry.slot);
            pending.extend(exits.iter().map(|&slot| node.port(slot)));
        }
    }
    entered
}

/// For each node index, whether a reading from the root can reach the node.
pub fn reachable(net: &Net) -> Vec<bool> {
    let mut reached: Vec<bool> = entries(net)
        .iter()
        .map(|ports| ports.contains(&true))
        .collect();
    reached[net.root().index()] = true;
    reached
}

/// Removes everything a reading from the root cannot reach and returns the
/// number of nodes removed.
///
/// The erasers that an earlier collection plugged open ports with are not
/// counted. How many of those there are depends on when the collections ran,
/// and the count should depend on the reduction alone.
pub fn collect(net: &mut Net) -> usize {
    let reached = reachable(net);
    // An eraser is no part of any reading: it lives as long as what it plugs.
    let keeps = |net: &Net, id: NodeId| match net.kind(id) {
        Kind::Eraser => net
            .wire(id.principal())
            .is_some_and(|plugged| reached[plugged.node.index()]),
        _ => reached[id.index()],
    };
    let mut doomed = Vec::new();
    let mut open = Vec::new();
    for (id, kind) in net.nodes() {
        if !keeps(net, id) {
            doomed.push(id);
            continue;
        }
        for slot in 0..kind.ports() {
            if net
                .wire(id.port(slot))
                .is_some_and(|peer| !keeps(net, peer.node))
            {
                open.push(id.port(slot));
            }
        }
    }
    let removed = doomed.iter().filter(|&&id| !net.is_plug(id)).count();
    for id in doomed {
        net.remove(id);
    }
    for port in open {
        net.plug(port);
    }
    net.trim();
    removed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::{Machine, readback};
    use crate::parse::parse;
    use crate::translate::translate;

    #[test]
    fn a_fresh_net_has_no_garbage() {
        for source in [
            r"\x. x",
            r"\x. \y. x",
            r"(\x. x x) (\y. f y y)",
            r"\x. \y. y",
        ] {
            let mut net = translate(&parse(source).unwrap()).unwrap();
            assert_eq!(collect(&mut net), 0, "{source}");
            assert_eq!(net.check(), Ok(()), "{source}");
        }
    }

    #[test]
    fn a_net_with_nothing_but_its_root_is_left_alone() {
        let mut net = Net::new();
        assert_eq!(reachable(&net), [true]);
        assert_eq!(collect(&mut net), 0);
        assert_eq!(net.len(), 1);
    }

    #[test]
    fn discarded_arguments_are_removed() {
        let term = parse(r"(\x. y) ((\x. x x) (\x. x x))").unwrap();
        let mut machine = Machine::new(&term).unwrap();
        assert_eq!(machine.normalize(1_000), Ok(parse("y").unwrap()));
        assert!(machine.net().len() > 2);
        machine.collect();
        // Only the root and the free variable are left.
        assert_eq!(machine.net().len(), 2);
        assert_eq!(machine.net().check(), Ok(()));
        assert_eq!(machine.readback(), Ok(parse("y").unwrap()));
    }

    #[test]
    fn a_half_dead_fan_keeps_its_live_branch() {
        // `x` is shared by a live occurrence and by one inside a discarded
        // argument.
        let term = parse(r"\x. (\y. x) (x x)").unwrap();
        let mut machine = Machine::new(&term).unwrap();
        let expected = parse(r"\x. x").unwrap();
        assert_eq!(machine.normalize(1_000), Ok(expected.clone()));
        let removed = machine.collect();
        assert!(removed > 0);
        assert_eq!(machine.net().check(), Ok(()));
        assert_eq!(readback(machine.net()), Ok(expected));
        // Collecting again finds nothing more.
        assert_eq!(machine.collect(), 0);
    }

    #[test]
    fn the_erasers_a_collection_adds_are_not_counted_when_they_go() {
        // Root, a fan and two free variables. One of them is cut off and
        // collected, which leaves an eraser on the branch it hung from.
        let mut net = Net::new();
        let fan = net.add(Kind::Fan { level: 0 });
        let name = net.intern("a");
        let (kept, dropped) = (net.add(Kind::Free { name }), net.add(Kind::Free { name }));
        net.link(net.root().principal(), fan.port(1));
        net.link(fan.principal(), kept.principal());
        net.link(fan.port(2), dropped.principal());
        assert_eq!(collect(&mut net), 1);
        assert_eq!(net.check(), Ok(()));
        let plug = net.peer(fan.port(2)).node;
        assert!(net.is_plug(plug));
        // Now the fan goes as well, and the eraser with it: one node of the
        // reduction is gone, whenever the first collection ran.
        net.link(net.root().principal(), kept.principal());
        assert_eq!(collect(&mut net), 1);
        assert_eq!(net.len(), 2);
        assert_eq!(net.check(), Ok(()));
    }
}
