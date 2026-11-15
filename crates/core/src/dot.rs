//! Graphviz export, for looking at a net while debugging.

use std::fmt::Write;

use crate::net::{Kind, Net, slot};

/// Renders the net in Graphviz DOT format.
///
/// Each wire is labelled at both ends with the port it attaches to. The
/// principal port is marked with a dot.
pub fn to_dot(net: &Net) -> String {
    let mut out = String::from("graph net {\n  node [shape=circle];\n");
    for (id, kind) in net.nodes() {
        let label = match kind {
            Kind::Root => "root".to_owned(),
            Kind::Lam { name } => format!("λ{}", net.name(name)),
            Kind::App => "@".to_owned(),
            Kind::Fan { level } => format!("▽{level}"),
            Kind::Delim { level, count: 1 } => format!("⌒{level}"),
            Kind::Delim { level, count } => format!("⌒{level}×{count}"),
            Kind::Eraser => "⊗".to_owned(),
            Kind::Free { name } => net.name(name).to_owned(),
        };
        // Names come from the outside, and a quote in one would end the label.
        let label = label.replace('\\', "\\\\").replace('"', "\\\"");
        writeln!(out, "  n{} [label=\"{label}\"];", id.index()).expect("writing to a string");
    }
    for (id, kind) in net.nodes() {
        for slot in 0..kind.ports() {
            let port = id.port(slot);
            // A net still being built can have ports without a wire.
            let Some(peer) = net.wire(port) else {
                continue;
            };
            if (peer.node, peer.slot) < (port.node, port.slot) {
                continue;
            }
            writeln!(
                out,
                "  n{} -- n{} [taillabel=\"{}\", headlabel=\"{}\"];",
                port.node.index(),
                peer.node.index(),
                port_name(kind, port.slot),
                port_name(net.kind(peer.node), peer.slot),
            )
            .expect("writing to a string");
        }
    }
    out.push_str("}\n");
    out
}

fn port_name(kind: Kind, port: u8) -> &'static str {
    match (kind, port) {
        (_, slot::PRINCIPAL) => "•",
        (Kind::Lam { .. }, slot::BODY) => "body",
        (Kind::Lam { .. }, _) => "var",
        (Kind::App, slot::RESULT) => "out",
        (Kind::App, _) => "arg",
        (Kind::Delim { .. }, _) => "in",
        (_, 1) => "1",
        _ => "2",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;
    use crate::translate::translate;

    #[test]
    fn every_wire_is_drawn_once() {
        let net = translate(&parse(r"(\x. x x) y").unwrap()).unwrap();
        let dot = to_dot(&net);
        // root, application, abstraction, fan, inner application, free variable.
        assert_eq!(dot.matches("[label=").count(), 6);
        // Total ports are 1 + 3 + 3 + 3 + 3 + 1 = 14, so there are 7 wires.
        assert_eq!(dot.matches(" -- ").count(), 7);
        assert!(dot.contains("λx"));
    }

    #[test]
    fn odd_names_and_loose_ports_still_give_a_graph() {
        assert_eq!(to_dot(&Net::new()).matches("[label=").count(), 1);
        let mut net = Net::new();
        let name = net.intern("a\"b\\");
        let free = net.add(Kind::Free { name });
        net.link(net.root().principal(), free.principal());
        assert!(to_dot(&net).contains(r#"[label="a\"b\\"];"#));
    }
}
