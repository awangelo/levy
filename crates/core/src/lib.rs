//! Lévy-optimal reduction of the untyped λ-calculus.
//!
//! Terms are translated to Lambdascope interaction nets (van Oostrom, van de
//! Looij and Zwitserlood, 2004), reduced there with a leftmost-outermost
//! strategy, and read back as terms.

mod context;
pub mod dot;
pub mod machine;
pub mod net;
pub mod parse;
pub mod reference;
pub mod rules;
pub mod script;
pub mod term;
pub mod translate;

pub use machine::{Halt, Machine, Stats};
pub use parse::{ParseError, parse, parse_with};
pub use rules::Rule;
pub use script::{Definitions, Statement};
pub use term::Term;
