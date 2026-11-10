//! Scripts: statements that define names or ask for a term to be evaluated.
//!
//! ```text
//! statement ::= name "=" term | term
//! ```
//!
//! A definition gives a name to a term. The name stands for that term in
//! every statement that follows, wherever no binder captures it. Definitions
//! are expanded when a term is parsed, so they cannot refer to themselves:
//! recursion needs a fixed-point combinator.

use crate::parse::{ParseError, is_name, parse_with};
use crate::term::Term;

/// One statement of a script.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    Define(String, Term),
    Evaluate(Term),
}

/// The names defined so far.
#[derive(Clone, Debug, Default)]
pub struct Definitions {
    entries: Vec<(String, Term)>,
}

impl Definitions {
    pub fn new() -> Definitions {
        Definitions::default()
    }

    pub fn get(&self, name: &str) -> Option<&Term> {
        self.entries
            .iter()
            .find(|(defined, _)| defined == name)
            .map(|(_, term)| term)
    }

    /// Defines `name`, replacing any earlier definition of it.
    pub fn define(&mut self, name: impl Into<String>, term: Term) {
        let name = name.into();
        match self
            .entries
            .iter_mut()
            .find(|(defined, _)| *defined == name)
        {
            Some(entry) => entry.1 = term,
            None => self.entries.push((name, term)),
        }
    }

    /// The definitions, in the order the names were first defined.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &Term)> {
        self.entries
            .iter()
            .map(|(name, term)| (name.as_str(), term))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Parses a term, expanding the defined names.
    pub fn parse(&self, source: &str) -> Result<Term, ParseError> {
        parse_with(source, &|name| self.get(name).cloned())
    }

    /// Parses a statement, expanding the defined names. Returns `None` for a
    /// statement that holds nothing but blanks and comments.
    pub fn statement(&self, source: &str) -> Result<Option<Statement>, ParseError> {
        let code = blank_comments(source);
        if code.trim().is_empty() {
            return Ok(None);
        }
        let Some(sign) = code.find('=') else {
            return self.parse(&code).map(Statement::Evaluate).map(Some);
        };
        let name = code[..sign].trim();
        if !is_name(name) {
            return Err(ParseError {
                offset: 0,
                message: format!("expected a name before `=`, found `{name}`"),
            });
        }
        let body = sign + 1;
        let term = self.parse(&code[body..]).map_err(|error| ParseError {
            offset: error.offset + body,
            message: error.message,
        })?;
        Ok(Some(Statement::Define(name.to_owned(), term)))
    }
}

/// Replaces every comment by spaces, which keeps all offsets intact.
fn blank_comments(source: &str) -> String {
    let mut code = String::with_capacity(source.len());
    for line in source.split_inclusive('\n') {
        match line.find("--") {
            Some(start) => {
                code.push_str(&line[..start]);
                let comment = line[start..].trim_end_matches('\n');
                code.extend(std::iter::repeat_n(' ', comment.len()));
                code.push_str(&line[start + comment.len()..]);
            }
            None => code.push_str(line),
        }
    }
    code
}

/// Splits a script into statements, each with the number of the line it
/// starts on, counting from 1.
///
/// A statement starts on a line that begins in the first column and runs over
/// the indented and empty lines that follow.
pub fn statements(script: &str) -> Vec<(usize, &str)> {
    let mut found: Vec<(usize, std::ops::Range<usize>)> = Vec::new();
    let mut offset = 0;
    for (number, line) in script.split_inclusive('\n').enumerate() {
        let end = offset + line.len();
        let continues = line.starts_with([' ', '\t']) || line.trim().is_empty();
        match found.last_mut() {
            Some((_, range)) if continues => range.end = end,
            _ => found.push((number + 1, offset..end)),
        }
        offset = end;
    }
    found
        .into_iter()
        .map(|(line, range)| (line, &script[range]))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    #[test]
    fn definitions_expand_in_later_statements() {
        let mut definitions = Definitions::new();
        let Ok(Some(Statement::Define(name, term))) = definitions.statement(r"id = \x. x") else {
            panic!("expected a definition");
        };
        assert_eq!(name, "id");
        definitions.define(name, term);
        assert_eq!(
            definitions.statement("id id"),
            Ok(Some(Statement::Evaluate(
                parse(r"(\x. x) (\x. x)").unwrap()
            )))
        );
    }

    #[test]
    fn redefinition_replaces_and_keeps_the_order() {
        let mut definitions = Definitions::new();
        definitions.define("a", Term::church(1));
        definitions.define("b", Term::church(2));
        definitions.define("a", Term::church(3));
        let names: Vec<&str> = definitions.iter().map(|(name, _)| name).collect();
        assert_eq!(names, ["a", "b"]);
        assert_eq!(definitions.get("a"), Some(&Term::church(3)));
        assert_eq!(definitions.len(), 2);
    }

    #[test]
    fn comments_and_blanks_are_not_statements() {
        let definitions = Definitions::new();
        assert_eq!(definitions.statement("   "), Ok(None));
        assert_eq!(definitions.statement("-- x = y"), Ok(None));
        assert_eq!(
            definitions.statement("x -- = y"),
            Ok(Some(Statement::Evaluate(Term::free("x"))))
        );
    }

    #[test]
    fn errors_point_into_the_statement() {
        let definitions = Definitions::new();
        let error = definitions.statement("two = (x").unwrap_err();
        assert_eq!(error.offset, 8);
        let error = definitions.statement("-- note\ntwo = )").unwrap_err();
        assert_eq!(error.offset, 14);
        assert!(definitions.statement("a b = c").is_err());
        assert!(definitions.statement("= c").is_err());
    }

    #[test]
    fn statements_continue_on_indented_lines() {
        let script =
            "-- prelude\nid = \\x. x\n\ntwo = \\f x.\n  f (f x)\n\n  -- still two\ntwo id\n";
        let found = statements(script);
        let lines: Vec<usize> = found.iter().map(|(line, _)| *line).collect();
        assert_eq!(lines, [1, 2, 4, 8]);
        assert_eq!(found[1].1, "id = \\x. x\n\n");
        assert_eq!(found[2].1, "two = \\f x.\n  f (f x)\n\n  -- still two\n");
        assert_eq!(found[3].1, "two id\n");
        assert!(statements("").is_empty());
    }
}
