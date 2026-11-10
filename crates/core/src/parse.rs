//! Parser for the surface syntax.
//!
//! ```text
//! term        ::= abstraction | application
//! abstraction ::= ("λ" | "\") name+ "." term
//! application ::= atom+ abstraction?
//! atom        ::= name | numeral | "(" term ")"
//! ```
//!
//! A numeral stands for the corresponding Church numeral. `--` starts a
//! comment that runs to the end of the line.

use std::fmt;

use crate::term::Term;

/// The largest numeral literal the parser expands.
pub const MAX_NUMERAL: u64 = 10_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// Byte offset into the source where the problem was found.
    pub offset: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at offset {}", self.message, self.offset)
    }
}

impl std::error::Error for ParseError {}

/// Parses a term. Names that no binder captures become free variables.
pub fn parse(source: &str) -> Result<Term, ParseError> {
    parse_with(source, &|_| None)
}

/// Parses a term, replacing each name that no binder captures by the term
/// `definition` gives for it, if any.
pub fn parse_with(
    source: &str,
    definition: &dyn Fn(&str) -> Option<Term>,
) -> Result<Term, ParseError> {
    let mut parser = Parser {
        tokens: lex(source)?,
        position: 0,
        scope: Vec::new(),
        definition,
    };
    let term = parser.term()?;
    match parser.peek() {
        Token::End => Ok(term),
        token => Err(parser.error(format!("unexpected {token}"))),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Lambda,
    Dot,
    Open,
    Close,
    Name(String),
    Numeral(u64),
    End,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Lambda => f.write_str("`λ`"),
            Token::Dot => f.write_str("`.`"),
            Token::Open => f.write_str("`(`"),
            Token::Close => f.write_str("`)`"),
            Token::Name(name) => write!(f, "name `{name}`"),
            Token::Numeral(value) => write!(f, "numeral `{value}`"),
            Token::End => f.write_str("end of input"),
        }
    }
}

fn is_name_start(c: char) -> bool {
    (c.is_alphabetic() && c != 'λ') || c == '_'
}

fn is_name_part(c: char) -> bool {
    is_name_start(c) || c.is_numeric() || c == '\''
}

fn lex(source: &str) -> Result<Vec<(usize, Token)>, ParseError> {
    let mut tokens = Vec::new();
    let mut chars = source.char_indices().peekable();
    while let Some(&(offset, c)) = chars.peek() {
        let token = match c {
            _ if c.is_whitespace() => {
                chars.next();
                continue;
            }
            '-' if source[offset..].starts_with("--") => {
                while chars.next_if(|&(_, c)| c != '\n').is_some() {}
                continue;
            }
            'λ' | '\\' => Token::Lambda,
            '.' => Token::Dot,
            '(' => Token::Open,
            ')' => Token::Close,
            _ if c.is_ascii_digit() => {
                let mut end = offset;
                while let Some((at, c)) = chars.next_if(|&(_, c)| c.is_ascii_digit()) {
                    end = at + c.len_utf8();
                }
                let value = source[offset..end]
                    .parse()
                    .ok()
                    .filter(|&value| value <= MAX_NUMERAL)
                    .ok_or_else(|| ParseError {
                        offset,
                        message: format!("numeral is larger than {MAX_NUMERAL}"),
                    })?;
                tokens.push((offset, Token::Numeral(value)));
                continue;
            }
            _ if is_name_start(c) => {
                let mut end = offset;
                while let Some((at, c)) = chars.next_if(|&(_, c)| is_name_part(c)) {
                    end = at + c.len_utf8();
                }
                tokens.push((offset, Token::Name(source[offset..end].to_owned())));
                continue;
            }
            _ => {
                return Err(ParseError {
                    offset,
                    message: format!("unexpected character `{c}`"),
                });
            }
        };
        chars.next();
        tokens.push((offset, token));
    }
    tokens.push((source.len(), Token::End));
    Ok(tokens)
}

struct Parser<'a> {
    tokens: Vec<(usize, Token)>,
    position: usize,
    /// Names of the enclosing binders, innermost last.
    scope: Vec<String>,
    definition: &'a dyn Fn(&str) -> Option<Term>,
}

impl Parser<'_> {
    fn peek(&self) -> &Token {
        &self.tokens[self.position].1
    }

    fn advance(&mut self) -> Token {
        let token = self.tokens[self.position].1.clone();
        if token != Token::End {
            self.position += 1;
        }
        token
    }

    fn error(&self, message: String) -> ParseError {
        ParseError {
            offset: self.tokens[self.position].0,
            message,
        }
    }

    fn term(&mut self) -> Result<Term, ParseError> {
        if *self.peek() == Token::Lambda {
            self.abstraction()
        } else {
            self.application()
        }
    }

    fn abstraction(&mut self) -> Result<Term, ParseError> {
        self.advance();
        let depth = self.scope.len();
        while let Token::Name(name) = self.peek() {
            let name = name.clone();
            self.scope.push(name);
            self.advance();
        }
        if self.scope.len() == depth {
            return Err(self.error(format!("expected a binder name, found {}", self.peek())));
        }
        if *self.peek() != Token::Dot {
            return Err(self.error(format!("expected `.`, found {}", self.peek())));
        }
        self.advance();
        let body = self.term()?;
        let names = self.scope.split_off(depth);
        Ok(names
            .into_iter()
            .rev()
            .fold(body, |body, name| Term::lam(name, body)))
    }

    fn application(&mut self) -> Result<Term, ParseError> {
        let mut term = self.atom()?;
        loop {
            match self.peek() {
                Token::Name(_) | Token::Numeral(_) | Token::Open => {
                    term = Term::app(term, self.atom()?);
                }
                Token::Lambda => return Ok(Term::app(term, self.abstraction()?)),
                _ => return Ok(term),
            }
        }
    }

    fn atom(&mut self) -> Result<Term, ParseError> {
        match self.peek().clone() {
            Token::Name(name) => {
                self.advance();
                Ok(self.resolve(name))
            }
            Token::Numeral(value) => {
                self.advance();
                Ok(Term::church(value))
            }
            Token::Open => {
                self.advance();
                let term = self.term()?;
                if *self.peek() != Token::Close {
                    return Err(self.error(format!("expected `)`, found {}", self.peek())));
                }
                self.advance();
                Ok(term)
            }
            token => Err(self.error(format!("expected a term, found {token}"))),
        }
    }

    fn resolve(&self, name: String) -> Term {
        if let Some(index) = self.scope.iter().rev().position(|bound| *bound == name) {
            Term::Var(index)
        } else if let Some(term) = (self.definition)(&name) {
            term
        } else {
            Term::Free(name)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_binders_and_applications() {
        let term = parse(r"\f x. f (f x)").unwrap();
        assert_eq!(term, Term::church(2));
        assert_eq!(parse("λf. λx. f (f x)").unwrap(), term);
    }

    #[test]
    fn application_associates_to_the_left() {
        let term = parse("a b c").unwrap();
        let expected = Term::app(Term::app(Term::free("a"), Term::free("b")), Term::free("c"));
        assert_eq!(term, expected);
    }

    #[test]
    fn trailing_abstraction_needs_no_parentheses() {
        assert_eq!(parse(r"f \x. x y").unwrap(), parse(r"f (\x. x y)").unwrap());
    }

    #[test]
    fn inner_binders_shadow_outer_ones() {
        let term = parse(r"\x. \x. x").unwrap();
        assert_eq!(term, Term::lam("x", Term::lam("x", Term::Var(0))));
    }

    #[test]
    fn numerals_and_comments() {
        assert_eq!(parse("3 -- three\n").unwrap(), Term::church(3));
        assert!(parse("99999999999").is_err());
    }

    #[test]
    fn definitions_replace_unbound_names_only() {
        let id = Term::lam("x", Term::Var(0));
        let lookup = |name: &str| (name == "id").then(|| id.clone());
        assert_eq!(
            parse_with("id y", &lookup).unwrap(),
            Term::app(id.clone(), Term::free("y"))
        );
        assert_eq!(
            parse_with(r"\id. id", &lookup).unwrap(),
            Term::lam("id", Term::Var(0))
        );
    }

    #[test]
    fn printed_terms_parse_back() {
        for source in [
            r"\x. x",
            r"\f x. f (f x)",
            r"(\x. x x) (\x. x x)",
            r"\x. \y. x (\z. z y) w",
            r"(\x. \x. x) a",
        ] {
            let term = parse(source).unwrap();
            assert_eq!(parse(&term.to_string()).unwrap(), term, "{source}");
        }
    }

    #[test]
    fn reports_errors_with_offsets() {
        assert_eq!(parse("(x").unwrap_err().offset, 2);
        assert_eq!(parse(r"\. x").unwrap_err().offset, 1);
        assert_eq!(parse("x )").unwrap_err().offset, 2);
        assert_eq!(parse("x $").unwrap_err().offset, 2);
        assert!(parse("").is_err());
    }
}
