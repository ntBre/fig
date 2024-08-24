//! A stringly-typed configuration language

#![allow(unused)]

use std::{collections::HashMap, error::Error, fs::read_to_string, hash::Hash};

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, digit1, space0, space1},
    combinator::recognize,
    multi::{many0, many0_count},
    sequence::{pair, tuple},
    IResult,
};

fn int(s: &str) -> IResult<&str, &str> {
    digit1(s)
}

/// expr := int
fn expr(s: &str) -> IResult<&str, &str> {
    alt((int,))(s)
}

/// ident := [A-Za-z][A-Za-z_0-9]*
fn ident(s: &str) -> IResult<&str, &str> {
    recognize(pair(
        alt((alpha1, tag("_"))),
        many0_count(alt((alphanumeric1, tag("_")))),
    ))(s)
}

/// assign := "let" ident "=" expr ";"
fn assign(s: &str) -> IResult<&str, Stmt> {
    tuple((
        tag("let"),
        space1,
        ident,
        space0,
        tag("="),
        space0,
        expr,
        space0,
        tag(";"),
    ))(s)
    .map(|(s, (_let, _, ident, _, _eq, _, expr, _, _sc))| {
        (s, Stmt::Assign((ident, expr)))
    })
}

#[derive(Debug)]
enum Stmt<'a> {
    Assign((&'a str, &'a str)),
}

/// stmt := assign
fn stmt(s: &str) -> IResult<&str, Stmt> {
    alt((assign,))(s)
}

/// program := stmt*
fn program(s: &str) -> IResult<&str, Ast> {
    many0(stmt)(s).map(|(s, t)| (s, Ast(t)))
}

#[derive(Debug)]
pub struct Ast<'a>(Vec<Stmt<'a>>);

type FigError<'a> = Box<dyn Error + 'a>;

fn parse(s: &str) -> Result<Ast, FigError> {
    let (rest, tree) = program(s)?;
    if !rest.is_empty() {
        return Err(format!("trailing input: {rest}").into());
    }
    Ok(tree)
}

#[derive(Debug)]
pub struct Fig {
    variables: HashMap<String, String>,
}

impl Fig {
    pub fn new() -> Self {
        Self { variables: HashMap::new() }
    }

    pub fn eval(&mut self, ast: Ast) -> Result<(), FigError> {
        for stmt in ast.0 {
            match stmt {
                Stmt::Assign((id, val)) => {
                    self.variables.insert(id.to_owned(), val.to_owned());
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
    fn main() {
        let s = read_to_string("testfiles/test.fig").unwrap();
        let ast = parse(&s).unwrap();

        let mut fig = Fig::new();
        fig.eval(ast).unwrap();

        dbg!(fig);
    }
}
