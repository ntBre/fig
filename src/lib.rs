//! A simple configuration language

#![allow(unused)]

use std::{collections::HashMap, error::Error, fs::read_to_string, hash::Hash};

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{
        alpha1, alphanumeric1, char, digit1, multispace0, one_of, space0,
        space1,
    },
    combinator::{opt, recognize},
    multi::{many0, many0_count, many1},
    sequence::{delimited, pair, preceded, terminated},
    IResult, Parser,
};

mod string;

#[derive(Clone, Debug)]
pub enum Value {
    Bool(bool),
    Float(f32),
    Int(i64),
    Str(String),
}

#[derive(Debug)]
enum Expr {
    Bool(bool),
    Float(f32),
    Int(i64),
    Ident(String),
    Str(String),
}

impl Expr {
    fn eval(self, env: &HashMap<String, Value>) -> Value {
        match self {
            Expr::Bool(b) => Value::Bool(b),
            Expr::Int(i) => Value::Int(i),
            Expr::Ident(id) => {
                let Some(v) = env.get(&id) else {
                    panic!("unknown identifier {id}");
                };
                v.clone()
            }
            Expr::Float(f) => Value::Float(f),
            Expr::Str(s) => Value::Str(s),
        }
    }

    fn try_into_ident(self) -> Result<String, Self> {
        if let Self::Ident(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }
}

fn bool(s: &str) -> IResult<&str, Expr> {
    alt((tag("true"), tag("false")))
        .parse(s)
        .map(|(s, v)| (s, Expr::Bool(v.parse().unwrap())))
}

fn float(s: &str) -> IResult<&str, Expr> {
    nom::number::complete::float(s).map(|(s, f)| (s, Expr::Float(f)))
}

fn int(s: &str) -> IResult<&str, Expr> {
    digit1(s).map(|(s, v)| (s, Expr::Int(v.parse().unwrap())))
}

fn string(s: &str) -> IResult<&str, Expr> {
    string::string(s).map(|(s, v)| (s, Expr::Str(v)))
}

/// expr := float | int | bool | string | ident
fn expr(s: &str) -> IResult<&str, Expr> {
    alt((float, int, bool, string, ident)).parse(s)
}

/// ident := [A-Za-z][A-Za-z_0-9]*
fn ident(s: &str) -> IResult<&str, Expr> {
    recognize(pair(
        alt((alpha1, tag("_"))),
        many0_count(alt((alphanumeric1, tag("_")))),
    ))
    .parse(s)
    .map(|(s, id)| (s, Expr::Ident(id.to_string())))
}

/// assign := "let" ident "=" expr ";"
fn assign(s: &str) -> IResult<&str, Stmt> {
    (
        tag("let"),
        space1,
        ident,
        space0,
        tag("="),
        space0,
        expr,
        space0,
        tag(";"),
    )
        .parse(s)
        .map(|(s, (_let, _, ident, _, _eq, _, expr, _, _sc))| {
            (
                s,
                Stmt::Assign((ident.try_into_ident().unwrap().clone(), expr)),
            )
        })
}

#[derive(Debug)]
enum Stmt {
    Assign((String, Expr)),
}

/// stmt := assign
fn stmt(s: &str) -> IResult<&str, Stmt> {
    alt((assign,)).parse(s)
}

/// program := stmt*
fn program(s: &str) -> IResult<&str, Ast> {
    many0(delimited(multispace0, stmt, multispace0))
        .parse(s)
        .map(|(s, t)| (s, Ast(t)))
}

#[derive(Debug)]
pub struct Ast(Vec<Stmt>);

type FigError<'a> = Box<dyn Error + 'a>;

fn parse(s: &str) -> Result<Ast, FigError> {
    let (rest, tree) = program(s)?;
    if !rest.is_empty() {
        return Err(format!("trailing input: `{rest}`").into());
    }
    Ok(tree)
}

#[derive(Debug)]
pub struct Fig {
    variables: HashMap<String, Value>,
}

impl Fig {
    pub fn new() -> Self {
        Self { variables: HashMap::new() }
    }

    pub fn eval(&mut self, ast: Ast) -> Result<(), FigError> {
        for stmt in ast.0 {
            match stmt {
                Stmt::Assign((id, expr)) => {
                    let val = expr.eval(&self.variables);
                    self.variables.insert(id.to_owned(), val);
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
