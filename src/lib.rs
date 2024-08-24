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
    multi::{many0, many0_count, many1, separated_list0},
    sequence::{delimited, pair, preceded, terminated},
    IResult, Parser,
};

mod string;

#[derive(Clone, Debug)]
pub enum Value {
    Bool(bool),
    Number(f32),
    Str(String),
    List(Vec<Value>),
    Map(HashMap<String, Value>),
}

#[derive(Debug)]
enum Expr {
    Bool(bool),
    Number(f32),
    Ident(String),
    Str(String),
    List(Vec<Expr>),
    Map(HashMap<String, Expr>),
}

impl Expr {
    fn eval(self, env: &HashMap<String, Value>) -> Value {
        match self {
            Expr::Bool(b) => Value::Bool(b),
            Expr::Ident(id) => {
                let Some(v) = env.get(&id) else {
                    panic!("unknown identifier {id}");
                };
                v.clone()
            }
            Expr::Number(f) => Value::Number(f),
            Expr::Str(s) => Value::Str(s),
            Expr::List(l) => {
                Value::List(l.into_iter().map(|e| e.eval(env)).collect())
            }
            Expr::Map(m) => Value::Map(
                m.into_iter().map(|(k, v)| (k, v.eval(env))).collect(),
            ),
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

fn number(s: &str) -> IResult<&str, Expr> {
    nom::number::complete::float(s).map(|(s, f)| (s, Expr::Number(f)))
}

fn string(s: &str) -> IResult<&str, Expr> {
    string::string(s).map(|(s, v)| (s, Expr::Str(v)))
}

fn list(s: &str) -> IResult<&str, Expr> {
    delimited(
        char('['),
        separated_list0((tag(","), opt(multispace0)), expr),
        char(']'),
    )
    .parse(s)
    .map(|(r, v)| (r, Expr::List(v)))
}

fn map(s: &str) -> IResult<&str, Expr> {
    delimited(
        char('{'),
        separated_list0(
            (tag(","), opt(multispace0)),
            (ident, (tag(":"), opt(multispace0)), expr),
        ),
        char('}'),
    )
    .parse(s)
    .map(|(r, v)| {
        (
            r,
            Expr::Map(
                v.into_iter()
                    .map(|(id, _colon, expr)| {
                        (id.try_into_ident().unwrap(), expr)
                    })
                    .collect(),
            ),
        )
    })
}

/// expr := float | int | bool | string | ident | list | map
fn expr(s: &str) -> IResult<&str, Expr> {
    alt((number, bool, string, ident, list, map)).parse(s)
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
    fn debug_map() {
        map("{x: 1, y: 2, z: 3}").unwrap();
    }

    #[test]
    fn debug_list() {
        list("[1, 2, 3]").unwrap();
    }

    #[test]
    fn main() {
        let s = read_to_string("testfiles/test.fig").unwrap();
        let ast = parse(&s).unwrap();

        let mut fig = Fig::new();
        fig.eval(ast).unwrap();

        dbg!(fig);
    }
}
