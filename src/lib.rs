//! A simple configuration language

#![allow(unused)]

use std::{
    any::Any, collections::HashMap, error::Error, fs::read_to_string,
    hash::Hash,
};

use nom::{
    branch::alt,
    bytes::complete::{is_not, tag},
    character::complete::{
        alpha1, alphanumeric1, char, digit1, multispace0, one_of, space0,
        space1,
    },
    combinator::{opt, recognize, value},
    multi::{many0, many0_count, many1, separated_list0},
    sequence::{delimited, pair, preceded, terminated},
    IResult, Parser,
};

mod string;

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f32),
    Str(String),
    List(Vec<Value>),
    Map(HashMap<String, Value>),
}

macro_rules! try_from {
    ($($out:ty => $method:ident$(,)*)*) => {
        $(impl TryFrom<Value> for $out {
            type Error = FigError;

            fn try_from(value: Value) -> Result<Self, Self::Error> {
                value.$method().map_err(|_| FigError::Conversion)
            }
        })*
    }
}

try_from! {
    bool => try_into_bool,
    i64 => try_into_int,
    f32 => try_into_float,
    String => try_into_str,
    HashMap<String, Value> => try_into_map,
}

impl<T: TryFrom<Value>> TryFrom<Value> for Vec<T> {
    type Error = FigError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        value
            .try_into_list()
            .map_err(|_| FigError::Conversion)?
            .into_iter()
            .map(|v| T::try_from(v).map_err(|_| FigError::Conversion))
            .collect()
    }
}

impl Value {
    pub fn as_bool(&self) -> Option<&bool> {
        if let Self::Bool(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_float(&self) -> Option<&f32> {
        if let Self::Float(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_str(&self) -> Option<&String> {
        if let Self::Str(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_list(&self) -> Option<&Vec<Value>> {
        if let Self::List(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_map(&self) -> Option<&HashMap<String, Value>> {
        if let Self::Map(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn try_into_bool(self) -> Result<bool, Self> {
        if let Self::Bool(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn try_into_float(self) -> Result<f32, Self> {
        if let Self::Float(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn try_into_str(self) -> Result<String, Self> {
        if let Self::Str(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn try_into_list(self) -> Result<Vec<Value>, Self> {
        if let Self::List(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn try_into_map(self) -> Result<HashMap<String, Value>, Self> {
        if let Self::Map(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn as_int(&self) -> Option<&i64> {
        if let Self::Int(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the value is [`Int`].
    ///
    /// [`Int`]: Value::Int
    #[must_use]
    pub fn is_int(&self) -> bool {
        matches!(self, Self::Int(..))
    }

    /// Returns `true` if the value is [`Float`].
    ///
    /// [`Float`]: Value::Float
    #[must_use]
    pub fn is_float(&self) -> bool {
        matches!(self, Self::Float(..))
    }

    pub fn try_into_int(self) -> Result<i64, Self> {
        if let Self::Int(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    /// Returns `true` if the value is [`Nil`].
    ///
    /// [`Nil`]: Value::Nil
    #[must_use]
    pub fn is_nil(&self) -> bool {
        matches!(self, Self::Nil)
    }
}

#[derive(Debug)]
enum Expr {
    Nil,
    Bool(bool),
    Int(i64),
    Number(f32),
    Ident(String),
    Str(String),
    List(Vec<Expr>),
    Map(HashMap<String, Expr>),
    Unop(UnOp, Box<Expr>),
    Binop(Box<Expr>, BinOp, Box<Expr>),
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
            Expr::Number(f) => Value::Float(f),
            Expr::Str(s) => Value::Str(s),
            Expr::List(l) => {
                Value::List(l.into_iter().map(|e| e.eval(env)).collect())
            }
            Expr::Map(m) => Value::Map(
                m.into_iter().map(|(k, v)| (k, v.eval(env))).collect(),
            ),
            Expr::Int(i) => Value::Int(i),
            Expr::Binop(e1, op, e2) => {
                let v1 = e1.eval(env);
                let v2 = e2.eval(env);
                match op {
                    BinOp::BitOr => {
                        if !v1.is_int() || !v2.is_int() {
                            panic!("invalid binary operator | for non-int");
                        }
                        Value::Int(
                            *v1.as_int().unwrap() | *v2.as_int().unwrap(),
                        )
                    }
                    BinOp::BitLeft => {
                        if !v1.is_int() || !v2.is_int() {
                            panic!("invalid binary operator | for non-int");
                        }
                        Value::Int(
                            *v1.as_int().unwrap() << *v2.as_int().unwrap(),
                        )
                    }
                }
            }
            Expr::Unop(op, e) => {
                let v = e.eval(env);
                match op {
                    UnOp::BitNot => {
                        if !v.is_int() {
                            panic!("invalid unary operator ! for non-int");
                        }
                        Value::Int(!*v.as_int().unwrap())
                    }
                }
            }
            Expr::Nil => Value::Nil,
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

fn nil(s: &str) -> IResult<&str, Expr> {
    tag("nil").parse(s).map(|(s, v)| (s, Expr::Nil))
}

fn bool(s: &str) -> IResult<&str, Expr> {
    alt((tag("true"), tag("false")))
        .parse(s)
        .map(|(s, v)| (s, Expr::Bool(v.parse().unwrap())))
}

fn number(s: &str) -> IResult<&str, Expr> {
    nom::number::complete::recognize_float(s).map(|(s, f)| {
        (
            s,
            match f.parse::<i64>() {
                Ok(i) => Expr::Int(i),
                Err(_) => Expr::Number(f.parse().unwrap()),
            },
        )
    })
}

fn string(s: &str) -> IResult<&str, Expr> {
    string::string(s).map(|(s, v)| (s, Expr::Str(v)))
}

/// This one is a little more complicated than I thought to handle whitespace. I
/// guess it's basically like a Rust macro with $(,)* since there's an
/// additional optional , and whitespace between the final expr and the closing
/// right bracket.
///
/// list := "[" \s* (expr,\s*)* ","? \s* "]"
fn list(s: &str) -> IResult<&str, Expr> {
    delimited(
        (char('['), multispace0),
        separated_list0((tag(","), multispace0), genexpr),
        (opt(recognize(char(','))), multispace0, char(']')),
    )
    .parse(s)
    .map(|(r, v)| (r, Expr::List(v)))
}

fn map(s: &str) -> IResult<&str, Expr> {
    delimited(
        char('{'),
        separated_list0(
            (tag(","), opt(multispace0)),
            (ident, (tag(":"), opt(multispace0)), genexpr),
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

#[derive(Debug)]
enum UnOp {
    BitNot,
}

fn unop(s: &str) -> IResult<&str, UnOp> {
    alt((tag("!"),)).parse(s).map(|(r, s)| (r, UnOp::BitNot))
}

/// unexpr := unop expr
fn unexpr(s: &str) -> IResult<&str, Expr> {
    (terminated(unop, multispace0), terminated(expr, multispace0))
        .parse(s)
        .map(|(r, (op, e2))| (r, Expr::Unop(op, Box::new(e2))))
}

#[derive(Debug)]
enum BinOp {
    BitOr,
    BitLeft,
}

fn binop(s: &str) -> IResult<&str, BinOp> {
    alt((tag("<<"), tag("|"))).parse(s).map(|(r, s)| {
        (
            r,
            match s {
                "<<" => BinOp::BitLeft,
                "|" => BinOp::BitOr,
                _ => unreachable!(),
            },
        )
    })
}

/// binexpr := expr binop expr
fn binexpr(s: &str) -> IResult<&str, Expr> {
    (
        terminated(expr, multispace0),
        terminated(binop, multispace0),
        terminated(expr, multispace0),
    )
        .parse(s)
        .map(|(r, (e1, op, e2))| {
            (r, Expr::Binop(Box::new(e1), op, Box::new(e2)))
        })
}

/// expr := float | int | bool | string | ident | list | map
fn expr(s: &str) -> IResult<&str, Expr> {
    alt((number, bool, nil, string, ident, list, map)).parse(s)
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

fn genexpr(s: &str) -> IResult<&str, Expr> {
    alt((unexpr, binexpr, expr)).parse(s)
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
        genexpr,
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
    Comment,
}

fn comment(i: &str) -> IResult<&str, Stmt> {
    value((), pair(char('#'), is_not("\n\r")))
        .parse(i)
        .map(|(r, s)| (r, Stmt::Comment))
}

/// stmt := assign
fn stmt(s: &str) -> IResult<&str, Stmt> {
    alt((assign, comment)).parse(s)
}

/// program := stmt*
fn program(s: &str) -> IResult<&str, Ast> {
    many0(delimited(multispace0, stmt, multispace0))
        .parse(s)
        .map(|(s, t)| (s, Ast(t)))
}

#[derive(Debug)]
pub struct Ast(Vec<Stmt>);

#[derive(Debug)]
pub enum FigError {
    NomIncomplete,
    NomError(nom::error::ErrorKind),
    TrailingInput(String),
    Conversion,
}

impl std::fmt::Display for FigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl Error for FigError {}

impl From<nom::Err<nom::error::Error<&str>>> for FigError {
    fn from(value: nom::Err<nom::error::Error<&str>>) -> Self {
        match value {
            nom::Err::Incomplete(_) => Self::NomIncomplete,
            nom::Err::Error(e) => Self::NomError(e.code),
            nom::Err::Failure(e) => Self::NomError(e.code),
        }
    }
}

fn parse(s: &str) -> Result<Ast, FigError> {
    let (rest, tree) = program(s)?;
    if !rest.is_empty() {
        return Err(FigError::TrailingInput(rest.to_owned()));
    }
    Ok(tree)
}

#[derive(Debug)]
pub struct Fig {
    pub variables: HashMap<String, Value>,
}

impl Fig {
    pub fn new() -> Self {
        Self { variables: HashMap::new() }
    }

    fn eval(&mut self, ast: Ast) -> Result<(), FigError> {
        for stmt in ast.0 {
            match stmt {
                Stmt::Assign((id, expr)) => {
                    let val = expr.eval(&self.variables);
                    self.variables.insert(id.to_owned(), val);
                }
                Stmt::Comment => {}
            }
        }
        Ok(())
    }

    pub fn parse(&mut self, s: &str) -> Result<(), FigError> {
        let ast = parse(s)?;
        self.eval(ast)?;
        Ok(())
    }
}

impl Default for Fig {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[allow(clippy::single_element_loop)]
mod tests {
    use super::*;

    #[test]
    fn binexprs() {
        for b in ["MODKEY | ShiftMask"] {
            binexpr(b).unwrap();
        }
    }

    #[test]
    fn maps() {
        for m in ["{x: 1, y: 2, z: 3}"] {
            map(m).unwrap();
        }
    }

    #[test]
    fn lists() {
        for t in ["[1, 2, 3]", "[1,2,3]", "[\n1,\n2,\n3,\n]"] {
            list(t).unwrap();
        }
    }

    #[test]
    fn assigns() {
        for a in ["let key = MODKEY | ShiftMask;"] {
            assign(a).unwrap();
        }
    }

    #[test]
    fn vec_from_list() {
        for list in [
            //
            Value::List(vec![
                Value::Str("hello".into()),
                Value::Str("world".into()),
            ]),
        ] {
            let _: Vec<String> = list.try_into().unwrap();
        }
    }

    #[test]
    fn main() {
        let s = read_to_string("testfiles/test.fig").unwrap();
        let ast = parse(&s).unwrap();

        let mut fig = Fig::new();
        fig.eval(ast).unwrap();

        assert!(fig.variables["XK_d"].is_int());
        assert!(fig.variables["float"].is_float());

        assert_eq!(*fig.variables["key"].as_int().unwrap(), 64 | 1);
        assert_eq!(*fig.variables["x"].as_int().unwrap(), 1 << 3);
        assert_eq!(*fig.variables["y"].as_int().unwrap(), !0);

        assert_eq!(fig.variables["nothing"], Value::Nil);
    }
}
