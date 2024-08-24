# fig
A simple configuration language

## Syntax
Fig currently supports the following expression types:

| Type   | Examples              |
|--------|-----------------------|
| Bool   | `true`, `false`       |
| Number | `123`, `45.6`, `7e8`  |
| Ident  | `x`, `x2`, `an_ident` |
| Str    | "Hello, world"        |
| List   | [1, 2, 3]             |
| Map    | {x: 1, y: 2}          |

with a limited form of evaluation that just looks up `Ident` expressions in the
global environment. Watch out for spaces! `[ 1, 2, 3]` is currently invalid, for
example, but `[1,2,3]` should be fine.

## Usage
The intended usage of Fig is through the `Fig::parse` function. This will parse
a `&str` as a Fig program and return a `Fig` struct, which is currently a thin
wrapper around a `HashMap<String, Value>`. You'll likely want to do some type
checking on the `Value`s and assemble some kind of `Config` struct. For example:

``` rust
use fig::Fig;

struct Config {
    x: usize,
}

impl From<Fig> for Config {
    fn from(value: Fig) -> Self {
        Self {
            x: *value.variables.get("x").unwrap().as_number().unwrap() as usize,
        }
    }
}

#[test]
fn main() {
    let s = "
        let x = 1;
    ";
    let f = Fig::parse(s).unwrap();
    let conf = Config::from(f);
}
```
