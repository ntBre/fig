//! A stringly-typed configuration language

use std::fs::read_to_string;

fn main() {
    let s = read_to_string("testfiles/test.fig").unwrap();
    dbg!(s);
}
