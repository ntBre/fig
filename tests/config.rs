use fig::Fig;

struct Config {
    x: usize,
    y: usize,
}

impl From<Fig> for Config {
    fn from(value: Fig) -> Self {
        Self {
            x: *value.variables.get("x").unwrap().as_number().unwrap() as usize,
            y: *value.variables.get("y").unwrap().as_number().unwrap() as usize,
        }
    }
}

#[test]
fn main() {
    let s = "
        let x = 1;
        let y = 2;
    ";
    let f = Fig::parse(s).unwrap();
    let conf = Config::from(f);
    let (_x, _y) = (conf.x, conf.y);
}
