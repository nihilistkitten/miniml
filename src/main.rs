use miniml::to_expn;
fn main() {
    let res = to_expn("fn x => (x true) + (x 3)");
    match res {
        Ok(e) => println!("{}", e.infer()),
        Err(e) => println!("{}", e),
    }
}
