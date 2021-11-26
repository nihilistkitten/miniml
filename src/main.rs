use miniml::to_expn;
fn main() {
    if let Err(e) = to_expn("4+") {
        println!("{}", e);
    }
}
