#[d(
    /*rwar*/
)]

fn format_macro(macro_str: &Rnode) -> Rnode {
    #[abc(/*COCCI*/)]
    let a = X;
}