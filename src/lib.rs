use lalrpop_util::lalrpop_mod;

pub mod parsing_cocci;
pub mod parsing_rs;
pub mod commons;
pub mod engine;
pub mod interface;
mod tests;
pub mod ctl;
//all these need to be make private once they are tested

lalrpop_mod!(smpl_grammar);

#[test]
fn tt() {
    smpl_grammar::SPatchParser::new().parse("test");
}