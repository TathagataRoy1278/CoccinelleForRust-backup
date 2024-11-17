pub type ModType = (String, Vec<usize>);// usize are the indices where there are ellipses
pub type RuleInfo<'a> = &'a str;//rulename as of now
pub type RuleType<'a> = (RuleInfo<'a>, Metavars<'a>, Vec<DisjElems>);
pub type Metavar<'a> = (&'a str, Vec<&'a str>);
pub type Metavars<'a> = Vec<Metavar<'a>>;

pub enum DisjElems {
    Mod(ModType),
    DisjBranches(Vec<DisjElems>)
}

// impl DisjElems {
//     fn add_elem(&mut self, elem: DisjElems) {
//         match (self, elem) {
//             (DisjElems::Mod(_), DisjElems::Mod(_)) => panic!("Not possible"),
//             (DisjElems::Mod(_), DisjElems::DisjBranches(vec)) => todo!(),
//             (DisjElems::DisjBranches(vec), DisjElems::Mod(_)) => todo!(),
//             (DisjElems::DisjBranches(vec), DisjElems::DisjBranches(vec)) => todo!(),
//         }
//     }
// }

pub fn make_metavar<'a>(t: &'a str, def: Vec<&'a str>) -> Metavar<'a> {
    return (t, def);
}

pub fn add_metavar<'a>(mut mvars: Metavars<'a>, t: &'a str, def: Vec<&'a str>) -> Metavars<'a> {
    mvars.push((t, def));
    return mvars;
}
