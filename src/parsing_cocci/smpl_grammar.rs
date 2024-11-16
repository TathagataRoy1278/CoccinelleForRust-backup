pub type ModType = (String, Vec<usize>);
pub type RuleInfo<'a> = &'a str;//rulename as of now
pub type RuleType<'a> = (RuleInfo<'a>, Metavars<'a>, ModType);
pub type Metavar<'a> = (&'a str, Vec<&'a str>);
pub type Metavars<'a> = Vec<Metavar<'a>>;

pub fn make_metavar<'a>(t: &'a str, def: Vec<&'a str>) -> Metavar<'a> {
    return (t, def);
}

pub fn add_metavar<'a>(mut mvars: Metavars<'a>, t: &'a str, def: Vec<&'a str>) -> Metavars<'a> {
    mvars.push((t, def));
    return mvars;
}
