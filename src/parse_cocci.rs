#![feature(try_blocks)]

use std::{vec, io::Lines};

use parser::SyntaxKind;

use crate::{
    syntaxerror,
    util::{tuple_of_2, tuple_of_3},
    wrap::{wrap_root, Rnode},
};

type Tag = SyntaxKind;

enum dep {
    NoDep,
    FailDep,
    Dep(String),
    AndDep(Box<(dep, dep)>),
    OrDep(Box<(dep, dep)>),
    AntiDep(Box<dep>),
}
struct mvar {
    ruleid: usize,
    varname: String,
}

impl mvar {
    pub fn new(ruleid: usize, var: &str) -> mvar {
        mvar {
            ruleid: ruleid,//ruleid is because the array of mvars will be
            //put inside a rule data structure
            varname: var.to_string(),
        }
    }
}

struct patch{
    minus: Rnode,
    plus: Rnode
}

struct rule {
    name: String,
    dependson: dep,
    expmetavars: Vec<String>,
    idmetavars: Vec<String>,
    patch: patch//index for the patch vector
}

fn getdep(rules: &Vec<rule>, lino: usize, dep: &mut Rnode) -> dep {
    let node = &dep.astnode;
    match node.kind() {
        Tag::PREFIX_EXPR => {
            //for NOT depends
            let [cond, expr] = tuple_of_2(&mut dep.children_with_tokens);
            match cond.kind() {
                Tag::BANG => dep::AntiDep(Box::new(getdep(rules, lino, expr))),
                _ => syntaxerror!(lino, "Dependance must be a boolean expression")
            }
        }
        Tag::BIN_EXPR => {
            let [lhs, cond, rhs] = tuple_of_3(&mut dep.children_with_tokens);
            match cond.kind() {
                Tag::AMP2 => {
                    dep::AndDep(Box::new((
                        getdep(rules, lino, lhs),
                        getdep(rules, lino, rhs),
                    )))
                }
                Tag::PIPE2 => {
                    dep::OrDep(Box::new((
                        getdep(rules, lino, lhs),
                        getdep(rules, lino, rhs),
                    )))
                }
                _ => syntaxerror!(lino, "Dependance must be a boolean expression"),
            }
        }
        Tag::PATH_EXPR => {
            let name = dep.astnode.to_string();
            if rules.iter().any(|x| x.name == name) {
                dep::Dep(name)
            } else {
                syntaxerror!(lino, "no such Rule", name)
            }
        }
        Tag::PAREN_EXPR => {
            let expr = &mut dep.children_with_tokens[1];
            getdep(rules, lino, expr)
        }
        _ => syntaxerror!(lino, "Malformed Rule", dep.astnode.to_string())
    }
}

fn get_blxpr(contents: &str) -> Rnode {
    wrap_root(contents)
        .children_with_tokens
        .swap_remove(0) //Fn
        .children_with_tokens
        .swap_remove(4) //BlockExpr
}

fn get_blxpr_arb(contents: &str) -> Rnode {
    let root = wrap_root(contents);
    for mut child in root.children_with_tokens{
        if child.kind()==Tag::FN{
            return child.children_with_tokens.swap_remove(4)//BlockExpr
        }
    }
    panic!("contents does not have a function")
}

fn get_expr(contents: &str) -> Rnode {
    //assumes that a
    //binary expression exists
    println!("contents - {contents}");

    get_blxpr(contents) //BlockExpr
        .children_with_tokens
        .swap_remove(0) //StmtList
        .children_with_tokens
        .swap_remove(2) //TailExpr
}

impl rule {
    //We may need to keep a track of rules?
    pub fn new(name: String, patch: patch) -> rule {
        rule {
            name: name,
            dependson: dep::NoDep,
            expmetavars: vec![],
            idmetavars: vec![],
            patch: patch
        }
    }
}

fn getdependson(rules: &Vec<rule>, rule: &str, lino: usize) -> dep{
    //rule is trimmed
    let fnstr = format!("fn {}_plus {{ {} }}", "coccifn", rule);
    getdep(rules, lino, &mut get_expr(fnstr.as_str()))
}

fn handlemetavars(
    ruleid: usize,
    idmetavars: &mut Vec<mvar>,
    exmetavars: &mut Vec<mvar>,
    line: String,
) {
    //rule here is usize because this does not represent the
    //name of the rule but the index at which it was encountered
    let mut tokens = line.split(&[',', ' ', ';'][..]);
    match tokens.next().unwrap().trim() {
        //unwrap because there must atleast be a "" in a line
        "expression" => {
            for var in tokens {
                //does not check for ; at the end of the line
                //TODO
                let var = var.trim();
                if var != "" {
                    exmetavars.push(mvar::new(ruleid, var));
                }
            }
        }
        "identifier" => {
            //can expressions have the same name as identifiers?
            //Would it not be better to create two seperate lists
            //for ident and exp metavariables?
            for var in tokens {
                //does not check for ; at the end of the line
                //TODO
                let var = var.trim();
                if var != "" {
                    idmetavars.push(mvar::new(ruleid, var));
                }
            }
        }
        _ => {}
    }
}

fn handlerules(rules: &Vec<rule>, chars: Vec<char>, ind:usize, lino: usize) -> (String, dep) {
    let decl: String = chars[1..chars.len() - 1].iter().collect();
    let mut tokens = decl.trim().split(" ");
    let currrulename = if let Some(currrulename) = tokens.next() {
        String::from(currrulename) //converted &str to String,
                               //because rule should own its name
    } else {
        format!("rule{lino}")
    }; //if currrulename does not exist

    let sword = tokens.next();
    let tword = tokens.next();

    let depends = 
    match (sword, tword) {
        (Some("depends"), Some("on")) => {
            let booleanexp: String = tokens.collect();
            getdependson(rules, String::from(booleanexp).trim(), lino)
        }
        (None, None) => { dep::NoDep }
        _ => syntaxerror!(lino, "")
    };

    (currrulename, depends)
}

fn get_logilines(mut lino: usize, node: &mut Rnode){
    if node.kind() == Tag::LITERAL{
        return;   
    }
    for child in &mut node.children_with_tokens{
        let mut end = 0;
        let text = child.astnode.to_string();
        if text.matches('\n').count() == 0{//for single line tokens, set them as so
            child.wrapper.set_logilines(lino, lino);
            continue;
        }

        //if there is a block, there can be either
        //a whitespace block or not

        //if multiline whitespace block, just increment by 1
        if child.kind() == Tag::WHITESPACE{
            end = 1;
        }
        else {
            //else if it is a block cal
            let lines= text.lines();
            for line in lines{
                if line.trim().len() != 0{
                    end+=1;
                }
            }
            end -= 1;
        }
        child.wrapper.set_logilines(lino, lino + end);
        
        get_logilines(lino, child);
        lino+=end;
    }

}

fn getpatch(plusparsed: &str, minusparsed: &str) -> patch{
    patch{
        plus: get_blxpr_arb(plusparsed),
        minus: get_blxpr_arb(minusparsed)
    }
    
    
}

pub fn processcocci(contents: &str) {
    let lines: Vec<String> = contents.lines().map(String::from).collect();
    let mut inmetadec = false; //checks if in metavar declaration
    let mut lino = 1; //stored line numbers
                      //mutable because I supply it with modifier statements

    let mut plusparsed = String::from("\n");
    let mut minusparsed = String::from("\n");

    let mut rules: Vec<rule> = vec![]; //list of rule headers in cocci file
    let mut patches: Vec<patch> = vec![];//list of associated patches
    
    let mut idmetavars: Vec<mvar> = vec![];//tmp
    let mut exmetavars: Vec<mvar> = vec![];//tmp

    let mut currrulename = String::from("");
    let mut currruleid = 0;
    let mut currdepends = dep::NoDep;
    for line in lines {
        let chars: Vec<char> = line.trim().chars().collect();
        let firstchar = chars.get(0);
        let lastchar = chars.last();
        
        match (firstchar, lastchar, inmetadec) {
            (Some('@'), Some('@'), false) => {
                //starting of @@ block
                //iter and collect converts from [char] to String

                if currrulename != "" {
                    plusparsed.push_str("}\n");
                    minusparsed.push_str("}\n");

                    let currpatch = getpatch(plusparsed.as_str(), minusparsed.as_str());
                    let rule = rule{
                        name: currrulename,
                        dependson: currdepends,
                        expmetavars: exmetavars.into_iter().map(|x| x.varname).collect(),
                        idmetavars: idmetavars.into_iter().map(|x| x.varname).collect(),
                        patch: currpatch
                    };
                    exmetavars = vec![];
                    idmetavars = vec![];
                    rules.push(rule);
                    
                    currruleid+=1;
                }

                (currrulename, currdepends) = handlerules(&mut rules, chars, currruleid, lino);
                //(get_blxpr(plusfn.as_str()), get_blxpr(minusfn.as_str()));
                inmetadec = true;
            }
            (Some('@'), Some('@'), true) => {
                plusparsed.push_str(format!("fn {currrulename}_plus() {{\n").as_str());
                minusparsed.push_str(format!("fn {currrulename}_minus() {{\n").as_str());
                inmetadec = false;
            }
            (Some('+'), _, false) => {
                plusparsed.push_str(line.as_str());
                plusparsed.push('\n');
                minusparsed.push('\n');
            }
            (Some('-'), _, false) => {
                minusparsed.push_str(line.as_str());
                minusparsed.push('\n');
                plusparsed.push('\n');
            }
            (_, _, false) => {
                plusparsed.push_str(line.as_str());
                plusparsed.push('\n');

                minusparsed.push_str(line.as_str());
                minusparsed.push('\n');
            }
            (_, _, true) => {
                handlemetavars(currruleid, &mut idmetavars, &mut exmetavars, line);
                plusparsed.push('\n');
                minusparsed.push('\n')
            }
        }
        lino += 1;
    }
    if inmetadec {
        syntaxerror!(lino, "Unclosed metavariable declaration block")
    }
    if currrulename != "" {
        plusparsed.push('}');
        minusparsed.push('}');
    }

    println!("{minusparsed}");
    let mut root = wrap_root(
        &minusparsed
    );

    get_logilines(0, &mut root);
    
}
