#![allow(dead_code)]
use std::fs;

use clap::Parser;

use crate::{
    commons::util::get_rcode,
    engine::transformation,
    interface::interface::CoccinelleForRust,
    parsing_cocci::parse_cocci::processcocci,
    parsing_rs::{ast_rs::Rcode, parse_rs::processrs},
};

pub struct TransformTest<'a> {
    pub prefix: &'a str,
}
impl<'a> TransformTest<'a> {
    fn transformfile(&self, coccifile: &str, rsfile: &str) -> Rcode {
        let patchstring = fs::read_to_string(format!("{}{}", &self.prefix, coccifile))
            .expect("This shouldnt be empty.");
        let rustcode = fs::read_to_string(format!("{}{}", &self.prefix, rsfile))
            .expect("This shouldnt be empty.");

        let (rules, _, _) = processcocci(&patchstring);
        let transformedcode =
            transformation::transformfile(&CoccinelleForRust::parse(), &rules, rustcode)
                .ok()
                .unwrap();
        let rnode = processrs(&get_rcode(&transformedcode)).unwrap();
        return rnode;
    }

    pub fn testtransformation(&self, coccifile: &str, rsfile: &str, expectedfile: &str) -> bool {
        let out = self.transformfile(coccifile, rsfile);
        println!("Outfile:- {}", out.getstring());
        let expected = fs::read_to_string(format!("{}{}", &self.prefix, expectedfile))
            .expect("This should not be empty.");
        let rnode = processrs(&expected).unwrap();
        return rnode.eq(&out);
    }
}
