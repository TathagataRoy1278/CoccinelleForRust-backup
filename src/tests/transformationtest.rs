#![allow(dead_code)]
use std::fs;

use crate::{
    engine::transformation,
    parsing_rs::{ast_rs::Rnode, parse_rs::processrs_old}, parsing_cocci::parse_cocci::processcocci,
};

pub struct TransformTest<'a> {
    pub prefix: &'a str,
}
impl<'a> TransformTest<'a> {
    fn transformfile(&self, coccifile: &str, rsfile: &str) -> Rnode {
        let patchstring = fs::read_to_string(format!("{}{}", &self.prefix, coccifile))
            .expect("This shouldnt be empty.");
        let rustcode = fs::read_to_string(format!("{}{}", &self.prefix, rsfile))
            .expect("This shouldnt be empty.");

        let (rules, _, _) = processcocci(&patchstring);
        let transformedcode = transformation::transformfile(&rules, rustcode).ok().unwrap();
        let rnode = processrs_old(&transformedcode.getstring()).unwrap();
        return rnode;
    }

    pub fn testtransformation(&self, coccifile: &str, rsfile: &str, expectedfile: &str) -> bool {
        let out = self.transformfile(coccifile, rsfile);
        println!("Outfile:- {}", out.getstring());
        let expected = fs::read_to_string(format!("{}{}", &self.prefix, expectedfile))
            .expect("This should not be empty.");
        let rnode = processrs_old(&expected).unwrap();
        return rnode.equals(&out);
    }
}
