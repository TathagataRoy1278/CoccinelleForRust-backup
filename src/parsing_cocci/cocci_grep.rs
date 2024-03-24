// SPDX-License-Identifier: GPL-2.0

// The input should be in CNF, ie an outer list, representing a conjunction,
// with inner lists of words, representing disjunctions.  There is no negation.

use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use regex::Regex;

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

pub fn interpret(big_regexp : &Regex, regexps : &Vec<Regex>, file : &String) -> bool {
    let mut regexps = regexps.clone();
    let mut rlen = regexps.len();
    if let Ok(lines) = read_lines(file) {
        for line in lines {
            if let Ok(l) = line {
                if rlen == 1 && regexps[0].is_match(&l) {
                    return true
                }
                if big_regexp.is_match(&l) {
                    regexps.retain(|re| !re.is_match(&l));
                    rlen = regexps.len();
                    if rlen == 0 {
                        return true
                    }
                }
            }
        }
    }
    false
}
