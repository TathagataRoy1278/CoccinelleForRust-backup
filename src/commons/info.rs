// SPDX-License-Identifier: GPL-2.0

#[derive(Clone, PartialEq,)]
pub struct PositionInfo {
    pub line_start: usize,
    pub line_end: usize,
    pub logical_start: usize,
    pub logical_end: usize,
    pub column: usize,
    pub offset: usize,
}

impl PositionInfo {
    pub fn new(
        line_start: usize,
        line_end: usize,
        logical_start: usize,
        logical_end: usize,
        column: usize,
        offset: usize,
    ) -> PositionInfo {
        PositionInfo {
            line_start: line_start,
            line_end: line_end,
            logical_start: logical_start,
            logical_end: logical_end,
            column: column,
            offset: offset,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ParseInfo {
    str: String,
    pub charstart: usize,
    pub charend: usize,

    pub sline: usize,
    pub eline: usize,
    column: usize,
    file: String
  }

impl ParseInfo {
    pub fn new(str: String, charstart: usize, charend: usize, sline: usize, eline: usize, col: usize, file: String) -> ParseInfo {
        ParseInfo {
            str: str,
            charstart: charstart,
            charend: charend,
            sline: sline,
            eline: eline,
            column: col,
            file: file
        }
    }

    pub fn getempty() -> ParseInfo{
        ParseInfo { str: String::new(), charstart: 0, charend: 0, sline: 0, eline: 0, column: 0, file: String::new() }
    }

    pub fn subtract(&mut self, info: &Self) {
        self.charstart -= info.charstart;
        self.charend -= info.charstart;
        self.sline -= info.sline;
        self.eline -= info.sline;
    }

    pub fn add(&mut self, info: &Self) {
        self.charstart += info.charstart;
        self.charend += info.charstart;
        self.sline += info.sline;
        self.eline += info.sline;
    }
}

pub enum ParseError {
    TARGETERROR(String, String),
                        //This means there has been an error in parsing the target file
                        //It contains the error, the unparsed file
    RULEERROR(String, String, String)
                        //This means there is an error after transformation
                        //It contains the rulename, error, the unparsed file
}

pub const WILDCARD: &str = "/*__BLOCK_WILD_CARD__*/";
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Unknown;