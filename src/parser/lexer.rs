use crate::code_loc::*;
use crate::error::*;
use crate::operator::*;

const KEYWORDS: &[&str] = &[
    "if", "else", "loop", "skip", "bit_cast", "type_of", "type", "struct", "import",
];

#[derive(Debug, Clone)]
pub struct Token {
    pub loc: CodeLoc,
    pub kind: TokenKind,
}

impl Token {
    fn new(loc: CodeLoc, kind: TokenKind) -> Self {
        Token { loc, kind }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Identifier(ustr::Ustr),
    Keyword(&'static str),
    Operator(Operator),
    Semicolon,
    Comma,
    Colon,
    ConstMember,
    Bracket(char),
    ClosingBracket(char),
    NumericLiteral(i128), // TODO: Make the numeric literal arbitrarily large.
    FloatLiteral(f64),
    StringLiteral(String),
}

impl Location for Token {
    fn get_location(&self) -> CodeLoc {
        self.loc.clone()
    }
}

struct Lexer<'a> {
    chars: std::str::CharIndices<'a>,
    source_code_location: CodeLoc,
}

impl Lexer<'_> {
    fn peek(&self) -> Option<char> {
        self.chars.clone().next().map(|(_, c)| c)
    }

    fn next(&mut self) -> Option<char> {
        self.chars.next().map(|(_, c)| c)
    }

    fn as_str(&self) -> &str {
        self.chars.as_str()
    }

    fn skip_if_starts_with(&mut self, text: &str) -> Option<CodeLoc> {
        let string = self.chars.as_str();
        if string.starts_with(text) {
            self.chars = string[text.len()..].char_indices();
            let old_loc = self.source_code_location.clone();
            self.source_code_location.column += text.chars().count() as u32;
            Some(old_loc)
        } else {
            None
        }
    }
}

impl Location for Lexer<'_> {
    fn get_location(&self) -> CodeLoc {
        self.source_code_location.clone()
    }
}

fn move_pos_with_char(pos: &mut CodeLoc, character: char) {
    pos.column += 1;

    if character == '\n' {
        pos.line += 1;
        pos.column = 1;
    }
}

pub fn lex_code(file: ustr::Ustr, code: &str) -> Result<(CodeLoc, Vec<Token>), ()> {
    let mut lexer = Lexer {
        chars: code.char_indices(),
        source_code_location: CodeLoc {
            line: 1,
            column: 1,
            file,
        },
    };

    let mut tokens = Vec::new();

    skip_whitespace(&mut lexer);
    while let Some(c) = lexer.peek() {
        match c {
            '(' | '[' | '{' => {
                tokens.push(Token::new(
                    lexer.source_code_location.clone(),
                    TokenKind::Bracket(c),
                ));
                lexer.next();
                lexer.source_code_location.column += 1;
            }
            ')' | ']' | '}' => {
                tokens.push(Token::new(
                    lexer.source_code_location.clone(),
                    TokenKind::ClosingBracket(c),
                ));
                lexer.next();
                lexer.source_code_location.column += 1;
            }
            ';' => {
                tokens.push(Token::new(
                    lexer.source_code_location.clone(),
                    TokenKind::Semicolon,
                ));
                lexer.next();
                lexer.source_code_location.column += 1;
            }
            ',' => {
                tokens.push(Token::new(
                    lexer.source_code_location.clone(),
                    TokenKind::Comma,
                ));
                lexer.source_code_location.column += 1;
                lexer.next();
            }
            '\\' => {
                tokens.push(Token::new(
                    lexer.source_code_location.clone(),
                    TokenKind::ConstMember,
                ));
                lexer.source_code_location.column += 1;
                lexer.next();
            }
            _ if c.is_alphabetic() || c == '_' => {
                let (location, identifier) = lex_identifier(&mut lexer);

                let mut found_keyword = false;
                for &keyword in KEYWORDS {
                    if identifier == keyword {
                        tokens.push(Token::new(location.clone(), TokenKind::Keyword(keyword)));
                        found_keyword = true;
                    }
                }

                if !found_keyword {
                    tokens.push(Token::new(
                        location,
                        TokenKind::Identifier(ustr::ustr(identifier)),
                    ));
                }
            }
            _ if c.is_digit(10) => {
                tokens.push(match lex_numeric_literal(&mut lexer)? {
                    (loc, Number::Integer(num)) => Token {
                        loc,
                        kind: TokenKind::NumericLiteral(num),
                    },
                    (loc, Number::Float(num)) => Token {
                        loc,
                        kind: TokenKind::FloatLiteral(num),
                    },
                });
            }
            '"' => {
                let (loc, string) = lex_string_literal(&mut lexer)?;
                tokens.push(Token::new(loc, TokenKind::StringLiteral(string)));
            }
            c => {
                // Might be an operator
                let mut found_operator = false;
                for &(name, operator) in OPERATORS {
                    if let Some(loc) = lexer.skip_if_starts_with(name) {
                        tokens.push(Token::new(loc, TokenKind::Operator(operator)));
                        found_operator = true;
                    }
                }

                if !found_operator && c == ':' {
                    tokens.push(Token::new(
                        lexer.source_code_location.clone(),
                        TokenKind::Colon,
                    ));
                    lexer.source_code_location.column += 1;
                    lexer.next();

                    found_operator = true;
                }

                if !found_operator {
                    return error!(lexer, "Invalid character {}", c);
                }
            }
        }

        skip_whitespace(&mut lexer);
    }

    Ok((lexer.source_code_location, tokens))
}

fn skip_whitespace(lexer: &mut Lexer) {
    while let Some(c) = lexer.peek() {
        if c == '/' && lexer.as_str().as_bytes()[1] == b'/' {
            while let Some(c) = lexer.next() {
                if c == '\n' {
                    break;
                }
            }

            lexer.source_code_location.column = 1;
            lexer.source_code_location.line += 1;
            continue;
        }

        if !c.is_whitespace() {
            return;
        }

        move_pos_with_char(&mut lexer.source_code_location, c);
        lexer.next();
    }
}

fn lex_numeric_literal(lexer: &mut Lexer) -> Result<(CodeLoc, Number), ()> {
    let location = lexer.source_code_location.clone();
    let mut number: i128 = 0;
    let mut base = 10;
    let mut has_custom_base = false;
    let mut has_digits = false;

    let mut float_number: f64 = 0.0;
    let mut is_float = None;

    while let Some(c) = lexer.peek() {
        match c.to_digit(base) {
            Some(digit) => {
                match is_float {
                    None => {
                        let (num, overflow_a) = number.overflowing_mul(base as i128);
                        let (num, overflow_b) = num.overflowing_add(digit as i128);

                        if overflow_a || overflow_b {
                            return error!(lexer, "Number too big");
                        }

                        number = num;
                        has_digits = true;
                    }
                    Some(ref mut num) => {
                        *num /= base as f64;
                        float_number += *num * (digit as f64);
                    }
                }

                lexer.next();
                lexer.source_code_location.column += 1;
            }
            None if c == '_' => {
                lexer.next();
                lexer.source_code_location.column += 1;
            }
            None if c == '.' && is_float.is_none() => {
                lexer.next();
                float_number = number as f64;
                is_float = Some(1.0);
            }
            None if is_float.is_none() && !has_custom_base && c.is_alphabetic() => match c {
                'c' => {
                    if number > 36 {
                        return error!(
                            location,
                            "Cannot have a base higher than 36(got {})", number
                        );
                    } else if number < 2 {
                        return error!(location, "Cannot have a base less than 2(got {})", number);
                    }

                    lexer.next();
                    lexer.source_code_location.column += 1;

                    // This is fine because we know number is between 2 and 46
                    base = number as u32;
                    number = 0;
                    float_number = 0.0;
                    has_custom_base = true;
                    has_digits = false;
                }
                'x' => {
                    if number != 0 {
                        return error!(
                            location,
                            "Expected '0' before hexadecimal base specifier, got '{}'", number
                        );
                    }

                    lexer.next();
                    lexer.source_code_location.column += 1;

                    base = 16;
                    number = 0;
                    float_number = 0.0;
                    has_custom_base = true;
                    has_digits = false;
                }
                'b' => {
                    if number != 0 {
                        return error!(
                            location,
                            "Expected '0' before binary base specifier, got '{}'", number
                        );
                    }

                    lexer.next();
                    lexer.source_code_location.column += 1;

                    base = 2;
                    number = 0;
                    float_number = 0.0;
                    has_custom_base = true;
                    has_digits = false;
                }
                _ => {
                    return error!(
                        lexer,
                        "Invalid custom base character in numberic literal.\n\
						If you intended to have an identifier after the number, \
						add a space in between."
                    );
                }
            },
            None if c.is_digit(36) => {
                if c.is_alphabetic() {
                    return error!(lexer, "Digit '{}' is not a number in the given base(alphabetic character can be digits too in high bases", c);
                } else {
                    return error!(lexer, "Digit '{}' is not a number in the given base", c);
                }
            }
            None => break,
        }
    }

    if !has_digits {
        return error!(lexer, "Number has to have digits");
    }

    match is_float {
        Some(_) => Ok((location, Number::Float(float_number))),
        None => Ok((location, Number::Integer(number))),
    }
}

enum Number {
    Integer(i128),
    Float(f64),
}

fn lex_string_literal(lexer: &mut Lexer) -> Result<(CodeLoc, String), ()> {
    let location = lexer.source_code_location.clone();

    let mut quotes = 0;
    while lexer.peek() == Some('"') {
        lexer.next();
        lexer.source_code_location.column += 1;
        quotes += 1;
    }
    assert!(
        quotes > 0,
        "Don't call lex_string_literal without having found a double quote"
    );

    let mut quote_streak = 0;
    let mut string = String::new();
    loop {
        let c = match lexer.next() {
            Some(c) => c,
            None => {
                // TODO: Show a note of where the string literal started.
                return error!(lexer, "String literal wasn't closed");
            }
        };
        move_pos_with_char(&mut lexer.source_code_location, c);

        if c == '"' {
            quote_streak += 1;
            if quote_streak == quotes {
                break;
            }
            continue;
        } else if quote_streak > 0 {
            for _ in 0..quote_streak {
                string.push('"');
            }
            quote_streak = 0;
        }

        if c == '\\' {
            // Escaped character
            let c = match lexer.next() {
                Some(value) => value,
                None => {
                    return error!(lexer, "String literal wasn't closed");
                }
            };
            move_pos_with_char(&mut lexer.source_code_location, c);

            match c {
                'u' => {
                    use std::convert::TryInto;

                    // Parse a unicode letter
                    let (num_loc, number) = match lex_numeric_literal(lexer)? {
                        (loc, Number::Integer(number)) => (loc, number),
                        (loc, _) => return error!(loc, "Expected integer, got float"),
                    };

                    let number_u32: u32 = match number.try_into() {
                        Ok(n) => n,
                        Err(_) => {
                            return error!(num_loc, "Number {} does not fit within 32 bits, which is required for unicode values", number);
                        }
                    };
                    let unicode = match char::from_u32(number_u32) {
                        Some(unicode) => unicode,
                        None => {
                            return error!(num_loc, "Number {} is invalid unicode", number);
                        }
                    };

                    if let Some('\\') = lexer.next() {
                        lexer.source_code_location.column += 1;
                        string.push(unicode);
                    } else {
                        return error!(
                            lexer,
                            "Expected '\\' character after unicode escape character."
                        );
                    }
                }
                '\\' => string.push('\\'),
                '"' => string.push('"'),
                'n' => string.push('\n'),
                'r' => string.push('\r'),
                't' => string.push('\t'),
                _ => {
                    return error!(lexer, "'{}' is not a valid escape character", c);
                }
            }

            continue;
        }

        string.push(c);
    }

    Ok((location, string))
}

fn lex_identifier<'a>(lexer: &mut Lexer<'a>) -> (CodeLoc, &'a str) {
    let location = lexer.source_code_location.clone();
    let start = lexer.chars.as_str();

    let mut char_indices = start.char_indices();
    for (i, c) in &mut char_indices {
        if !(c.is_alphabetic() || c == '_' || c.is_digit(10)) {
            return (location, &start[..i]);
        } else {
            move_pos_with_char(&mut lexer.source_code_location, c);
            lexer.next();
        }
    }

    // TODO: Error message here? The end of the file should never be
    // an identifier in proper code, but the error message might be better
    // presented elsewhere, like in the parser for example.
    (location, start)
}
