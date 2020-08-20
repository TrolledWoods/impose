type CodeLoc = (u32, u32);

#[derive(Debug)]
pub struct Error {	
	message: String,
	source_code_location: CodeLoc,
	compiler_location: CodeLoc,
}

// This is a macro to allow the compiler line and column to ergonomically be passed
// inside
macro_rules! make_error {
	($lexer:expr, $($format_message:tt)+) => {{
		return Err(Error {
			message: format!($($format_message)+),
			source_code_location: $lexer.source_code_location,
			compiler_location: (line!(), column!()),
		}.into());
	}}
}

#[derive(Debug)]
pub enum Token<'a> {
	Identifier(CodeLoc, &'a str),
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
}

fn move_pos_with_char(pos: &mut CodeLoc, character: char) {
	pos.1 + 1;

	if character == '\n' {
		pos.0 += 1;
		pos.1 = 1;
	}
}

pub fn lex_string(code: &str) -> Result<Vec<Token>, Error> {
	let mut lexer = Lexer {
		chars: code.char_indices(),
		source_code_location: (1, 1),
	};

	let mut tokens = Vec::new();

	skip_whitespace(&mut lexer);
	while let Some(c) = lexer.peek() {
		match c {
			_ if c.is_alphabetic() => {
				let identifier = lex_identifier(&mut lexer);

				match identifier {
					_ => {
						tokens.push(Token::Identifier(lexer.source_code_location, identifier));
					}
				}
			}
			c => {
				make_error!(lexer, "Invalid character {}", c);
			}
		}

		skip_whitespace(&mut lexer);
	}

	Ok(tokens)
}

fn skip_whitespace(lexer: &mut Lexer) {
	while let Some(c) = lexer.peek() {
		if c == '#' {
			// Skip comment lines
			while let Some(c) = lexer.next() {
				if c == '\n' { break; }
			}

			lexer.source_code_location.0 += 1;
			lexer.source_code_location.1 = 1;
			continue;
		} 

		if !c.is_whitespace() {
			return;
		} 

		move_pos_with_char(&mut lexer.source_code_location, c);
		lexer.next();
	}
}

fn lex_identifier<'a>(lexer: &mut Lexer<'a>) -> &'a str {
	let start = lexer.chars.as_str();

	let mut char_indices = start.char_indices();
	for (i, c) in &mut char_indices {
		if !c.is_alphabetic() {
			return &start[..i];
		} else {
			move_pos_with_char(&mut lexer.source_code_location, c);
			lexer.next();
		}
	}

	// TODO: Error message here? The end of the file should never be
	// an identifier in proper code, but the error message might be better
	// presented elsewhere, like in the parser for example.
	start
}
