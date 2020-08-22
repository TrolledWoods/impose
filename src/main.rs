#![feature(assoc_char_funcs)]

mod lexer;

fn main() {
	let code = r#""Strings seem to work just fine now! :D \n""#;
	match lexer::lex_code(code) {
		Ok(tokens) => {
			for token in tokens {
				println!("{:?}: {:?}", &token.loc, &token.kind);
			}
		},
		Err(err) => {
			println!("ERROR: {}", err.message);
			println!("{}", code);
			println!("{}^", "-".repeat(
				err.source_code_location.column.saturating_sub(1) as usize
			));
		}
	};
}
