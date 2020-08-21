mod parser;

fn main() {
	let thing = parser::lex_code(r#"
		x ====+=+--**//// if loop 
	"#).unwrap();
	println!("Success! {:?}", thing);
}
