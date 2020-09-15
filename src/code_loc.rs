#[derive(Clone, PartialEq, Eq)]
pub struct CodeLoc {
	pub file: ustr::Ustr,
	pub line: u32, 
	pub column: u32,
}

impl Location for CodeLoc {
	fn get_location(&self) -> CodeLoc { self.clone() }
}

impl std::fmt::Debug for CodeLoc {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "'{}'({}:{})", self.file, self.line, self.column)
	}
}

pub trait Location {
	fn get_location(&self) -> CodeLoc;
}
