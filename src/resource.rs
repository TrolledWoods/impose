use crate::prelude::*;
use crate::code_gen;

pub type ResourceId = usize;

pub struct Resources {
	pub members: Vec<Resource>,
}

impl Resources {
	pub fn new() -> Self {
		Self {
			members: Vec::new(),
		}
	}

	pub fn insert(&mut self, resource: Resource) -> ResourceId {
		let id = self.members.len();
		self.members.push(resource);
		id
	}

	pub fn resource(&self, id: ResourceId) -> &Resource {
		&self.members[id]
	}

	pub fn resource_mut(&mut self, id: ResourceId) -> &mut Resource {
		&mut self.members[id]
	}
}

pub struct Resource {
	pub loc: CodeLoc,
	pub kind: ResourceKind,
}

impl Location for Resource {
	fn get_location(&self) -> CodeLoc {
		self.loc.clone()
	}
}

pub enum ResourceKind {
	Function {
		arguments: Vec<ScopeMemberId>,
		// argument_type_defs: Vec<Ast>,
		// argument_types: Vec<Option<TypeId>>,
		code: Ast,
		instructions: Option<(code_gen::Locals, Vec<code_gen::Instruction>)>,
	},
	String(String),
}
