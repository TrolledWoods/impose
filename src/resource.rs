use crate::prelude::*;
use crate::code_gen;
use std::collections::{ VecDeque, HashSet };

create_id!(ResourceId);

pub struct Resources {
	compute_queue: VecDeque<ResourceId>,
	uncomputed_resources: HashSet<ResourceId>,
	pub members: IdVec<Resource, ResourceId>,
}

impl Resources {
	pub fn new() -> Self {
		Self {
			members: Default::default(),
			compute_queue: Default::default(),
			uncomputed_resources: Default::default(),
		}
	}

	pub fn insert(&mut self, resource: Resource) -> ResourceId {
		let id = self.members.push(resource);
		self.uncomputed_resources.insert(id);
		self.compute_queue.push_back(id);
		id
	}

	/// Tries to compute one value. Returns an error if there is an error, or if
	/// the compute_queue is empty but there are still uncomputed resources
	pub fn compute_one(&mut self, types: &mut Types, scopes: &mut Scopes) -> Result<bool> {
		if let Some(member_id) = self.compute_queue.pop_front() {
			let mut member = self.use_resource(member_id);
			let resource_type = &mut member.type_;

			match member.kind {
				ResourceKind::Function { 
					arguments: ref resource_arguments, 
					code: ref mut resource_code, 
					instructions: ref mut resource_instructions,
					typer: ref mut resource_typer,
				} => {
					// TODO: Figure out the types of all the arguments.
					// TODO: Ping all of the things depending on the type of the function that
					// we are done here.
					// We are going to assume at first that all arguments are of type U64.
					// TODO: The return type should be figured out based on an '->', and not
					// implicitly.
					let arg_types = resource_arguments.iter()
						.map(|_| types.insert(Type::new(TypeKind::Primitive(PrimitiveKind::U64))))
						.collect();

					if !resource_code.is_typed {
						if resource_typer.is_none() {
							*resource_typer = Some(AstTyper::new(resource_code));
						}

						if let Some(mut typer) = resource_typer.take() {
							// TODO: Check if the error is an unknown identifier or something 
							// like that, in which case just put this back on the todo list.
							typer.try_type_ast(types, resource_code, scopes, self)?;

							// TODO: If the typer is not done, put the typer back into the option.

							// TODO: Remove this implicit type check
							let return_type = typer.types.last().unwrap().unwrap();
							*resource_type = Some(types.insert(Type::new(TypeKind::FunctionPointer {
								args: arg_types,
								returns: return_type,
							})));
						} 
					}

					// Generate the instructions
					// TODO: If the value is not defined yet, pause, and come back later.
					let (locals, instructions, return_value) 
						= code_gen::compile_expression(resource_code, scopes, self);

					if DEBUG {
						println!("\n\n--- Resource {} (function) has finished computing! ---", member_id);
						print!("Type: ");
						types.print(resource_type.unwrap());
						println!();
						println!("Locals: ");
						for (i, local) in locals.locals.iter().enumerate() {
							println!("{}: {:?}", i, local);
						}
						println!("Instructions: ");
						for instruction in &instructions {
							println!("{:?}", instruction);
						}
					}

					*resource_instructions = Some((locals, instructions, return_value));
				}
				ResourceKind::Value {
					code: ref mut resource_code,
					typer: ref mut resource_typer,
					value: ref mut resource_value,
					..
				} => {
					*resource_type = 
						Some(types.insert(Type::new(TypeKind::Primitive(PrimitiveKind::U64))));

					if !resource_code.is_typed {
						if resource_typer.is_none() {
							*resource_typer = Some(AstTyper::new(resource_code));
						}

						if let Some(mut typer) = resource_typer.take() {
							// TODO: Check if the error is an unknown identifier or something 
							// like that, in which case just put this back on the todo list.
							typer.try_type_ast(types, resource_code, scopes, self)?;

							// TODO: If the typer is not done, put the typer back into the option.
						} 
					}

					// Generate the instructions
					// TODO: If the value is not defined yet, pause, and come back later.
					let (locals, instructions, return_value) 
						= code_gen::compile_expression(resource_code, scopes, self);

					if DEBUG {
						println!("\n\n--- Resource {} (value) has finished computing! ---", member_id);
						print!("Type: ");
						types.print(resource_type.unwrap());
						println!();
						println!("Locals: ");
						for (i, local) in locals.locals.iter().enumerate() {
							println!("{}: {:?}", i, local);
						}
						println!("Instructions: ");
						for instruction in &instructions {
							println!("{:?}", instruction);
						}
					}

					*resource_value = Some(vec![Primitive::U64(crate::run::run_instructions(
						&locals,
						&instructions,
						return_value,
						self,
					) as u64)]);
				}
				ResourceKind::CurrentlyUsed => panic!("CurrentlyUsed stuff, fix this later"),
				ResourceKind::String(_) => { }
				ResourceKind::ExternalFunction { .. } => { }
			}

			self.return_resource(member_id, member);
			self.uncomputed_resources.remove(&member_id);
			Ok(true)
		} else {
			if self.uncomputed_resources.len() > 0 {
				panic!("Some resources are not computed!");
			} else {
				Ok(false)
			}
		}
	}

	pub fn use_resource(&mut self, id: ResourceId) -> Resource {
		let resource = self.members.get_mut(id);
		let loc = resource.loc.clone();
		std::mem::replace(resource, Resource { loc, kind: ResourceKind::CurrentlyUsed, type_: None })
	}

	pub fn return_resource(&mut self, id: ResourceId, resource: Resource) {
		assert!(matches!(self.members.get(id).kind, ResourceKind::CurrentlyUsed));
		*self.members.get_mut(id) = resource;
	}

	pub fn resource(&self, id: ResourceId) -> &Resource {
		self.members.get(id)
	}
}

pub struct Resource {
	pub loc: CodeLoc,
	pub kind: ResourceKind,
	pub type_: Option<TypeId>,
}

impl Location for Resource {
	fn get_location(&self) -> CodeLoc {
		self.loc.clone()
	}
}

impl Resource {
}

pub enum ResourceKind {
	CurrentlyUsed,
	ExternalFunction {
		// TODO: Make a more advanced interface to call external functions
		func: Box<dyn Fn(&Resources, &[i64]) -> i64>,
	},
	Function {
		// argument_type_defs: Vec<Ast>,
		// waiting_on_type: Vec<ResourceId>,
		arguments: Vec<ScopeMemberId>,
		code: Ast,
		typer: Option<AstTyper>,
		instructions: Option<(code_gen::Locals, Vec<code_gen::Instruction>, code_gen::Value)>,
	},
	String(String),
	Value {
		code: Ast,
		typer: Option<AstTyper>,
		depending_on_type: Vec<ResourceId>,
		value: Option<Vec<Primitive>>,
		depending_on_value: Vec<ResourceId>,
	},
}
