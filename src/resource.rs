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
							match typer.try_type_ast(types, resource_code, scopes, self)? {
								Some(dependency) => {
									self.add_dependency(member_id, dependency, scopes);
									*resource_typer = Some(typer);
									self.return_resource(member_id, member);
									return Ok(true);
								}
								None => {}
							}

							*resource_type = typer.types.last().unwrap().map(|return_type| {
								types.insert(Type::new(TypeKind::FunctionPointer {
									args: arg_types,
									returns: return_type,
								}))
							});

							self.compute_queue.extend(member.waiting_on_type.drain(..));
						} 
					}

					let (locals, instructions, return_value) 
						= match code_gen::compile_expression(resource_code, scopes, self) 
					{
						Ok(value) => value,
						Err(dependency) => {
							self.add_dependency(member_id, dependency, scopes);
							self.return_resource(member_id, member);
							return Ok(true);
						}
					};

					if let Some(waiting_on_value) = member.waiting_on_value.take() {
						self.compute_queue.extend(waiting_on_value);
					}

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
					if !resource_code.is_typed {
						if resource_typer.is_none() {
							*resource_typer = Some(AstTyper::new(resource_code));
						}

						if let Some(mut typer) = resource_typer.take() {
							match typer.try_type_ast(types, resource_code, scopes, self)? {
								Some(dependency) => {
									self.add_dependency(member_id, dependency, scopes);
									*resource_typer = Some(typer);
									self.return_resource(member_id, member);
									return Ok(true);
								}
								None => {}
							}

							*resource_type = *typer.types.last().unwrap();
							self.compute_queue.extend(member.waiting_on_type.drain(..));
						} 
					}

					let (locals, instructions, return_value) 
						= match code_gen::compile_expression(resource_code, scopes, self) 
					{
						Ok(value) => value,
						Err(dependency) => {
							self.add_dependency(member_id, dependency, scopes);
							self.return_resource(member_id, member);
							return Ok(true);
						}
					};

					*resource_value = Some(crate::run::run_instructions(
						&locals,
						&instructions,
						return_value,
						self,
					) as i64);

					if let Some(waiting_on_value) = member.waiting_on_value.take() {
						self.compute_queue.extend(waiting_on_value);
					}

					if DEBUG {
						println!("\n\n--- Resource {} (value) has finished computing! ---", member_id);
						if let Some(resource_type) = resource_type {
							print!("Type: ");
							types.print(*resource_type);
						}
						println!();
						println!("Locals: ");
						for (i, local) in locals.locals.iter().enumerate() {
							println!("{}: {:?}", i, local);
						}
						println!("Instructions: ");
						for instruction in &instructions {
							println!("{:?}", instruction);
						}

						println!("Value: {:?}", resource_value.unwrap());
					}
				}
				ResourceKind::CurrentlyUsed => panic!("CurrentlyUsed stuff, fix this later"),
				ResourceKind::String(ref content) => { 
					if DEBUG {
						println!("\n\n--- Resource {} (string) has finished computing! ---", member_id);
						println!("'{:?}", content);
					}
				}
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

	/// Adds a dependency on something for a resource. Once that dependency is resolved, the
	/// dependant will be pushed onto the compute queue again to resume evaluation.
	fn add_dependency(&mut self, dependant: ResourceId, dependency: Dependency, scopes: &mut Scopes) {
		match dependency {
			Dependency::Constant(scope_member_id) => {
				if let ScopeMemberKind::UndefinedDependency(ref mut dependants) =
					scopes.member_mut(scope_member_id).kind
				{
					dependants.push(dependant);
				} else {
					self.compute_queue.push_back(dependant);
				}
			}
			Dependency::Type(resource_id) => {
				let depending_on = self.resource_mut(resource_id);
				if depending_on.type_.is_none() {
					depending_on.waiting_on_type.push(dependant);
				} else {
					self.compute_queue.push_back(dependant);
				}
			}
			Dependency::Value(resource_id) => {
				let depending_on = self.resource_mut(resource_id);
				if let Some(ref mut waiting_on_value) = depending_on.waiting_on_value {
					waiting_on_value.push(dependant);
				} else {
					self.compute_queue.push_back(dependant);
				}
			}
		}
	}

	pub fn use_resource(&mut self, id: ResourceId) -> Resource {
		let resource = self.members.get_mut(id);
		let loc = resource.loc.clone();
		std::mem::replace(resource, Resource::new(loc, ResourceKind::CurrentlyUsed))
	}

	pub fn return_resource(&mut self, id: ResourceId, resource: Resource) {
		assert!(matches!(self.members.get(id).kind, ResourceKind::CurrentlyUsed));
		*self.members.get_mut(id) = resource;
	}

	pub fn resource(&self, id: ResourceId) -> &Resource {
		self.members.get(id)
	}

	pub fn resource_mut(&mut self, id: ResourceId) -> &mut Resource {
		self.members.get_mut(id)
	}
}

#[derive(Debug)]
pub enum Dependency {
	/// We depend on some ScopeMember that isn't defined yet, presumably a constant, but it could
	/// be a local too if all we want is the type.
	Constant(ScopeMemberId),
	Type(ResourceId),
	Value(ResourceId),
}

pub struct Resource {
	pub loc: CodeLoc,
	pub kind: ResourceKind,
	pub type_: Option<TypeId>,
	pub waiting_on_type: Vec<ResourceId>,
	/// This is Some when the value has not been calculated yet,
	/// but None when it has been calculated, so that we cannot add more dependencies
	/// after it's been calulated and fail compilation for no reason.
	pub waiting_on_value: Option<Vec<ResourceId>>,
}

impl Location for Resource {
	fn get_location(&self) -> CodeLoc {
		self.loc.clone()
	}
}

impl Resource {
	pub fn new(loc: CodeLoc, kind: ResourceKind) -> Self {
		Self {
			loc,
			kind,
			type_: None,
			waiting_on_type: vec![],
			waiting_on_value: Some(vec![]),
		}
	}

	pub fn new_with_type(loc: CodeLoc, kind: ResourceKind, type_: TypeId) -> Self {
		Self {
			loc,
			kind,
			type_: Some(type_),
			waiting_on_type: vec![],
			waiting_on_value: Some(vec![]),
		}
	}
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
		value: Option<i64>,
		depending_on_value: Vec<ResourceId>,
	},
}

impl std::fmt::Debug for ResourceKind {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			ResourceKind::CurrentlyUsed => write!(f, "currently used"),
			ResourceKind::ExternalFunction { .. } => write!(f, "extern func"),
			ResourceKind::Function { .. } => write!(f, "func"),
			ResourceKind::String(_) => write!(f, "string"),
			ResourceKind::Value { .. } => write!(f, "value"),
		}
	}
}
