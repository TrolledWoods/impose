use std::collections::{ VecDeque, HashSet };

use crate::parser::*;
use crate::types::*;
use crate::code_gen::*;
use crate::code_loc::*;
use crate::scopes::*;
use crate::id::*;
use crate::error::*;
use crate::run::*;
use crate::DEBUG;

create_id!(ResourceId);

#[derive(Debug)]
pub struct Resources {
	compute_queue: VecDeque<ResourceId>,
	uncomputed_resources: HashSet<ResourceId>,
	pub members: IdVec<Option<Resource>, ResourceId>,
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
		let id = self.members.push(Some(resource));
		self.uncomputed_resources.insert(id);
		self.compute_queue.push_back(id);

		id
	}
	
	pub fn insert_done(&mut self, resource: Resource) -> ResourceId {
		self.members.push(Some(resource))
	}

	/// Tries to compute one value. Returns an error if there is an error, or if
	/// the compute_queue is empty but there are still uncomputed resources
	pub fn compute_one(&mut self, types: &mut Types, scopes: &mut Scopes) -> Result<bool, ()> {
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
					// TODO: The return type should be figured out based on an '->', and not
					// implicitly.
					// TODO: Ping all of the things depending on the type of the function that
					// we are done here.

					if !resource_code.is_typed {
						if resource_typer.is_none() {
							*resource_typer = Some(AstTyper::new());
						}

						if let Some(mut typer) = resource_typer.take() {
							match typer.try_type_ast(types, resource_code, scopes, self) {
								Ok(Some(dependency)) => {
									self.add_dependency(member_id, dependency, scopes);
									*resource_typer = Some(typer);
									member.depending_on = Some(dependency);
									self.return_resource(member_id, member);
									return Ok(true);
								}
								Ok(None) => {}
								Err(()) => {
									return Ok(true);
								}
							}

							let arg_types = resource_arguments.iter().map(|&arg| {
								scopes.member(arg).type_.unwrap()
							}).collect();

							*resource_type = resource_code.nodes.last().unwrap().type_.map(|return_type| {
								types.insert(Type::new(TypeKind::FunctionPointer {
									args: arg_types,
									returns: return_type,
								}))
							});

							self.resolve_dependencies(&mut member.waiting_on_type);
						} 
					}

					let (locals, instructions, return_value) 
						= match compile_expression(resource_code, scopes, self, types) 
					{
						Ok(value) => value,
						Err(dependency) => {
							self.add_dependency(member_id, dependency, scopes);
							member.depending_on = Some(dependency);
							self.return_resource(member_id, member);
							return Ok(true);
						}
					};

					if let Some(mut waiting_on_value) = member.waiting_on_value.take() {
						self.resolve_dependencies(&mut waiting_on_value);
					}

					if DEBUG {
						println!("\n\n--- Resource {} (function) has finished computing! ---", member_id);
						print!("Type: ");
						types.print(resource_type.unwrap());
						println!();
						println!("Instructions: ");
						for instruction in &instructions {
							println!("{:?}", instruction);
						}
					}

					*resource_instructions = 
						Some((std::sync::Arc::new(locals), instructions, return_value));
				}
				ResourceKind::Value {
					code: ref mut resource_code,
					typer: ref mut resource_typer,
					value: ref mut resource_value,
					..
				} => {
					if !resource_code.is_typed {
						if resource_typer.is_none() {
							*resource_typer = Some(AstTyper::new());
						}

						if let Some(mut typer) = resource_typer.take() {
							match typer.try_type_ast(types, resource_code, scopes, self) {
								Ok(Some(dependency)) => {
									self.add_dependency(member_id, dependency, scopes);
									*resource_typer = Some(typer);
									member.depending_on = Some(dependency);
									self.return_resource(member_id, member);
									return Ok(true);
								}
								Ok(None) => {}
								Err(()) => {
									return Ok(true);
								}
							}

							*resource_type = resource_code.nodes.last().unwrap().type_;
							self.resolve_dependencies(&mut member.waiting_on_type);
						} 
					}

					let (stack_layout, instructions, return_value) 
						= match compile_expression(resource_code, scopes, self, types) 
					{
						Ok(value) => value,
						Err(dependency) => {
							self.add_dependency(member_id, dependency, scopes);
							member.depending_on = Some(dependency);
							self.return_resource(member_id, member);
							return Ok(true);
						}
					};

					// TODO: Go through the type, and change any pointers into resource pointers.
					*resource_value = Some(run_instructions(
						&instructions,
						return_value.as_ref(),
						&mut std::sync::Arc::new(stack_layout).create_instance(),
						self,
					));

					if let Some(mut waiting_on_value) = member.waiting_on_value.take() {
						self.resolve_dependencies(&mut waiting_on_value);
					}

					if DEBUG {
						println!("\n\n--- Resource {} (value) has finished computing! ---", member_id);
						if let Some(resource_type) = resource_type {
							print!("Type: ");
							types.print(*resource_type);
						}
						println!("Instructions: ");
						for instruction in &instructions {
							println!("{:?}", instruction);
						}

						println!("Value: {:?}", resource_value.as_ref().unwrap());
					}
				}
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
			Ok(false)
		}
	}

	pub fn check_completion(&self) {
		if self.uncomputed_resources.len() > 0 {
			for uncomputed_resource_id in self.uncomputed_resources.iter().copied() {
				let resource = self.resource(uncomputed_resource_id);

				match resource.depending_on {
					Some(Dependency::Constant(loc, _)) => {
						error_value!(loc, "Unknown identifier");
					}
					Some(Dependency::Type(loc, depending_on)) => {
						info!(self.resource(depending_on).loc, "Type of this is needed");
						error_value!(loc, "Needs a type that cannot be calculated");
					}
					Some(Dependency::Value(loc, depending_on)) => {
						info!(self.resource(depending_on).loc, "Value of this is needed");
						error_value!(loc, "Needs a value that cannot be calculated");
					}
					None => {
						error_value!(resource.loc, "Value cannot be computed, got forgotten for some reason");
					}
				}
			}
		}
	}

	/// Adds a dependency on something for a resource. Once that dependency is resolved, the
	/// dependant will be pushed onto the compute queue again to resume evaluation.
	///
	/// This function DOES NOT set the depending_on value, because this function may be called
	/// while a resource is taken, and in that case it can't set that flag.
	fn add_dependency(&mut self, dependant: ResourceId, dependency: Dependency, scopes: &mut Scopes) {
		match dependency {
			Dependency::Constant(_, scope_member_id) => {
				if let ScopeMemberKind::UndefinedDependency(ref mut dependants) =
					scopes.member_mut(scope_member_id).kind
				{
					dependants.push(dependant);
				} else {
					self.compute_queue.push_back(dependant);
					return;
				}
			}
			Dependency::Type(_, resource_id) => {
				let depending_on = self.resource_mut(resource_id);
				if depending_on.type_.is_none() {
					depending_on.waiting_on_type.push(dependant);
				} else {
					self.compute_queue.push_back(dependant);
					return;
				}
			}
			Dependency::Value(_, resource_id) => {
				let depending_on = self.resource_mut(resource_id);
				if let Some(ref mut waiting_on_value) = depending_on.waiting_on_value {
					waiting_on_value.push(dependant);
				} else {
					self.compute_queue.push_back(dependant);
					return;
				}
			}
		}
	}

	pub fn resolve_dependencies(&mut self, dependencies: &mut Vec<ResourceId>) {
		for resource_id in dependencies.drain(..) {
			self.resource_mut(resource_id).depending_on = None;
			self.compute_queue.push_back(resource_id);
		}
	}

	pub fn use_resource(&mut self, id: ResourceId) -> Resource {
		let resource = self.members.get_mut(id);
		resource.take().expect("Resource is taken")
	}

	pub fn return_resource(&mut self, id: ResourceId, resource: Resource) {
		let member = self.members.get_mut(id);
		assert!(member.is_none(), "Cannot return resource when member is not taken");
		*member = Some(resource);
	}

	pub fn resource(&self, id: ResourceId) -> &Resource {
		self.members.get(id).as_ref().expect("Resource is taken")
	}

	pub fn resource_mut(&mut self, id: ResourceId) -> &mut Resource {
		self.members.get_mut(id).as_mut().expect("Resource is taken")
	}
}

#[derive(Debug, Clone, Copy)]
pub enum Dependency {
	/// We depend on some ScopeMember that isn't defined yet, presumably a constant, but it could
	/// be a local too if all we want is the type.
	Constant(CodeLoc, ScopeMemberId),
	Type(CodeLoc, ResourceId),
	Value(CodeLoc, ResourceId),
}

#[derive(Debug)]
pub struct Resource {
	pub depending_on: Option<Dependency>,
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
			depending_on: None,
			loc,
			kind,
			type_: None,
			waiting_on_type: vec![],
			waiting_on_value: Some(vec![]),
		}
	}

	pub fn new_with_type(loc: CodeLoc, kind: ResourceKind, type_: TypeId) -> Self {
		Self {
			depending_on: None,
			loc,
			kind,
			type_: Some(type_),
			waiting_on_type: vec![],
			waiting_on_value: Some(vec![]),
		}
	}
}

// TODO: Make resource states encoded in an enum, to make things much simpler.
pub enum ResourceKind {
	ExternalFunction {
		// TODO: Make a more advanced interface to call external functions
		func: Box<dyn Fn(&Resources, &[u8], &mut [u8])>,
		n_arg_bytes: usize,
		n_return_bytes: usize,
	},
	Function {
		// argument_type_defs: Vec<Ast>,
		// waiting_on_type: Vec<ResourceId>,
		arguments: Vec<ScopeMemberId>,
		code: Ast,
		typer: Option<AstTyper>,
		instructions: Option<(
			std::sync::Arc<crate::stack_frame::StackFrameLayout>,
			Vec<Instruction>, 
			Option<crate::stack_frame::Value>,
		)>,
	},
	String(String),
	Value {
		code: Ast,
		typer: Option<AstTyper>,
		depending_on_type: Vec<ResourceId>,
		value: Option<crate::stack_frame::ConstBuffer>,
		depending_on_value: Vec<ResourceId>,
	},
}

impl std::fmt::Debug for ResourceKind {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			ResourceKind::ExternalFunction { .. } => write!(f, "extern func"),
			ResourceKind::Function { .. } => write!(f, "func"),
			ResourceKind::String(_) => write!(f, "string"),
			ResourceKind::Value { .. } => write!(f, "value"),
		}
	}
}
