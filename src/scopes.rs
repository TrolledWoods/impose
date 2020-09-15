// TODO: Remove parser dependency here!
use crate::parser::*;
use crate::resource::*;
use crate::stack_frame::*;
use crate::types::*;
use crate::id::*;
use crate::code_loc::*;
use crate::{ Error, Result };

/// Scopes contains all the scopes in the entire program.
#[derive(Debug)]
pub struct Scopes {
	scopes: IdVec<Scope, ScopeId>,
	members: IdVec<ScopeMember, ScopeMemberId>,
	/// The super_scope is stuff that is contained within all the things.
	pub super_scope: ScopeId,
}

impl Scopes {
	pub fn new() -> Self {
		let mut scopes = IdVec::new();
		let super_scope = scopes.push(Default::default());
		Scopes {
			scopes,
			members: IdVec::new(),
			super_scope,
		}
	}

	pub fn insert_root_value(
		&mut self, 
		resources: &mut Resources,
		name: ustr::Ustr, 
		type_: TypeId, 
		value: ConstBuffer,
	) {
		let loc = CodeLoc { file: std::rc::Rc::new(format!("no")), line: 0, column: 0 };
		let mut ast = Ast::new();
		ast.is_typed = true;
		let id = resources.insert_done(Resource::new_with_type(
			loc.clone(),
			ResourceKind::Value {
				code: ast,
				typer: None,
				depending_on_type: Vec::new(),
				value: Some(value),
				depending_on_value: Vec::new(),
			},
			type_,
		));

		let scope = self.super_scope;
		self.declare_member(scope, name, None, ScopeMemberKind::Constant(id)).unwrap();
	}

	pub fn insert_root_resource(
		&mut self, 
		resources: &mut Resources,
		name: ustr::Ustr, 
		type_: TypeId, 
		kind: ResourceKind,
	) -> Result<()> {
		let loc = CodeLoc { file: std::rc::Rc::new(format!("no")), line: 0, column: 0 };
		let mut ast = Ast::new();
		ast.is_typed = true;
		let id = resources.insert_done(Resource::new_with_type(
			loc.clone(),
			kind,
			type_,
		));

		let scope = self.super_scope;
		self.declare_member(scope, name, None, ScopeMemberKind::Constant(id))?;

		Ok(())
	}

	#[allow(unused)]
	pub fn debug(&self, scope_id: ScopeId, indent: usize) {
		println!("{}Scope {:?}:", "\t".repeat(indent), scope_id);
		for member in self.scopes.get(scope_id).members.iter() {
			println!("{}Member {}: {:?}", "\t".repeat(indent), 
				self.members.get(*member).name, self.members.get(*member).kind);
		}

		for scope in self.scopes.get(scope_id).sub_scopes.iter() {
			self.debug(*scope, indent + 1);
		}
	}

	pub fn create_scope(&mut self, parent: Option<ScopeId>) -> ScopeId {
		let parent = parent.unwrap_or(self.super_scope);
		let id = self.scopes.push(Scope { 
			parent: Some(parent), 
			.. Default::default()
		});

		self.scopes.get_mut(parent).sub_scopes.push(id);

		id
	}

	pub fn member(&self, mut member: ScopeMemberId) -> &ScopeMember {
		// Because an indirect never points to another indirect(because then we can just redirect
		// to the thing that redirects), we can just do an if here.
		if let ScopeMemberKind::Indirect(indirect) = self.members.get(member).kind {
			member = indirect;
		}
		self.members.get(member)
	}

	pub fn member_mut(&mut self, mut member: ScopeMemberId) -> &mut ScopeMember {
		if let ScopeMemberKind::Indirect(indirect) = self.members.get(member).kind {
			member = indirect;
		}
		self.members.get_mut(member)
	}

	pub fn find_member(&self, mut scope_id: ScopeId, name: ustr::Ustr) -> Option<ScopeMemberId> {
		loop {
			for member_id in self.scopes.get(scope_id).members.iter() {
				// This does not use the ``member`` function on purpose, because the member function
				// uses indirection, while this does not use it.
				if self.members.get(*member_id).name == name {
					return Some(*member_id);
				}
			}

			scope_id = self.scopes.get(scope_id).parent?;
		}
	}

	fn get_members_in_subscopes_with_name(
		&self,
		scope_id: ScopeId,
		name: &str,
		// TODO: Use TinyVec or something to not allocate with few elements.
		buffer: &mut Vec<(ScopeId, ScopeMemberId)>,
	) {
		// If we find a member in this scope, there cannot possibly be a member in a subscope,
		// because that would be a name collision. However, there can be several different members
		// with the same name in different subscopes.
		for member_id in self.scopes.get(scope_id).members.iter().cloned() {
			if self.member(member_id).name == name {
				buffer.push((scope_id, member_id));
				// There is no way for another thing in a subscope to have the same name because 
				// that would be a name collision.
				return;
			}
		}

		// Not in this scope, so it may be in a subscope
		for sub_scope_id in self.scopes.get(scope_id).sub_scopes.iter().cloned() {
			self.get_members_in_subscopes_with_name(sub_scope_id, name, buffer);
		}
	}

	pub fn find_or_create_temp(&mut self, scope: ScopeId, name: ustr::Ustr) -> Result<ScopeMemberId> {
		if let Some(member_id) = self.find_member(scope, name) {
			return Ok(member_id);
		} else {
			let (mut dependants, id) = self.declare_member(scope, name, None, ScopeMemberKind::UndefinedDependency(Vec::new()))?;
			if let ScopeMemberKind::UndefinedDependency(ref mut vec) = self.member_mut(id).kind {
				vec.append(&mut dependants);
			} else { unreachable!(); }

			Ok(id)
		}
	}

	pub fn declare_member(
		&mut self, 
		scope: ScopeId, 
		name: ustr::Ustr, 
		loc: Option<&CodeLoc>,
		kind: ScopeMemberKind,
	) -> Result<(Vec<ResourceId>, ScopeMemberId)> {
		let mut same_names_in_sub_scopes = Vec::new();
		self.get_members_in_subscopes_with_name(scope, &name, &mut same_names_in_sub_scopes);

		let mut declared_member_id = None;

		let mut dependants_on_variable = Vec::new();

		// Member that we want to declare
		let mut member_we_are_declaring = Some(ScopeMember { 
			declaration_location: loc.cloned(), 
			name,
			kind,
			type_: None,
			storage_loc: None,
		});

		// TODO: If I get around to multithreading, we have to change this completely, because
		// anything can happen an that point.

		for (same_name_scope, same_name_id) in same_names_in_sub_scopes {
			// Check that the member is a temporary and not something else
			let member = self.members.get_mut(same_name_id);
			if let ScopeMemberKind::UndefinedDependency(ref mut dependants) = member.kind {
				dependants_on_variable.append(dependants);

				if let Some((_, declared_member_id)) = declared_member_id {
					// The member we have declared is already in a scope, however, 
					member.kind = ScopeMemberKind::Indirect(declared_member_id);
				} else {
					// Swap the UndefinedDependency here with the thing we are going to declare,
					// and change the scope of it.

					*member = member_we_are_declaring.take().unwrap();

					// Change the scope
					let declared_member_scope = self.scopes.get_mut(same_name_scope);
					let index = declared_member_scope.members.iter()
						.position(|&member| member == same_name_id)
						.expect("Scope should contain member");
					declared_member_scope.members.swap_remove(index);
					self.scopes.get_mut(scope).members.push(same_name_id);

					declared_member_id = Some((same_name_scope, same_name_id));
				}
			} else {
				if let Some(ref loc) = self.member(same_name_id).declaration_location {
					// TODO: Show where it was taken before.
					return_error!(
						loc,
						"Name is already taken"
					);
				} else {
					panic!("Non code based identifier name clash");
				}
			}
		}

		let declared_member_id = match declared_member_id {
			Some((_, declared_member_id)) => {
				(dependants_on_variable, declared_member_id)
			}
			None => {
				// There is no way for us to have depenendants if there were no UndefinedDependencies,
				// because if there were a depenendant already, we would have one of those.
				assert_eq!(dependants_on_variable.len(), 0);
				let scope_instance = self.scopes.get_mut(scope);
				let id = self.members.push(member_we_are_declaring.take().unwrap());
				scope_instance.members.push(id);
				(dependants_on_variable, id)
			}
		};
		
		Ok(declared_member_id)
	}
}

#[derive(Debug, Default)]
pub struct Scope {
	// TODO: Add stack frame id:s to scopes, so that we can check if a local is from the current
	// stack frame and not some other stack frame, which can cause very weird behaviour.
	pub parent: Option<ScopeId>,
	// TODO: Make this better
	pub has_locals: bool,
	members: Vec<ScopeMemberId>,
	sub_scopes: Vec<ScopeId>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ScopeMemberKind {
	UndefinedDependency(Vec<ResourceId>),
	/// Redirects to another scope member. Used if 2 temporaries are created for the same variable,
	/// in which case on of them has to become a "false" temporary and point to the other one,
	/// because the things depending on them have different id:s.
	Indirect(ScopeMemberId),

	LocalVariable,
	FunctionArgument,
	Label,
	Constant(ResourceId),
}

#[derive(Debug)]
pub struct ScopeMember {
	pub name: ustr::Ustr,
	pub kind: ScopeMemberKind,
	pub declaration_location: Option<CodeLoc>,
	pub type_: Option<TypeId>,
	pub storage_loc: Option<LocalHandle>,
}

create_id!(ScopeId);

create_id!(
	/// NOTE: Even if 2 ScopeMemberId:s are different, doesn't mean that they point to different
	/// variables. This is because we use a system to temorarily place scope members when making constants,
	/// but that may create duplicates. For example:
	///
	/// ```impose
	/// {
	/// 	print(MY_CONSTANT);
	/// 	// Here, a temporary scope member called 'MY_CONSTANT' is created
	/// }
	/// {
	/// 	print(MY_CONSTANT);
	/// 	// Here, another temporary scope member called 'MY_CONSTANT' is created
	/// }
	///
	/// MY_CONSTANT :: "Hello, World!";
	/// // This MY_CONSTANT looks into subscopes, finds out that there are 2 temporaries that should
	/// // point to this constant. Hence, we have 2 id:s that point to MY_CONSTANT even though there
	/// // is only one constant
	/// ```
	ScopeMemberId
);
