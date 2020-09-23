//! Types abstract syntax trees into a different kind of abstract syntax
//! tree
use smallvec::SmallVec;
use std::collections::HashMap;

use crate::align::*;
use crate::error::*;
use crate::code_loc::*;
use crate::types::*;
use crate::resource::*;
use crate::operator::*;
use crate::scopes::*;
use crate::id::*;
use crate::parser;

create_id!(NodeId);

#[derive(Debug)]
pub struct Node {
	pub kind: NodeKind,
	pub loc: CodeLoc,
	// TODO: Think about whether or not this is necessary
	pub type_: TypeId,
}

impl Location for Node {
	fn get_location(&self) -> CodeLoc {
		self.loc
	}
}

#[derive(Debug)]
pub enum MarkerKind {
	IfCondition,
	IfElseSeparator,
	LoopHead,
}

/// The "philosophy" for nodes in this ast is very different from parser nodes. There are lots
/// and lots of different parser nodes, without reservation, but when we get into typing we
/// want to simplify the tree as much as possible and reduce the number of concepts at play.
/// Therefore, a lot of the nodes are quite general.
#[derive(Debug)]
pub enum NodeKind {
	/// No children
	// TODO: Since constants turn into Constant or Resource,
	// consider making this only for locals? Later, maybe we have some system for
	// only local id.
	ScopeMember {
		id: ScopeMemberId,
		// sub_member: SubMemberAccess,
	},
	/// Has one child
	SubMember {
		sub_member: SubMemberAccess,
	},
	/// No children
	Resource {
		id: ResourceId,
		// sub_member: SubMemberAccess,
	},
	/// No children
	Constant(SmallVec<[u8; 8]>),
	/// n_members children
	Block {
		n_members: usize,
	},
	/// 1 child
	Skip {
		label: ScopeMemberId,
	},
	/// n_args + 1 children [function pointer, arg1, arg2, arg3, ...]
	FunctionCall {
		function_type: TypeId,
		n_args: usize,
	},
	/// 2 children, [condition, block] + 1 member, the condition
	If,
	/// 3 children, [condition, true block, false block] + 2 members, condition and else block.
	IfElse,
	/// 1 child, the expression that it loops + 1 member, top of loop.
	Loop,
	/// A marker, does not have children and is not a child.
	Marker(MarkerKind),
	/// TODO: Thing about combining this with assignment, and using local lifetime analysis
	/// to determine when it should be introduced.
	Declaration {
		id: ScopeMemberId
	},
	Struct {
		n_members: usize,
	},
	/// Two children
	// TODO: Remove this, we want to use functions instead later on(for operator overloading e.t.c)
	BinaryOperator(Operator),

	/// One child
	// TODO: Remove this, we want to use functions instead later on(for operator overloading e.t.c)
	UnaryOperator(Operator),
}

impl NodeKind {
	fn sub_member_access(&mut self) -> Option<&mut SubMemberAccess> {
		match self {
			// NodeKind::ScopeMember { sub_member, .. } => Some(sub_member),
			NodeKind::SubMember   { sub_member, .. } => Some(sub_member),
			// NodeKind::Resource    { sub_member, .. } => Some(sub_member),
			_ => None,
		}
	}
}

pub struct Typer {
	ast: parser::Ast,
	pub nodes: IdVec<Node, NodeId>,
	child_stack: Vec<(TypeHandle, NodeId)>,
	label_types: HashMap<ScopeMemberId, (TypeId, Vec<NodeId>)>,
	index: usize,
}

impl Typer {
	pub fn new(ast: parser::Ast) -> Self {
		Self {
			ast,
			nodes: Default::default(),
			child_stack: Default::default(),
			label_types: Default::default(),
			index: 0,
		}
	}

	pub fn compute(
		&mut self,
		types: &mut Types,
		resources: &Resources,
		scopes: &mut Scopes,
	) -> Result<Option<Dependency>, ()> {
		while let Some(node) = self.ast.nodes.get(self.index) {
			println!("{:?}", self.child_stack);
			for node in self.nodes.iter() {
				print!("{:?}", node.loc);
			}
			println!();

			let node = match node.kind {
				parser::NodeKind::Temporary => panic!("This should have been dealt with in the parser"),
				parser::NodeKind::Member { child_of, id, .. } => {
					// TODO: Change the parsers member system to be more like markers.
					let marker = match (&self.ast.nodes[child_of as usize].kind, id) {
						(parser::NodeKind::If { .. }, 0) => {
							Some(MarkerKind::IfCondition)
						}
						(parser::NodeKind::If { .. }, 1) => None,
						(parser::NodeKind::IfWithElse { .. }, 0) => {
							Some(MarkerKind::IfCondition)
						}
						(parser::NodeKind::IfWithElse { .. }, 1) => {
							Some(MarkerKind::IfElseSeparator)
						}
						(parser::NodeKind::IfWithElse { .. }, 2) => None,
						_ => panic!(),
					};

					if let Some(marker) = marker {
						self.nodes.push(Node {
							loc: node.loc,
							kind: NodeKind::Marker(marker),
							type_: EMPTY_TYPE_ID,
						});
					}

					None
				},
				parser::NodeKind::MemberAccess(_, name) => {
					let (child_type, child_id) = self.child_stack.pop().unwrap();

					// TODO: Check if the child_type is a pointer, if it is, dereference it
					// first. More than one pointer indirection will probably not be allowed
					// though.

					let (offset, handle) = types.sub_member(child_type.id, &name)
						.ok_or_else(|| error_value!(
							node.loc,
							"Type '{}' has no member '{}'",
							types.type_to_string(child_type.id),
							name
						))?;

					let child_node = self.nodes.get_mut(child_id);
					match child_node.kind.sub_member_access() {
						Some(member_access) => {
							member_access.offset(offset, handle.size);
							child_node.type_ = handle.id;
							Some((handle, child_id))
						},
						None => {
							match child_node.kind {
								NodeKind::Constant(ref value) => {
									let buffer = value[offset..offset + handle.size].into();
									child_node.kind = NodeKind::Constant(buffer);

									Some((handle, child_id))
								}
								_ => {
									let id = self.nodes.push(Node {
										kind: NodeKind::SubMember { 
											sub_member: SubMemberAccess::new(offset, handle.size)
										},
										loc: node.loc,
										type_: handle.id,
									});
									Some((handle, id))
								}
							}
						}
					}
				}
				parser::NodeKind::Number(num) => {
					// TODO: Think about if constants should be const folded, and only when
					// they can't they are pushed onto the members list.
					let id = self.nodes.push(Node {
						kind: NodeKind::Constant(SmallVec::from_slice(&(num as i64).to_le_bytes())),
						loc: node.loc,
						type_: U64_TYPE_ID,
					});

					Some((types.handle(U64_TYPE_ID), id))
				}
				parser::NodeKind::EmptyLiteral => {
					let id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Constant(smallvec![]),
						type_: EMPTY_TYPE_ID,
					});

					Some((types.handle(EMPTY_TYPE_ID), id))
				}
				parser::NodeKind::Identifier {
					source: mut id, const_members: ref sub_members, ..
				} => {
					// TODO: Change this entire system to something more similar to
					// MemberAccess
					for sub_member_name in sub_members {
						let member = scopes.member(id);
						match member.kind {
							ScopeMemberKind::Constant(constant_id) => {
								if let Some(scope_inside) = resources.resource(constant_id).scope_inside {
									id = scopes.find_or_create_temp(scope_inside, *sub_member_name)?;
								} else {
									return error!(node, "This value does not contain a scope");
								}
							}
							ScopeMemberKind::UndefinedDependency(_) => {
								return Ok(Some(Dependency::Constant(node.loc, id)));
							}
							_ => { 
								return error!(node, "Can only do a constant member on a constant");
							}
						}
					}

					let member = scopes.member(id);
					match member.kind {
						ScopeMemberKind::LocalVariable | ScopeMemberKind::FunctionArgument => {
							if let Some(type_) = member.type_ {
								let type_handle = types.handle(type_);
								let id = self.nodes.push(Node {
									type_,
									loc: node.loc,
									kind: NodeKind::ScopeMember {
										id,
										// sub_member: SubMemberAccess::new(0, type_handle.size),
									},
								});

								Some((type_handle, id))
							} else {
								return error!(node, "Type is not assigned, is the variable not declared? (This is probably a compiler problem)");
							}
						} 
						ScopeMemberKind::Constant(id) => {
							let resource = resources.resource(id);
							match resource {
								Resource {
									kind: ResourceKind::Value(
									  ResourceValue::Value(type_, 1, ref buffer, ref vec)
									),
									..
								} if vec.len() == 0 => {
									let id = self.nodes.push(Node {
										type_: type_.id,
										loc: node.loc,
										kind: NodeKind::Constant(buffer.clone()),
									});

									Some((*type_, id))
								}
								Resource {
									kind: kind @ ResourceKind::Value(_),
									..
								} if !matches!(
									kind,
									ResourceKind::Value(ResourceValue::Value(_, _, _, _))
								) => {
									return Ok(Some(Dependency::Value(node.loc, id)));
								}
								// TODO: Eventually even function resources will be considered
								// values at the end, just constants pointing to a function id,
								// so then this part will be more consistant and nice! That will
								// also allow for function inlining and even function constant
								// folding. (when a function is constant).
								_ => {
									if let (Some(type_), None) = (resources.resource(id).type_, &resources.resource(id).waiting_on_value) {
										let type_handle = types.handle(type_);
										let id = self.nodes.push(Node {
											type_,
											loc: node.loc,
											kind: NodeKind::Resource {
												id,
												// sub_member: SubMemberAccess::new(0, type_handle.size),
											},
										});

										Some((type_handle, id))
									} else {
										return Ok(Some(Dependency::Value(node.loc, id)));
									}
								}
							}
						}
						ScopeMemberKind::UndefinedDependency(_) => {
							return Ok(Some(Dependency::Constant(node.loc, id)));
						}
						ScopeMemberKind::Label => {
							return error!(node, "This is not a variable, it is a label!");
						}
						ScopeMemberKind::Indirect(_) => { 
							unreachable!("scope.member function should never return Indirect");
						}
					}
				}
				parser::NodeKind::BitCast { .. } => {
					// TODO: Make the order in these things more well defined.
					let (from_type, node_id) = self.child_stack.pop().unwrap();
					let (_, type_id) = self.child_stack.pop().unwrap();

					let type_ = types.handle(
						get_constant_type(self.nodes.get(type_id), types.types.len())?
					);

					self.nodes.get_mut(node_id).type_ = type_.id;

					self.nodes.remove(type_id);
					let node_id = Id::create(node_id.get() - 1);
					
					if from_type.size != type_.size {
						return error!(node, "Cannot bit cast if the types are of different sizes('{}' is {} bytes, '{}' is {} bytes)", types.type_to_string(from_type.id), from_type.size, types.type_to_string(type_.id), type_.size);
					}

					if !is_aligned(type_.align, from_type.align) {
						return error!(node, "Cannot bitcast from lower to higher alignments");
					}

					Some((type_, node_id))
				}
				parser::NodeKind::Resource(id) => {
					if let Some(type_) = resources.resource(id).type_ {
						let type_handle = types.handle(type_);
						let node_id = self.nodes.push(Node {
							kind: NodeKind::Resource {
								id,
								// sub_member: SubMemberAccess::new(0, type_handle.size),
							},
							loc: node.loc,
							type_,
						});
						Some((type_handle, node_id))
					} else {
						return Ok(Some(Dependency::Type(node.loc, id)));
					}
				}
				parser::NodeKind::FunctionCall { ref arg_list, .. } => {
					let arg_list = &self.child_stack[self.child_stack.len() - arg_list.len() ..];
					let (function_pointer_type, _) = 
						self.child_stack[self.child_stack.len() - arg_list.len() - 1];

					let func_type = types.get(function_pointer_type.id);
					if let Type { kind: TypeKind::FunctionPointer { ref args, returns }, .. } 
						= *func_type 
					{
						if arg_list.len() != args.len() {
							return error!(node.loc, "Expected {} arguments, got {}", 
								args.len(), arg_list.len());
						}

						for (wanted, (got_type, got_node)) in args.iter().zip(arg_list) {
							if *wanted != got_type.id {
								return error!(self.nodes.get(*got_node).loc,
									"Expected '{}', got '{}'",
									types.type_to_string(*wanted), 
									types.type_to_string(got_type.id)
								);
							}
						}

						let length = self.child_stack.len() - arg_list.len() - 1;
						self.child_stack.truncate(length);

						let node_id = self.nodes.push(Node {
							loc: node.loc,
							kind: NodeKind::FunctionCall {
								function_type: function_pointer_type.id,
								n_args: args.len(),
							},
							type_: returns,
						});

						Some((types.handle(returns), node_id))
					} else {
						return error!(node, "This is not a function pointer, yet a function call was attemted on it");
					}
				}
				parser::NodeKind::BinaryOperator { operator, .. } => {
					let right = self.child_stack.pop().unwrap();
					let left  = self.child_stack.pop().unwrap();

					if right.0 != left.0 {
						return error!(node, "For now, binary operators cannot have differently typed operands");
					}

					let node_id = self.nodes.push(Node {
						kind: NodeKind::BinaryOperator(operator),
						loc: node.loc,
						type_: right.0.id,
					});

					Some((right.0, node_id))
				}
				parser::NodeKind::UnaryOperator { operator, .. } => {
					let operand = self.child_stack.pop().unwrap();

					let node_id = self.nodes.push(Node {
						kind: NodeKind::UnaryOperator(operator),
						loc: node.loc,
						type_: operand.0.id,
					});

					Some((operand.0, node_id))
				}
				parser::NodeKind::If { .. } => {
					let (body_type, body_id) = self.child_stack.pop().unwrap();

					if body_type.id != EMPTY_TYPE_ID {
						return error!(
							self.nodes.get(body_id).loc,
							"If block cannot evaluate to anything if the if does not have an else"
						);
					}
					
					let (condition_type, condition_id) = self.child_stack.pop().unwrap();

					if condition_type.id != U64_TYPE_ID {
						return error!(
							self.nodes.get(condition_id).loc,
							"If condition has to be a U64 for now until booleans become a thing"
						);
					}

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::If,
						type_: EMPTY_TYPE_ID,
					});

					Some((types.handle(EMPTY_TYPE_ID), node_id))
				},
				parser::NodeKind::IfWithElse { .. } => {
					let (false_body_type, false_body_id) = self.child_stack.pop().unwrap();
					let (true_body_type, true_body_id)   = self.child_stack.pop().unwrap();

					if false_body_type.id != true_body_type.id {
						info!(
							self.nodes.get(true_body_id),
							"If block is '{}'",
							types.type_to_string(true_body_type.id),
						);
						info!(
							self.nodes.get(false_body_id),
							"Else block is '{}'",
							types.type_to_string(false_body_type.id),
						);
						return error!(
							node,
							"If block and else block have to evaluate to the same type"
						);
					}
					
					let (condition_type, condition_id) = self.child_stack.pop().unwrap();

					if condition_type.id != U64_TYPE_ID {
						return error!(
							self.nodes.get(condition_id),
							"If condition has to be a U64 for now until booleans become a thing"
						);
					}

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::IfElse,
						type_: EMPTY_TYPE_ID,
					});

					Some((types.handle(EMPTY_TYPE_ID), node_id))
				},
				parser::NodeKind::LocationMarker => {
					// TODO: Unify this with the marker stuff
					self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Marker(MarkerKind::LoopHead),
						type_: EMPTY_TYPE_ID,
					});

					None
				},
				parser::NodeKind::Loop { .. } => {
					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Loop,
						type_: EMPTY_TYPE_ID,
					});

					Some((types.handle(EMPTY_TYPE_ID), node_id))
				},
				parser::NodeKind::Struct { ref members } => {
					let child_nodes = &self.child_stack[self.child_stack.len() - members.len() ..];
					let type_id = types.insert_struct(
						members.iter().zip(child_nodes).map(|
							((name, _), (type_handle, _))|
						(*name, type_handle.id)
					));
					self.child_stack.truncate(self.child_stack.len() - members.len());

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Struct { n_members: members.len() },
						type_: type_id,
					});

					Some((types.handle(type_id), node_id))
				}
				parser::NodeKind::DeclareFunctionArgument { .. } => panic!("deprecated"),
				parser::NodeKind::Declaration { variable_name, .. } => {
					let value = self.child_stack.pop().unwrap();

					scopes.member_mut(variable_name).type_ = Some(value.0.id);

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Declaration { id: variable_name },
						type_: EMPTY_TYPE_ID,
					});

					Some((types.handle(EMPTY_TYPE_ID), node_id))
				}
				parser::NodeKind::Block { ref contents, label } => {
					let (type_, _) = self.child_stack.pop().unwrap();

					for _ in 1..contents.len() {
						self.child_stack.pop();
					}

					if let Some(label) = label {
						// We own our label, so we can remove it safely
						if let Some((label_type, labels)) = self.label_types.remove(&label) {
							if label_type != type_.id {
								for label in labels {
									let node = self.nodes.get(label);
									info!(node, "Type is '{}'", types.type_to_string(label_type));
								}
								info!(node, "Type is '{}'", types.type_to_string(type_.id));
								return error!(
									node,
									"Block does not return the same type as its label",
								);
							}
						}
					}

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Block { n_members: contents.len() },
						type_: type_.id,
					});

					Some((type_, node_id))
				}
				parser::NodeKind::Skip { label, value } => {
					let (value_type, _) = match value {
						Some(_) => self.child_stack.pop().unwrap(),
						None => {
							(
								types.handle(EMPTY_TYPE_ID),
								self.nodes.push(Node {
									loc: node.loc,
									kind: NodeKind::Constant(smallvec![]),
									type_: EMPTY_TYPE_ID,
								})
							)
						},
					};

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Skip { label },
						type_: EMPTY_TYPE_ID,
					});

					if let Some((label_type, labels)) = self.label_types.get_mut(&label) {
						if value_type.id != *label_type {
							return error!(node, "Incompatible types, block doesn't return this type");
						}

						labels.push(node_id);
					} else {
						self.label_types.insert(
							label, 
							(value_type.id, vec![node_id]),
						);
					}

					Some((types.handle(EMPTY_TYPE_ID), node_id))
				},
				parser::NodeKind::GetType(_) =>
					Some(self.child_stack.pop().unwrap()),
				parser::NodeKind::TypeFunctionPointer { ref arg_list, .. } => {
					let (_, return_node) = self.child_stack.pop().unwrap();
					let returns = get_constant_type(self.nodes.get(return_node), types.types.len())?;
					self.nodes.remove(return_node);

					// TODO: Remove this once the rust borrow checker isn't dumb here.
					let args = self.child_stack[self.child_stack.len() - arg_list.len() ..]
						.iter()
						.map(|&(_, arg_id)|
							get_constant_type(self.nodes.get(arg_id), types.types.len())
						)
						.collect::<Result<Vec<_>, _>>()?;

					let type_id =
						types.insert(Type::new(TypeKind::FunctionPointer { args, returns }));

					self.nodes.pop_n(arg_list.len());

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Constant((type_id.get() as u64).to_le_bytes().into()),
						type_: TYPE_TYPE_ID,
					});

					Some((types.handle(TYPE_TYPE_ID), node_id))
				}
				parser::NodeKind::TypeStruct { ref args } => {
					// Silly borrow checker!
					let n_types = types.types.len();
					let arg_types = self.child_stack[self.child_stack.len() - args.len() ..]
						.iter()
						.zip(args)
						.map(|(&(_, arg_id), &(name, _))|
							Ok((name, get_constant_type(self.nodes.get(arg_id), n_types)?))
						);

					let type_id = types.try_insert_struct(arg_types)?;

					self.nodes.pop_n(args.len());
					let length = self.child_stack.len() - args.len();
					self.child_stack.truncate(length);

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Constant((type_id.get() as u64).to_le_bytes().into()),
						type_: TYPE_TYPE_ID,
					});

					Some((types.handle(TYPE_TYPE_ID), node_id))
				}
				parser::NodeKind::TypePointer(_) => {
					let (_, child_id) = self.child_stack.pop().unwrap();
					let type_id = get_constant_type(self.nodes.get(child_id), types.types.len())?;
					self.nodes.remove(child_id);
					let type_id = types.insert(Type::new(TypeKind::Pointer(type_id)));

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Constant((type_id.get() as u64).to_le_bytes().into()),
						type_: TYPE_TYPE_ID,
					});

					Some((types.handle(TYPE_TYPE_ID), node_id))
				}
				parser::NodeKind::TypeEmpty => {
					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Constant((EMPTY_TYPE_ID.get() as u64).to_le_bytes().into()),
						type_: TYPE_TYPE_ID,
					});

					Some((types.handle(TYPE_TYPE_ID), node_id))
				}
				parser::NodeKind::TypeBufferPointer(_) => {
					let (_, child_id) = self.child_stack.pop().unwrap();
					let type_id = get_constant_type(self.nodes.get(child_id), types.types.len())?;
					self.nodes.remove(child_id);
					let type_id = types.insert(Type::new(TypeKind::BufferPointer(type_id)));

					let node_id = self.nodes.push(Node {
						loc: node.loc,
						kind: NodeKind::Constant((type_id.get() as u64).to_le_bytes().into()),
						type_: TYPE_TYPE_ID,
					});

					Some((types.handle(TYPE_TYPE_ID), node_id))
				}

				parser::NodeKind::StackClone(_) => todo!(),
				parser::NodeKind::HeapClone(_) => todo!(),
			};

			if let Some(node) = node {
				self.child_stack.push(node);
			}

			self.index += 1;
		}

		Ok(None)
	}
}

/// Removes a node and returns a type id instead.
pub fn get_constant_type(node: &Node, n_types: usize) -> Result<TypeId, ()> {
	if node.type_ != TYPE_TYPE_ID {
		return error!(node.loc, "Node is not type expression");
	}

	match node.kind {
		NodeKind::Constant(ref value) => {
			use std::convert::TryInto;
			
			let id = usize::from_le_bytes(value.as_slice().try_into().unwrap());

			if id >= n_types {
				return error!(node.loc, "This is a type, but the id it contains is not valid");
			}

			Ok(TypeId::create(id as u32))
		}
		_ => return error!(node.loc, "Type expression node is not constant, it's {:?}", node.kind),
	}
}

/// An access way to a sub member. This generalises;
/// * Struct member access.
/// * Dereferencing.
/// * Pointer offsets.
#[derive(Debug)]
pub struct SubMemberAccess {
	pub offsets: Vec<usize>,
	pub value_offset: usize,
	pub last_size: usize,
}

impl SubMemberAccess {
	fn new(offset: usize, size: usize) -> Self {
		Self {
			offsets: Vec::new(),
			value_offset: offset,
			last_size: size,
		}
	}

	fn dereference(&mut self, next_size: usize) {
		assert_eq!(self.last_size, 8);

		self.offsets.push(self.value_offset);
		self.value_offset = 0;
		self.last_size = next_size;
	}

	fn offset(&mut self, offset: usize, next_size: usize) {
		self.value_offset += offset;
		self.last_size = next_size;
	}
}
