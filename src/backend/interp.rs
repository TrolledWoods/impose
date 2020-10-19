use crate::align::*;
use crate::intrinsic::*;
use crate::parser::MarkerKind;
use crate::resource::*;
use crate::scopes::*;
use crate::types::*;

use std::alloc::{alloc, dealloc, Layout};

pub type Value = smallvec::SmallVec<[u8; 8]>;

#[derive(Debug)]
struct Stack {
    buffer: *mut u8,
    buffer_max: *mut u8,
    head: *mut u8,
    member_sizes: Vec<usize>,
}

impl Stack {
    fn new() -> Self {
        let stack_layout = Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap();
        let stack_ptr: *mut u8 = unsafe { alloc(stack_layout) };

        Stack {
            buffer: stack_ptr,
            buffer_max: unsafe { stack_ptr.add(STACK_SIZE) },
            head: stack_ptr,
            member_sizes: Vec::new(),
        }
    }

    fn push_zero(&mut self) {
        self.push_uninit(0);
    }

    fn push(&mut self, value: *const u8, size: usize) -> *mut u8 {
        let buffer = self.push_uninit(size);

        // SAFETY: This is safe even if the size is zero, because push_uninit will always
        // return a properly aligned, non-null pointer and that is all that is required for
        // copy to be safe when the size is 0.
        unsafe {
            std::ptr::copy(value, buffer, size);
        }

        buffer
    }

    /// Allocates a value of size bytes and returns the pointer to it.
    /// Intended to be used when you want to initialize the data in the buffer
    /// later.
    ///
    /// Returns a dangling pointer with STACK_ALIGN alignment if the size is zero
    fn push_uninit(&mut self, size: usize) -> *mut u8 {
        self.member_sizes.push(size);
        if size == 0 {
            return STACK_ALIGN as *mut u8;
        }

        assert!(
            self.head as usize + size < self.buffer_max as usize,
            "Stack overflow"
        );

        let pos = self.head;

        unsafe {
            self.head = self.head.add(to_aligned(STACK_ALIGN, size));
        }

        pos
    }

    /// Makes sure there is enough space for size elements, and returns the head of the
    /// stack.
    ///
    /// SAFETY: Make sure to not use the storage after any writes have happened to the stack,
    /// such as push. push_uninit(as long as you don't write it yourself) and pop are fine though.
    fn temp_storage(&mut self, size: usize) -> *mut u8 {
        assert!(
            self.head as usize + size < self.buffer_max as usize,
            "Stack overflow"
        );

        self.head
    }

    fn pop(&mut self) -> (*const u8, usize) {
        let size = self.member_sizes.pop().unwrap();
        if size == 0 {
            return (std::ptr::NonNull::dangling().as_ptr(), 0);
        }

        unsafe {
            self.head = self.head.sub(to_aligned(STACK_ALIGN, size));

            print!("Bytes: ");
            for off in 0..size {
                print!("{} ", *self.head.add(off));
            }

            (self.head, size)
        }
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        unsafe {
            dealloc(
                self.buffer,
                Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap(),
            );
        }
    }
}

const STACK_SIZE: usize = 2048;
const STACK_ALIGN: usize = 16;

pub struct Interpreter<'a> {
    stack: Stack,
    locals_stack: Stack,
    // TODO: Make the locals represented by their idex in the locals array so that this can be done
    // more efficiently.
    locals: Vec<(ScopeMemberId, *mut u8)>,
    code: Vec<(&'a Ast, usize)>,
}

impl<'a> Interpreter<'a> {
    pub fn new() -> Self {
        Interpreter {
            stack: Stack::new(),
            locals_stack: Stack::new(),
            locals: Vec::new(),
            code: Vec::new(),
        }
    }

    fn get_local(&self, local_id: ScopeMemberId) -> *mut u8 {
        let &(_, ptr) = self
            .locals
            .iter()
            .rev()
            .find(|&&(id, _)| id == local_id)
            .unwrap();
        ptr
    }

    pub fn resume(
        &mut self,
        resources: &'a Resources,
        types: &Types,
        scopes: &Scopes,
    ) -> Result<Value, Dependency> {
        let (ast, mut node_id) = self.code.pop().expect("Nothing to resume");

        while let Some(node) = ast.nodes.get(node_id) {
            node_id += 1;

            match node.kind {
                NodeKind::Marker(MarkerKind::IfCondition(_, label_id)) => {
                    // The size of a boolean is 1.
                    let (condition, _size) = self.stack.pop();
                    // assert_eq!(size, 1);

                    if unsafe { *condition } == 0 {
                        node_id = *ast.label_map.get(&label_id).unwrap();
                    }
                }
                NodeKind::Marker(MarkerKind::IfElseTrueBody {
                    contains: _,
                    true_body_label: _,
                    false_body_label,
                }) => {
                    node_id = *ast.label_map.get(&false_body_label).unwrap();
                }
                NodeKind::Marker(MarkerKind::LoopHead(_)) => {}
                NodeKind::MemberAccess { offset, size } => {
                    let (value, length) = self.stack.pop();
                    assert!(offset + size <= length);
                    self.stack.push(unsafe { value.add(offset) }, size);
                }
                NodeKind::Constant(ref buffer) => {
                    self.stack.push(buffer.as_ptr(), buffer.len());
                }
                NodeKind::IntrinsicTwo(intrinsic_kind) => {
                    let (right, right_len) = self.stack.pop();
                    let (left, left_len) = self.stack.pop();
                    let mut output = 0;
                    run_intrinsic_two(
                        intrinsic_kind,
                        &mut output,
                        unsafe { std::slice::from_raw_parts(left, left_len) },
                        unsafe { std::slice::from_raw_parts(right, right_len) },
                    );

                    self.stack.push(
                        &output as *const u64 as *const u8,
                        types.handle(node.type_).size,
                    );
                }
                NodeKind::ScopeMemberReference(member_id) => match scopes.member(member_id).kind {
                    ScopeMemberKind::LocalVariable => {
                        let bytes = (self.get_local(member_id) as usize).to_le_bytes();
                        self.stack.push(bytes.as_slice().as_ptr(), 8);
                    }
                    ref kind => panic!("Unhandled identifier kind {:?}", kind),
                },
                NodeKind::Identifier(member_id) => match scopes.member(member_id).kind {
                    ScopeMemberKind::LocalVariable => {
                        let ptr = self.get_local(member_id);
                        let size = types.handle(scopes.member(member_id).type_.unwrap()).size;

                        self.stack.push(ptr, size);
                    }
                    ref kind => panic!("Unhandled identifier kind {:?}", kind),
                },
                NodeKind::BitCast => {}
                NodeKind::Assign => {
                    let (value, value_len) = self.stack.pop();
                    let (pointer, pointer_len) = self.stack.pop();

                    if value_len > 0 {
                        assert_eq!(pointer_len, 8);

                        unsafe {
                            std::ptr::copy(value, *(pointer as *mut *mut u8), value_len);
                        }

                        self.stack.push(value, value_len);
                    }
                }
                NodeKind::Resource(id) => {
                    let resource = resources.resource(id);
                    match resource.kind {
                        ResourceKind::Done(ref value, ref pointers) => {
                            let mut value_copy = value.clone();

                            for &(sub_offset, sub_id, _) in pointers {
                                match resources.resource(sub_id).kind {
                                    ResourceKind::Done(ref sub_value, ref sub_pointers) => {
                                        if sub_pointers.len() > 0 {
                                            panic!(
                                                "Cannot copy a resource with recursive subpointers"
                                            );
                                        }

                                        value_copy[sub_offset..sub_offset + 8].copy_from_slice(
                                            &(sub_value.as_ptr() as usize).to_le_bytes(),
                                        );
                                    }
                                    _ => {
                                        todo!(
                                            "We can't currently deal with non-finished resources"
                                        );
                                    }
                                }
                            }

                            self.stack.push(value_copy.as_ptr(), value_copy.len());
                        }
                        _ => {
                            todo!("We can't currently deal with non-finished resources");
                        }
                    }
                }
                NodeKind::FunctionCall(type_id) => {
                    let mut args = Vec::new();
                    let type_ = types.get(type_id);
                    let return_type = match type_.kind {
                        TypeKind::FunctionPointer {
                            args: ref arg_types,
                            returns,
                        } => {
                            for &arg_type in arg_types.iter().rev() {
                                let (arg, size) = self.stack.pop();
                                let arg_type_handle = types.handle(arg_type);
                                assert_eq!(size, arg_type_handle.size);
                                args.push(arg);
                            }
                            returns
                        }
                        _ => unreachable!(),
                    };

                    let (func_id, id_len) = self.stack.pop();
                    assert_eq!(id_len, 8);
                    let func_id = unsafe { *(func_id as *mut usize) };

                    match resources.functions.get(func_id) {
                        Some(FunctionKind::ExternalFunction {
                            func: _,
                            n_arg_bytes: _,
                            n_return_bytes: _,
                        }) => todo!(),
                        Some(FunctionKind::Function(ast)) => {
                            let returns = self.interpret(resources, types, scopes, ast, &args)?;
                            assert_eq!(returns.len(), types.handle(return_type).size);
                            self.stack.push(returns.as_ptr(), returns.len());
                        }
                        None => panic!("Not a valid function"),
                    }
                }
                NodeKind::Dereference => {
                    let (pointer, pointer_len) = self.stack.pop();
                    assert_eq!(pointer_len, 8);

                    self.stack.push(
                        unsafe { *(pointer as *mut *mut u8) },
                        types.handle(node.type_).size,
                    );
                }
                NodeKind::If(_) => {}
                NodeKind::IfWithElse { end_label: _ } => {}
                NodeKind::Loop(head, _) => node_id = *ast.label_map.get(&head).unwrap(),
                NodeKind::Struct => match types.get(node.type_).kind {
                    TypeKind::Struct { ref members } => {
                        let handle = types.handle(node.type_);
                        let temp = self.stack.temp_storage(handle.size);

                        for &(_, offset, member_type_handle) in members.iter().rev() {
                            let (value_buffer, value_size) = self.stack.pop();
                            assert_eq!(value_size, member_type_handle.size);

                            unsafe {
                                std::ptr::copy(
                                    value_buffer,
                                    temp.add(offset),
                                    member_type_handle.size,
                                );
                            }
                        }

                        self.stack.push(temp, handle.size);
                    }
                    _ => unreachable!("A Struct node has to have to type of struct"),
                },
                NodeKind::Declaration { variable_name } => {
                    let ptr = self.get_local(variable_name);
                    let size = types
                        .handle(scopes.member(variable_name).type_.unwrap())
                        .size;
                    let (pointer, pointer_size) = self.stack.pop();
                    assert_eq!(size, pointer_size);

                    unsafe {
                        std::ptr::copy(pointer, ptr, size);
                    }

                    self.stack.push_zero();
                }
                NodeKind::Block {
                    ref contents,
                    label: _,
                } => {
                    let (return_value, return_value_length) = self.stack.pop();
                    for _ in contents[1..].iter() {
                        self.stack.pop();
                    }

                    self.stack.push(return_value, return_value_length);
                }
                NodeKind::Skip { label } => {
                    node_id = *ast.label_map.get(&label).unwrap();
                }
            }
        }

        for _ in ast.locals.all_locals.iter() {
            self.locals.pop();
            self.locals_stack.pop();
        }

        let (buffer_raw_ptr, buffer_raw_len) = self.stack.pop();
        let buffer = unsafe { std::slice::from_raw_parts(buffer_raw_ptr, buffer_raw_len).into() };

        Ok(buffer)
    }

    pub fn interpret(
        &mut self,
        resources: &'a Resources,
        types: &Types,
        scopes: &Scopes,
        ast: &'a Ast,
        arguments: &[*const u8],
    ) -> Result<Value, Dependency> {
        self.code.push((ast, 0));

        for (i, &local_var_id) in ast.locals.all_locals.iter().enumerate() {
            let member = scopes.member(local_var_id);
            let type_handle = types.handle(member.type_.unwrap());
            let local = self.locals_stack.push_uninit(type_handle.size);

            if let Some(arg) = arguments.get(i) {
                unsafe {
                    std::ptr::copy(*arg, local, type_handle.size);
                }
            }

            self.locals.push((local_var_id, local));
        }

        self.resume(resources, types, scopes)
    }
}
