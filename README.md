# Impose
A silly little compiler for a programming language.

Except it's not a compiler right now, it's just an interpreter. Compilation will come in the future
though! (with full compile time execution using the interpreter)

## Running
For now, this compiler only runs the ``test.im`` file. There is no command line argument
handling yet.

So just call ``cargo run`` and it will run the code in the ``test.im``.

## Hello world
Because every language needs a hello world.
```rust
print("Hello, World!\n");
```

## Syntax
```rust
// This is a comment
// v-- and this is a declaration.
x := 5;

// We may want to print what our variable 'x' is.
// (print_num and print are temporary, they will be replaced with something else in the future)
print_num(x); // "5"
print("\n");  // new line

// All integers are 64 bits by default. If you want a 32 bit integer, you'll have to do some
// casting that is described further down.

// Most things in impose are an expression. Assignments are also expressions that return the
// right hand side, just like in C.
y := x = 2;

// You can add things together, subtract, multiply and divide.
// It respects order of operations, like you'd expect.
y = x + 2 * 5 * x;

// Code blocks are defined with curly brackets. If the last expression does not have a trailing
// semicolon, the block returns that expression.
x = {
	// Each block has its own scope, so this variable
	// cannot be accessed from the outside.
	hello := 5;

	//       v-- no trailing semicolon, so this expression is what the block will evaluate to.
	hello * y
};

// Sometimes you want to organise things. In that case, you can make a struct.
position := struct {
	x: x + 1,
	y: y * 2, 
	z: 50, // This last comma is optional
};

// Let's print our position
print("Position = { x: ");
print_num(position.x);
print(", y: ");
print_num(position.y);
print(", z: ");
print_num(position.z);
print(" }\n");

// Outputs "Position = { x: 111, y: 44, z: 50 }"

// That's kindof a pain. So let's make a function to print structs for us!
// This function will be stored in a local variable for now, I'll show you how you'd
// actually define a function in a bit.
print_vector := |vector: { x: U64, y: U64, z: U64 }| {
	print("{ x: ");
	print_num(vector.x);
	print(", y: ");
	print_num(vector.y);
	print(", z: ");
	print_num(vector.z);
	print(" }\n");
};

// That was a lot of syntax, so let's break it down.
// 
// Functions are defined with "||", putting the argument list inside. Since this is a typed language,
// each argument needs a type. Defining types is very similar to defining values, but with a few
// differences. I'll show you more about that later.
//
// Here are some more functions to help you get the jist of things:
add_one := |num: U64| num + 1;
print("3 + 1 = ");
print_num(add_one(3)); // 4
print("\n5 + 1 = ");
print_num(add_one(5)); // 6
print("\n");

divide_numbers := |num1: U64, num2: U64| num1 / num2;

print("5 / 2 = ");
print_num(divide_numbers(5, 2)); // 2
print("\n2 / 1 = ");
print_num(divide_numbers(add_one(0), 1)); // 1
print("\n");

// Now that we've covered some of the basics, I want to introduce the biggest feature of this
// language so far; constants!
//
// Constants in this language are defined similarly to declaring variables, except you use
// '::' instead of ':='.
MY_CONSTANT :: 5;
print("MY_CONSTANT = ");
print_num(MY_CONSTANT); // 5
print("\n");

// Constants do not have to be defined before they are used though.
print("MY_UNORDERED_CONSTANT = ");
print_num(MY_UNORDERED_CONSTANT); // 5
print("\n");
MY_UNORDERED_CONSTANT :: 5;

// Constants can have any expression you can think of inside them. The sky is the limit! In fact,
// you could wrap this whole program in a constant and it works just fine.
// Internally to the compiler, the program is infact already a constant.

// Let's go through some common programming language features and see how they are done
// using constants.

// Functions
my_function :: |x: MyType| {
	print("Hello from my function!\n");
};

// Types (I'll talk about this syntax a bit later)
MyType :: type { x: U64, y: U64 };

my_function(struct { x: 50, y: 20 });


// Now that the big features have been covered, let's go back to some smaller things.
// Namely; pointers!
// Pointers are defined just like in c: & to point to a value, and * to dereference a pointer.
number := 4;

print("number = ");
print_num(number);
print("\n");
// Prints "number = 4"

number_pointer := &number;
*number_pointer = 2;

print("number = ");
print_num(number);
print("\n");
// Prints "number = 2"

// The real banger is that constants can contain pointers.
MY_POINTER_CONSTANT :: {
	x := 4;
	x = x + 5;
	&x
};

print("*MY_POINTER_CONSTANT = ");
print_num(*MY_POINTER_CONSTANT);
print("\n");
// Prints "*MY_POINTER_CONSTANT = 9"

// This is not magic, and it can in some cases be very slow.
// Essentially, whenever you create a constant the compiler copies the values
// the pointers point to into another hidden constant. Then, whenever you
// access a constant it does a deep copy, copying every hidden constant onto the stack.
// This is inefficient, so in the future you'll have to explicitly state that you want
// a deep copy when it happens.

// Performance aside, this is very powerful, because it allows you to do literally anything
// at compile time, and pass any state you wantyou want  to runtime.

// On to something else!
//
//
// You may have seen this line before:
// 
// MyType :: type { x: U64, y: U64 };
// 
// The "type" keyword here indicates a type expression. i.e., an expression that creates a type.
// Type expressions can be put anywhere.

type_variable := type { x: U64, y: U64 };

// This type_variable now contains the id for the type { x: U64, y: U64 }.
// However, type expressions can only contain constant values, so this does not compile,
// even though, type_variable contains a type id:
//
// other_type_var := type { x: type_variable, y: U64 };
//
// This can be solved by making type_variable a constant instead.

TypeConstant :: type { x: U64, y: U64 };

// Now this line works
other_type_var := type { x: TypeConstant, y: U64 };

// In some cases type expressions are implicit, for example in function declarations.
//                                 v-v-v-v-v-v-v-v-v-v-v-v-v-v--- this is a type expression
some_random_function :: |argument: { x: U64, y: { okay: U64 }}| argument.x + argument.y.okay;

// Type expressions aren't very full featured at the moment, but there are a few things you
// can do with them:

// The type of a type id
Type;

// The type of a 64 bit unsigned integer.
U64;

// The type of a 32 bit unsigned integer.
U32;

// This is the type of a struct with the specified field names, and types of those fields.
// The order here matters! If the fields are in a different order, the type will be different.
type { field_1: Type, field_2: Type, field_3: Type };

// The type of a function. It's not denoted with ||, but instead (), to avoid ambiguity.
// This also means that parenthesis do not exist in type expressions, but that's fine because
// operators do not exist either :D
//
type (Type, U64, U32);

// If you need a return type, you can optionally add -> followed by the type the function returns.
// The return types of function declarations are inferred for now.
type (Type, U64, U32) -> U32;

// Now that all the type expressions have been covered, let's talk about casting.
// Right now there is only one type of cast, ``bit_cast``.
// It has quite a strange syntax(that is temporary);
// bit_cast TypeExpression (value_to_cast);
//
// All it does is tell the compiler to pretend a value is of a different type.
// The compiler can't do that if the types are different sizes though, so if they are different
// sizes you will get a compile error.
//
// An example:

// Remember the position variable from earlier?
a_casted_struct := bit_cast { a: U64, b: U64, c: U64 } (position);
print("a_casted_struct = { a: ");
print_num(a_casted_struct.a);
print(", b: ");
print_num(a_casted_struct.b);
print(", c: ");
print_num(a_casted_struct.c);
print(" }\n");

// The output from this depends on the way the structs are laid out in memory. For now, structs
// are organized in exactly the same way C organizes them, but that might change in the future.

// We could also use bit_cast to print the value of a pointer.
print_num(bit_cast U64 (&0)); // Outputs the memory address of our pointer.
print("\n");

// In conclusion, bit_cast is powerful but hard to use and easy to mess up with, so if there
// is a way to avoid using it that way is probably better.

// And that's it for now! There will be more later, or this example might be a little out of date.
```
