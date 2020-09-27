# Impose
A silly little compiler for a programming language.

Except it's not a compiler right now, it's just an interpreter. Compilation will come in the future
though! (with full compile time execution using the interpreter)

## Running
If no command line arguments are given, it will test the folder named 'tests' where the command
is called. This is not final behaviour, it is only there for testing against regressions
when working on the compiler.

If you want to compile a specific program, just type ``cargo run file_name.im`` and it will run
``file_name.im``.

## Hello world
Because every language needs a hello world.
```rust
print("Hello, World!\n");
```

## Examples
Check out the ``tests/`` directory for lots of tests which will show you how features work.

## Syntax
Because the syntax changes so frequently, I am not going to write anything about it. Check out
the examples.
