# nom++, [nom](https://github.com/Geal/nom) for methods


nom is a parser combinators library written in Rust. Its goal is to provide tools to build safe parsers without compromising the speed or memory consumption. To that end, it uses extensively Rust's *strong typing*, *zero copy* parsing, *push streaming*, *pull streaming*, and provides macros and traits to abstract most of the error prone plumbing.

nom++ is an extension of nom that allows you to create parsing [methods](http://stackoverflow.com/questions/155609/difference-between-a-method-and-a-function). The goal is for method-making macros have parity with the function-making macros that are already in nom. 

## Features

Here are the current and planned features, with their status:
- [ ] ~~Re-implement all of the macros in nom's macros.rs to either call methods or create methods~~
- [ ] Write tests for all of the new ways you can create and call methods and functions

## How ***NOT*** to use it
####Since I first wrote this I changed how methods work a bunch of times. The new way to use them is really simple and I'll update this README with how to use them when I get a chance. Everything after this line is out of date.

First read up on how to use [nom](https://github.com/Geal/nom) because the basics are the same. The differences come in creating methods and then in macros that call more than one method inside a method.

In nom you used `named!` to create a parser function:
```rust
named!(<&str, &str>, take4, take!(4));
```
In nom++ you use `method!`, and supply it with the type of self and the self object (a macro can't declare the self object on it's own):
```rust
impl<'a> SomeStruct<'a> {
  //      --self's type---                     -self-
  method!(<&SomeStruct<'a>, &str, &str>, take4, self, take!(4));
}
```
*TODO: put output of macro here*

Now you can call that method from another method by specifying `object.method` like this:
```rust
impl<'a> SomeStruct<'a> {
  method!(<&SomeStruct<'a>, &str, &str>, take4, self, take!(4));
  //                                                            -object.method-
  method!(<&SomeStruct<'a>, &str, &str>, call_take4, self, call_m!(self.take4));
}
```
Some macros produce code that calls multiple methods within the same method. This turns out to be difficult because the first call will borrow the self reference for the entire method regardless of what scope the first or second call is in. In these macros the self object is wrapped in a RefCell, then the method is called from a borrowed RefMut which only borrows the wrapped object for the scope it is in. In order to pass the RefCell down to macros within macros special syntax is needed. You first need to declare the object all the methods will be called on (usually `self`). Then any macro that eventually contains a method call needs to be invoked with a double bang, `!!`.
```rust
method!(<&SomeStruct, &str, &str>, tag_abcd, self, tag!("abcd"));
method!(<&SomeStruct, &str, &str>, tag_efgh, self, tag!("efgh"));
method!(<&SomeStruct, &str, &str>, take4, self, take!(4));
method!(<&SomeStruct, &str, &str>, chain_parsers, self, 
  alt_m!(self, // <--- specify your object here for multiple method-calling macros
    complete_m!!(tag_abcd) | // <--- instead of here
    complete_m!!(tag_efgh) |
    complete_m!!(take4)
  )
);
```
`alt_m` takes `self` and wrapps it in a RefCell. Then, because the child macros are called with `!!` it passes the cell to 
to them. The child macros use the passed in RefCell to get a mutable borrow of self and call their methods (`tag_abcd`, `tag_efgh`, or `take4`) on it. Child macros can be nested more than once and all parent macros that eventually end in a method call need to be called with `!!`:
```rust
method!(<&SomeStruct, &str, &str>, tag_foo, self, tag!("foo"));
method!(<&SomeStruct, &str, &str>, tag_bar, self, tag!("bar"));
method!(<&SomeStruct, &str, &str>, chain_parsers, self, 
  alt_m!(self,
    complete_m!!(chain_m!!(tag_abcd ~ tagged: alt_m!!(tag_foo | tag_bar),||{tagged})) |
    complete!(chain!(tag!("yes") ~ tag!("please"),||{"polite"}))
    // Note no '!!' is used above because none of the child macros call a method
  )
);
```
