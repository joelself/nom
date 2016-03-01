//! Method macro combinators
//!
//! These macros make parsers as methods of structs
//! and that can take methods of structs to call
//! as parsers.
//!
//! There is a trick to make them easier to assemble,
//! combinators are defined like this:
//!
//! ```ignore
//! macro_rules! tag (
//!   ($i:expr, $inp: expr) => (
//!     {
//!       ...
//!     }
//!   );
//! );
//! ```
//!
//! But when used as methods in other combinators, are used
//! like this:
//!
//! ```ignore
//! method!(my_function<Parser<'a> >, self, tag!("abcd"));
//! ```
//!
//! Internally, other combinators will rewrite
//! that call to pass the input as second argument:
//!
//! ```ignore
//! macro_rules! method (
//!   ($name:ident<$a:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
//!     fn $name( $self_: $a, i: &[u8] ) -> $crate::IResult<&[u8], &[u8]> {
//!       $submac!(i, $($args)*)
//!     }
//!   );
//! );
//! ```
//! 
//! The `method!` macro is similar to the `named!` macro in the macros module.
//! While `named!` will create a parser function, `method!` will create a parser
//! method on the struct it is defined in.
//!
//! Compared to the `named!` macro there are a few differences in how they are
//! invoked. A `method!` invocation always has to have the type of `self`
//! declared and it can't be a reference due to Rust's borrow lifetime
//! restrictions:
//! ```ignore
//! //                  -`self`'s type-
//! method!(method_name<  Parser<'a> >, ...);
//! ```
//! `self`'s type always comes first.
//! The next difference is you have to input the self struct. Due to Rust's
//! macro hygiene the macro can't declare it on it's own.
//! ```ignore
//! //                                                 -self-
//! method!(method_name<Parser<'a>, &'a str, &'a str>, self, ...);
//! ```
//! When making a parsing struct with parsing methods, due to the static borrow
//! checker,calling any parsing methods on self (or any other parsing struct)
//! will cause self to be moved for the rest of the method.To get around this
//! restriction all self is moved into the called method and then the called
//! method will return self to the caller.
//! 
//! To call a wrapped struct you need to use the `call_rc!` macro. For example:
//! ```ignore
//! struct<'a> Parser<'a> {
//!   parsed: &'a str,
//! }
//! impl<'a> Parser<'a> {
//!   // Constructor omitted for brevity
//!   method!(take4<&Parser<'a>, &'a str, &'a str>, self, take!(4));
//!   method!(caller<&Parser<'a>, &'a str, &'a str>, self, [(self, rcs)]), call_rc!(rcs.take4));
//! }
//! ```
//! Notice in the definition of `take4` no structs and wrapped names are specified
//! because they aren't needed since it won't be calling any methods. The `caller`
//! method however does call a method on the `self` struct so it specifies `self`
//! as a struct to be wrapped and `rcs` as the wrapped name. Later, we make use of
//! the `call_rc!` macro to call the `take4` method on the wrapped `self` struct, 
//! `rcs`.
//! 
//! More complicated combinations still mostly look the same as their `named!`
//! counterparts:
//! ```ignore
//!    method!(pub simple_chain<&mut Parser<'a>, &'a str, &'a str>, self,
//!      chain!(
//!             call_rc!(rcs.tag_abc)      ~
//!             call_rc!(rcs.tag_def)      ~
//!             call_rc!(rcs.tag_ghi)      ~
//!       last: call_rc!(rcs.simple_peek)  ,
//!        ||{rcs.borrow_mut().parsed = last; last}
//!      )
//!    );
//! ```
//!
//! The four additions to method definitions remeber are:
//! 1. Specify `self`'s type
//! 2. Pass `self` to the macro
//! 3. Specify structs that need to be wrapped and the name of their wrapper
//! 4. Call parser methods using the `call_rc!` macro.

/// Makes a method from a parser combination
///
/// The must be set up because the compiler needs
/// the information
///
/// ```ignore
/// method!(my_function<Parser<'a> >( &[u8] ) -> &[u8], tag!("abcd"));
/// // first type parameter is `self`'s type, second is input, third is output
/// method!(my_function<Parser<'a>, &[u8], &[u8]>,     tag!("abcd"));
/// //prefix them with 'pub' to make the methods public
/// method!(pub my_function<Parser<'a>,&[u8], &[u8]>, tag!("abcd"));
/// ```
#[macro_export]
macro_rules! method (
  // Non-public immutable self
  ($name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty,$e:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i, $o, $e>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>)  {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i,$o> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
  ($name:ident<$a:ty,$o:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name<'a>( mut $self_: $a, i: &'a[u8] ) -> ($a, $crate::IResult<&'a [u8], $o, u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  ($name:ident<$a:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name( mut $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], &[u8], u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  // Public mutable self
  (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      pub fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty,$e:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i, $o, $e>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name( mut $self_: $a,i: $i ) -> ($a, $crate::IResult<$i,$o,u32>)  {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  (pub $name:ident<$a:ty,$o:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name<'a>( mut $self_: $a, i: &'a[u8] ) -> ($a, $crate::IResult<&'a [u8], $o, u32>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );

  ($name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i,$o> {
      $submac!(i, $($args)*)
    }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i, $o> {
      $submac!(i, $($args)*)
    }
  );
  (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i,$o> {
      $submac!(i, $($args)*)
    }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i, $o> {
      $submac!(i, $($args)*)
    }
  );
  (pub $name:ident<$a:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a, i: &[u8] ) -> $crate::IResult<&[u8], $o> {
      $submac!(i, $($args)*)
    }
  );
);

/// Used to called methods on non-mutable structs wrapped in `RefCell`s
#[macro_export]
macro_rules! call_rc (
  ($i:expr, $cell:ident.$method:ident) => ( { let res = $cell.borrow_mut().$method( $i ); res } );
  ($i:expr, $cell:ident.$method:ident, $($args:expr),* ) => ( { let res = $cell.borrow_mut().$method( $i, $($args),* ); res } );
);

/// emulate function currying for method calls on non-mutable structs wrapped in `RefCell`s: 
/// `apply!(cell.my_function, arg1, arg2, ...)` becomes `cell.borrow_mut().my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_rf (
  ($i:expr, $cell:ident.$method:ident, $($args:expr),* ) => ( { let res = $cell.borrow_mut().$method( $i, $($args),* ); res } );
);

#[cfg(test)]
mod tests {
  use internal::IResult::*;

  // reproduce the tag_s and take_s macros, because of module import order
  macro_rules! tag_s (
    ($i:expr, $tag: expr) => (
      {
        let res: $crate::IResult<_,_> = if $tag.len() > $i.len() {
          $crate::IResult::Incomplete($crate::Needed::Size($tag.len()))
        //} else if &$i[0..$tag.len()] == $tag {
        } else if ($i).starts_with($tag) {
          $crate::IResult::Done(&$i[$tag.len()..], &$i[0..$tag.len()])
        } else {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::TagStr, $i))
        };
        res
      }
    );
  );

  macro_rules! take_s (
    ($i:expr, $count:expr) => (
      {
        let cnt = $count as usize;
        let res: $crate::IResult<_,_> = if $i.chars().count() < cnt {
          $crate::IResult::Incomplete($crate::Needed::Size(cnt))
        } else {
          let mut offset = $i.len();
          let mut count = 0;
          for (o, _) in $i.char_indices() {
            if count == cnt {
              offset = o;
              break;
            }
            count += 1;
          }
          $crate::IResult::Done(&$i[offset..], &$i[..offset])
        };
        res
      }
    );
  );

  struct Parser<'a> {
    bcd: &'a str,
  }

  impl<'a> Parser<'a> {
    pub fn new() -> Parser<'a> {
      Parser{bcd: ""}
    }

    method!(tag_abc<&mut Parser<'a>, &'a str, &'a str>, self, tag_s!("áβç"));
    method!(tag_bcd<&mut Parser<'a> >(&'a str) -> &'a str, self, tag_s!("βçδ"));
    method!(pub tag_hij<&mut Parser<'a> >(&'a str) -> &'a str, self, tag_s!("λïJ"));
    method!(pub tag_ijk<&mut Parser<'a>, &'a str, &'a str>, self, tag_s!("ïJƙ"));
    method!(take3<&mut Parser<'a>, &'a str, &'a str>, self, take_s!(3));
    method!(pub simple_call<&mut Parser<'a>, &'a str, &'a str>, self, [(self, ref_cell_self)],
      call_rc!(ref_cell_self.tag_abc)
    );
    method!(pub simple_peek<&mut Parser<'a>, &'a str, &'a str>, self, [(self, rcs)],
      peek!(call_rc!(rcs.take3))
    );
    method!(pub simple_chain<Parser<'a>, &'a str, &'a str>, mut self,
      chain!(
         bcd:  call_rc!(rcs.tag_bcd)      ~
         last: call_rc!(rcs.simple_peek)  ,
         ||{rcs.borrow_mut().bcd = bcd; last}
      )
    );
    fn tag_stuff(self: &mut Parser<'a>, input: &'a str, something: &'a str) -> ::IResult<&'a str, &'a str> {
      use std::cell::RefCell;
      let rcs = RefCell::new(self);
      let mut borrow = rcs.borrow_mut();
      borrow.bcd = something;
      borrow.tag_abc(input)
    }
    method!(use_apply<&mut Parser<'a>, &'a str, &'a str>, self, [(self, rcs)], apply_rf!(rcs.tag_stuff, "βçδ"));
  }
  #[test]
  fn test_method_call_abc() {
    let mut p = Parser::new();
    const INPUT: &'static str = "áβçδèƒϱλïJƙ";
    const CONSUMED: &'static str = "áβç";
    const LEFTOVER: &'static str = "δèƒϱλïJƙ";
    match p.tag_abc(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.tag_abc` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.tag_abc` doesnt return the string it consumed \
                                on success. Expected `{}`, got `{}`.", CONSUMED, output);
                             },
      other => panic!("`Parser.tag_abc` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
  #[test]
  fn test_method_call_bcd() {
    let mut p = Parser::new();
    const INPUT: &'static str = "βçδèƒϱλïJƙ";
    const CONSUMED: &'static str = "βçδ";
    const LEFTOVER: &'static str = "èƒϱλïJƙ";
    match p.tag_bcd(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.tag_bcd` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.tag_bcd` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", CONSUMED, output);
                             },
      other => panic!("`Parser.tag_bcd` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
  #[test]
  fn test_method_call_hij() {
    let mut p = Parser::new();
    const INPUT: &'static str = "λïJƙℓ₥ñôƥ9řƨ";
    const CONSUMED: &'static str = "λïJ";
    const LEFTOVER: &'static str = "ƙℓ₥ñôƥ9řƨ";
    match p.tag_hij(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.tag_hij` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.tag_hij` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", CONSUMED, output);
                             },
      other => panic!("`Parser.tag_hij` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
// áβçδèƒϱλïJƙℓ₥ñôƥ9řƨƭúƲωж¥ƺ
  #[test]
  fn test_method_call_ijk() {
    let mut p = Parser::new();
    const INPUT: &'static str = "ïJƙℓ₥ñôƥ9řƨ";
    const CONSUMED: &'static str = "ïJƙ";
    const LEFTOVER: &'static str = "ℓ₥ñôƥ9řƨ";
    match p.tag_ijk(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.tag_ijk` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.tag_ijk` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", CONSUMED, output);
                             },
      other => panic!("`Parser.tag_ijk` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
  #[test]
  fn test_method_call_rc() {
    let mut p = Parser::new();
    const INPUT: &'static str = "áβçδèƒϱλïJƙ";
    const CONSUMED: &'static str = "áβç";
    const LEFTOVER: &'static str = "δèƒϱλïJƙ";
    match p.simple_call(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.simple_call` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.simple_call` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", CONSUMED, output);
                             },
      other => panic!("`Parser.simple_call` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_apply_rf() {
    let mut p = Parser::new();
    const INPUT: &'static str = "áβçδèƒϱλïJƙ";
    const CONSUMED: &'static str = "áβç";
    const LEFTOVER: &'static str = "δèƒϱλïJƙ";
    match p.use_apply(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.use_apply` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.use_apply` doesn't return the string it was supposed to \
                                on success. Expected `{}`, got `{}`.", LEFTOVER, output);
                               assert!(p.bcd == "βçδ", "Parser.use_apply didn't modify the parser field correctly: {}", p.bcd);
                             },
      other => panic!("`Parser.use_apply` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_peek() {
    let mut p = Parser::new();
    const INPUT: &'static str = "ж¥ƺáβçδèƒϱλïJƙ";
    const CONSUMED: &'static str = "ж¥ƺ";
    match p.simple_peek(INPUT) {
      Done(extra, output) => { assert!(extra == INPUT, "`Parser.simple_peek` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.simple_peek` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", CONSUMED, output);
                             },
      other => panic!("`Parser.simple_peek` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_chain() {
    let mut p = Parser::new();
    const INPUT: &'static str = "βçδδèƒϱλïJƙℓ";
    const LEFTOVER: &'static str = "δèƒϱλïJƙℓ";
    const OUTPUT: &'static str = "δèƒ";
    match p.simple_chain(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.simple_chain` consumed leftover input. Leftover: {}", extra);
                               assert!(output == OUTPUT, "`Parser.simple_chain` doesn't return the string it was supposed to \
                                on success. Expected `{}`, got `{}`.", LEFTOVER, output);
                               assert!(p.bcd == "βçδ", "Parser.simple_chain didn't modify the parser field correctly: {}", p.bcd);
                             },
      other => panic!("`Parser.simple_chain` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
}
