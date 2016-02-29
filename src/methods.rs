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
//! method!(my_function<&Parser>,self, tag!("abcd"));
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
//! invodked. A `method!` invocation always has to have the type of `self`
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
//! To call a method on self you need to use the `call_m!` macro. For example:
//! ```ignore
//! struct<'a> Parser<'a> {
//!   parsed: &'a str,
//! }
//! impl<'a> Parser<'a> {
//!   // Constructor omitted for brevity
//!   method!(take4<Parser<'a>, &'a str, &'a str>, self, take!(4));
//!   method!(caller<Parser<'a>, &'a str, &'a str>, self, call_m!(self.take4));
//! }
//! ```
//! More complicated combinations still mostly look the same as their `named!`
//! counterparts:
//! ```ignore
//!    method!(pub simple_chain<&mut Parser<'a>, &'a str, &'a str>, self,
//!      chain!(
//!             call_m!(self.tag_abc)      ~
//!             call_m!(self.tag_def)      ~
//!             call_m!(self.tag_ghi)      ~
//!       last: call_m!(self.simple_peek)  ,
//!        ||{sb.parsed = last; last}
//!      )
//!    );
//! ```
//! The three additions to method definitions remeber are:
//! 1. Specify `self`'s type
//! 2. Pass `self` to the macro
//! 4. Call parser methods using the `call_m!` macro.

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
  ($name:ident<$a:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name<'a>( $self_: $a, i: &'a[u8] ) -> ($a, $crate::IResult<&'a [u8], $o, u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  ($name:ident<$a:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name( $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], &[u8], u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  // Public immutable self
  (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      pub fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty,$e:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i, $o, $e>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a,i: $i ) -> ($a, $crate::IResult<$i,$o,u32>)  {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  (pub $name:ident<$a:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name<'a>( $self_: $a, i: &'a[u8] ) -> ($a, $crate::IResult<&'a [u8], $o, u32>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  (pub $name:ident<$a:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], &[u8], u32>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  // Non-public mutable self
  ($name:ident<$a:ty>( $i:ty ) -> $o:ty, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty,$e:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i, $o, $e>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
      }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
    fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>)  {
      let result = $submac!(i, $($args)*);
      ($self_, result)
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
  (pub $name:ident<$a:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
    pub fn $name( mut $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], &[u8], u32>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
);

/// emulate function currying for method calls on structs 
/// `apply!(self.my_function, arg1, arg2, ...)` becomes `self.my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_m (
  ($i:expr, $self_:ident.$method:ident, $($args:expr),* ) => ( { let (tmp, res) = $self_.$method( $i, $($args),* ); $self_ = tmp; res } );
);

#[cfg(test)]
mod tests {
  use internal::{Needed,IResult,Err};
  use internal::IResult::*;
  use internal::Err::*;
  use util::ErrorKind;

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

    method!(tag_abc<Parser<'a>, &'a str, &'a str>, self, tag_s!("áβç"));
    method!(tag_bcd<Parser<'a> >(&'a str) -> &'a str, self, tag_s!("βçδ"));
    method!(pub tag_hij<Parser<'a> >(&'a str) -> &'a str, self, tag_s!("λïJ"));
    method!(pub tag_ijk<Parser<'a>, &'a str, &'a str>, self, tag_s!("ïJƙ"));
    method!(take3<Parser<'a>, &'a str, &'a str>, self, take_s!(3));
    method!(pub simple_call<Parser<'a>, &'a str, &'a str>, mut self,
      call_m!(self.tag_abc)
    );
    method!(pub simple_peek<Parser<'a>, &'a str, &'a str>, mut self,
      peek!(call_m!(self.take3))
    );
    method!(pub simple_chain<Parser<'a>, &'a str, &'a str>, mut self,
      chain!(
         bcd:  call_m!(self.tag_bcd)      ~
         last: call_m!(self.simple_peek)  ,
         ||{self.bcd = bcd; last}
      )
    );
    fn tag_stuff(mut self: Parser<'a>, input: &'a str, something: &'a str) -> (Parser<'a>, ::IResult<&'a str, &'a str>) {
      self.bcd = something;
      let(tmp, res) = self.tag_abc(input);
      self = tmp;
      (self, res)
    }
    method!(use_apply<Parser<'a>, &'a str, &'a str>, mut self, apply_rf!(self.tag_stuff, "βçδ"));
  }

  #[test]
  fn test_method_call_abc() {
    let p = Parser::new();
    let input: &str = "áβçδèƒϱλïJƙ";
    let consumed: &str = "áβç";
    let leftover: &str = "δèƒϱλïJƙ";
    let(_, res) = p.tag_abc(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.tag_abc` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.tag_abc` doesnt return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.tag_abc` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_bcd() {
    let p = Parser::new();
    let input: &str = "βçδèƒϱλïJƙ";
    let consumed: &str = "βçδ";
    let leftover: &str = "èƒϱλïJƙ";
    let(_, res) = p.tag_bcd(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.tag_bcd` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.tag_bcd` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.tag_bcd` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_hij() {
    let p = Parser::new();
    let input: &str = "λïJƙℓ₥ñôƥ9řƨ";
    let consumed: &str = "λïJ";
    let leftover: &str = "ƙℓ₥ñôƥ9řƨ";
    let(_, res) = p.tag_hij(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.tag_hij` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.tag_hij` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.tag_hij` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_ijk() {
    let p = Parser::new();
    let input: &str = "ïJƙℓ₥ñôƥ9řƨ";
    let consumed: &str = "ïJƙ";
    let leftover: &str = "ℓ₥ñôƥ9řƨ";
    let(_, res) = p.tag_ijk(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.tag_ijk` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.tag_ijk` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.tag_ijk` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
  #[test]
  fn test_method_simple_call() {
    let p = Parser::new();
    let input: &str = "áβçδèƒϱλïJƙ";
    let consumed: &str = "áβç";
    let leftover: &str = "δèƒϱλïJƙ";
    let(_, res) = p.simple_call(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.simple_call` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.simple_call` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.simple_call` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_apply_m() {
    let mut p = Parser::new();
    let input: &str = "áβçδèƒϱλïJƙ";
    let consumed: &str = "áβç";
    let leftover: &str = "δèƒϱλïJƙ";
    let(tmp, res) = p.use_apply(input);
    p = tmp;
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.use_apply` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.use_apply` doesn't return the string it was supposed to \
                                on success. Expected `{}`, got `{}`.", leftover, output);
                               assert!(p.bcd == "βçδ", "Parser.use_apply didn't modify the parser field correctly: {}", p.bcd);
                             },
      other => panic!("`Parser.use_apply` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_peek() {
    let p = Parser::new();
    let input: &str = "ж¥ƺáβçδèƒϱλïJƙ";
    let consumed: &str = "ж¥ƺ";
    let(_, res) = p.simple_peek(input);
    match res {
      Done(extra, output) => { assert!(extra == input, "`Parser.simple_peek` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.simple_peek` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.simple_peek` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_chain() {
    let mut p = Parser::new();
    let input : &str = "βçδδèƒϱλïJƙℓ";
    let leftover : &str = "δèƒϱλïJƙℓ";
    let output : &str = "δèƒ";
    let(tmp, res) = p.simple_chain(input);
    p = tmp;
    match res {
      Done(extra, out) => { assert!(extra == leftover, "`Parser.simple_chain` consumed leftover input. leftover: {}", extra);
                               assert!(out == output, "`Parser.simple_chain` doesn't return the string it was supposed to \
                                on success. Expected `{}`, got `{}`.", output, out);
                               assert!(p.bcd == "βçδ", "Parser.simple_chain didn't modify the parser field correctly: {}", p.bcd);
                             },
      other => panic!("`Parser.simple_chain` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  // reproduce the tag and take macros, because of module import order
  macro_rules! tag (
    ($i:expr, $inp: expr) => (
      {
        #[inline(always)]
        fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
          b.as_bytes()
        }

        let expected = $inp;
        let bytes    = as_bytes(&expected);

        tag_bytes!($i,bytes)
      }
    );
  );

  macro_rules! tag_bytes (
    ($i:expr, $bytes: expr) => (
      {
        use std::cmp::min;
        let len = $i.len();
        let blen = $bytes.len();
        let m   = min(len, blen);
        let reduced = &$i[..m];
        let b       = &$bytes[..m];

        let res: $crate::IResult<_,_> = if reduced != b {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Tag, $i))
        } else if m < blen {
          $crate::IResult::Incomplete($crate::Needed::Size(blen))
        } else {
          $crate::IResult::Done(&$i[blen..], reduced)
        };
        res
      }
    );
  );

  macro_rules! take(
    ($i:expr, $count:expr) => (
      {
        let cnt = $count as usize;
        let res:$crate::IResult<&[u8],&[u8]> = if $i.len() < cnt {
          $crate::IResult::Incomplete($crate::Needed::Size(cnt))
        } else {
          $crate::IResult::Done(&$i[cnt..],&$i[0..cnt])
        };
        res
      }
    );
  );


  #[derive(PartialEq,Eq,Debug)]
  struct B {
    a: u8,
    b: u8
  }
  struct TestParser<'a> {
    c: &'a [u8],
  }

  impl<'a> TestParser<'a> {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };

    fn new() -> TestParser<'a> {
      TestParser{c: b"" }
    }

    method!(pub chain_parser<TestParser<'a>,&[u8],B>, self
      chain!(
        tag!("abcd")        ~
        tag!("abcd")?       ~
        aa: self.ret_int1   ~
        tag!("efgh")        ~
        bb: self.ret_int2   ~
        tag!("efgh")        ,
        ||{B{a: aa, b: bb}}
      )
    );
  }
  #[test]
  fn chain2() {
    let parser = TestParser::new();
    assert_eq!(parser.chain_parser(&b"abcdabcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(parser.chain_parser(&b"abcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(parser.chain_parser(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(parser.chain_parser(&b"abcdefghef"[..]), Incomplete(Needed::Size(12)));
  }

  #[test]
  fn nested_chain() {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };

    named!(chain_parser<&[u8],B>,
      chain!(
        chain!(
          tag!("abcd")   ~
          tag!("abcd")?  ,
          || {}
        )              ~
        aa: ret_int1   ~
        tag!("efgh")   ~
        bb: ret_int2   ~
        tag!("efgh")   ,
        ||{B{a: aa, b: bb}}
      )
    );

    assert_eq!(chain_parser(&b"abcdabcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(chain_parser(&b"abcdefghef"[..]), Incomplete(Needed::Size(12)));
  }

  #[derive(PartialEq,Eq,Debug)]
  struct C {
    a: u8,
    b: Option<u8>
  }

  #[test]
  fn chain_mut() {
    fn ret_b1_2(i:&[u8]) -> IResult<&[u8], B> { Done(i,B{a:1,b:2}) };
    named!(f<&[u8],B>,
      chain!(
        tag!("abcd")     ~
        tag!("abcd")?    ~
        tag!("efgh")     ~
        mut bb: ret_b1_2 ~
        tag!("efgh")   ,
        ||{
          bb.b = 3;
          bb
        }
      )
    );

    let r = f(&b"abcdabcdefghefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], B{a: 1, b: 3}));
  }

  #[test]
  fn chain_opt() {
    named!(y, tag!("efgh"));
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    named!(ret_y<&[u8], u8>, map!(y, |_| 2));

    named!(chain_parser<&[u8],C>,
      chain!(
        tag!("abcd") ~
        aa: ret_int1 ~
        bb: ret_y?   ,
        ||{C{a: aa, b: bb}}
      )
    );

    assert_eq!(chain_parser(&b"abcdefghX"[..]), Done(&b"X"[..], C{a: 1, b: Some(2)}));
    assert_eq!(chain_parser(&b"abcdWXYZ"[..]), Done(&b"WXYZ"[..], C{a: 1, b: None}));
    assert_eq!(chain_parser(&b"abcdX"[..]), Done(&b"X"[..], C{ a: 1, b: None }));
    assert_eq!(chain_parser(&b"abcdef"[..]), Incomplete(Needed::Size(8)));
  }

  use util::{error_to_list, add_error_pattern, print_error};

  fn error_to_string<P>(e: &Err<P>) -> &'static str {
    let v:Vec<ErrorKind> = error_to_list(e);
    // do it this way if you can use slice patterns
    /*
    match &v[..] {
      [ErrorKind::Custom(42), ErrorKind::Tag]                         => "missing `ijkl` tag",
      [ErrorKind::Custom(42), ErrorKind::Custom(128), ErrorKind::Tag] => "missing `mnop` tag after `ijkl`",
      _            => "unrecognized error"
    }
    */
    if &v[..] == [ErrorKind::Custom(42),ErrorKind::Tag] {
      "missing `ijkl` tag"
    } else if &v[..] == [ErrorKind::Custom(42), ErrorKind::Custom(128), ErrorKind::Tag] {
      "missing `mnop` tag after `ijkl`"
    } else {
      "unrecognized error"
    }
  }

  // do it this way if you can use box patterns
  /*use std::str;
  fn error_to_string(e:Err) -> String
    match e {
      NodePosition(ErrorKind::Custom(42), i1, box Position(ErrorKind::Tag, i2)) => {
        format!("missing `ijkl` tag, found '{}' instead", str::from_utf8(i2).unwrap())
      },
      NodePosition(ErrorKind::Custom(42), i1, box NodePosition(ErrorKind::Custom(128), i2,  box Position(ErrorKind::Tag, i3))) => {
        format!("missing `mnop` tag after `ijkl`, found '{}' instead", str::from_utf8(i3).unwrap())
      },
      _ => "unrecognized error".to_string()
    }
  }*/
  use std::collections;
  #[test]
  fn err() {
    named!(err_test, alt!(
      tag!("abcd") |
      preceded!(tag!("efgh"), error!(ErrorKind::Custom(42),
          chain!(
                 tag!("ijkl")              ~
            res: error!(ErrorKind::Custom(128), tag!("mnop")) ,
            || { res }
          )
        )
      )
    ));
    let a = &b"efghblah"[..];
    let b = &b"efghijklblah"[..];
    let c = &b"efghijklmnop"[..];

    let blah = &b"blah"[..];

    let res_a = err_test(a);
    let res_b = err_test(b);
    let res_c = err_test(c);
    assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), blah, Box::new(Position(ErrorKind::Tag, blah)))));
    assert_eq!(res_b, Error(NodePosition(ErrorKind::Custom(42), &b"ijklblah"[..], Box::new(NodePosition(ErrorKind::Custom(128), blah, Box::new(Position(ErrorKind::Tag, blah)))))));
    assert_eq!(res_c, Done(&b""[..], &b"mnop"[..]));

    // Merr-like error matching
    let mut err_map = collections::HashMap::new();
    assert!(add_error_pattern(&mut err_map, err_test(&b"efghpouet"[..]), "missing `ijkl` tag"));
    assert!(add_error_pattern(&mut err_map, err_test(&b"efghijklpouet"[..]), "missing `mnop` tag after `ijkl`"));

    let res_a2 = res_a.clone();
    match res_a {
      Error(e) => {
        assert_eq!(error_to_list(&e), [ErrorKind::Custom(42), ErrorKind::Tag]);
        assert_eq!(error_to_string(&e), "missing `ijkl` tag");
        assert_eq!(err_map.get(&error_to_list(&e)), Some(&"missing `ijkl` tag"));
      },
      _ => panic!()
    };

    let res_b2 = res_b.clone();
    match res_b {
      Error(e) => {
        assert_eq!(error_to_list(&e), [ErrorKind::Custom(42), ErrorKind::Custom(128), ErrorKind::Tag]);
        assert_eq!(error_to_string(&e), "missing `mnop` tag after `ijkl`");
        assert_eq!(err_map.get(&error_to_list(&e)), Some(&"missing `mnop` tag after `ijkl`"));
      },
      _ => panic!()
    };

    print_error(a, res_a2);
    print_error(b, res_b2);
  }

  #[test]
  fn add_err() {
    named!(err_test,
      preceded!(tag!("efgh"), add_error!(ErrorKind::Custom(42),
          chain!(
                 tag!("ijkl")              ~
            res: add_error!(ErrorKind::Custom(128), tag!("mnop")) ,
            || { res }
          )
        )
    ));
    let a = &b"efghblah"[..];
    let b = &b"efghijklblah"[..];
    let c = &b"efghijklmnop"[..];

    let blah = &b"blah"[..];

    let res_a = err_test(a);
    let res_b = err_test(b);
    let res_c = err_test(c);
    assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), blah, Box::new(Position(ErrorKind::Tag, blah)))));
    assert_eq!(res_b, Error(NodePosition(ErrorKind::Custom(42), &b"ijklblah"[..], Box::new(NodePosition(ErrorKind::Custom(128), blah, Box::new(Position(ErrorKind::Tag, blah)))))));
    assert_eq!(res_c, Done(&b""[..], &b"mnop"[..]));
  }

  #[test]
  fn complete() {
    named!(err_test,
      chain!(
             tag!("ijkl")              ~
        res: complete!(tag!("mnop")) ,
        || { res }
      )
    );
    let a = &b"ijklmn"[..];

    let res_a = err_test(a);
    assert_eq!(res_a, Error(Position(ErrorKind::Complete, &b"mn"[..])));
  }
  #[test]
  fn alt() {
    fn work(input: &[u8]) -> IResult<&[u8],&[u8], &'static str> {
      Done(&b""[..], input)
    }

    #[allow(unused_variables)]
    fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8],&'static str> {
      Error(Code(ErrorKind::Custom("abcd")))
    }

    fn work2(input: &[u8]) -> IResult<&[u8],&[u8], &'static str> {
      Done(input, &b""[..])
    }

    fn alt1(i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
      alt!(i, dont_work | dont_work)
    }
    fn alt2(i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
      alt!(i, dont_work | work)
    }
    fn alt3(i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
      alt!(i, dont_work | dont_work | work2 | dont_work)
    }
    //named!(alt1, alt!(dont_work | dont_work));
    //named!(alt2, alt!(dont_work | work));
    //named!(alt3, alt!(dont_work | dont_work | work2 | dont_work));

    let a = &b"abcd"[..];
    assert_eq!(alt1(a), Error(Position(ErrorKind::Alt, a)));
    assert_eq!(alt2(a), Done(&b""[..], a));
    assert_eq!(alt3(a), Done(a, &b""[..]));

    named!(alt4, alt!(tag!("abcd") | tag!("efgh")));
    let b = &b"efgh"[..];
    assert_eq!(alt4(a), Done(&b""[..], a));
    assert_eq!(alt4(b), Done(&b""[..], b));

    // test the alternative syntax
    named!(alt5<bool>, alt!(tag!("abcd") => { |_| false } | tag!("efgh") => { |_| true }));
    assert_eq!(alt5(a), Done(&b""[..], false));
    assert_eq!(alt5(b), Done(&b""[..], true));

  }

  #[test]
  fn alt_incomplete() {
    named!(alt1, alt!(tag!("a") | tag!("bc") | tag!("def")));

    let a = &b""[..];
    assert_eq!(alt1(a), Incomplete(Needed::Size(1)));
    let a = &b"b"[..];
    assert_eq!(alt1(a), Incomplete(Needed::Size(2)));
    let a = &b"bcd"[..];
    assert_eq!(alt1(a), Done(&b"d"[..], &b"bc"[..]));
    let a = &b"cde"[..];
    assert_eq!(alt1(a), Error(Position(ErrorKind::Alt, a)));
    let a = &b"de"[..];
    assert_eq!(alt1(a), Incomplete(Needed::Size(3)));
    let a = &b"defg"[..];
    assert_eq!(alt1(a), Done(&b"g"[..], &b"def"[..]));
  }

  #[test]
  fn alt_complete() {
    named!(ac<&[u8], &[u8]>,
      alt_complete!(tag!("abcd") | tag!("ef") | tag!("ghi") | tag!("kl"))
    );

    let a = &b""[..];
    assert_eq!(ac(a), Incomplete(Needed::Size(2)));
    let a = &b"ef"[..];
    assert_eq!(ac(a), Done(&b""[..], &b"ef"[..]));
    let a = &b"cde"[..];
    assert_eq!(ac(a), Error(Position(ErrorKind::Alt, a)));
  }

  #[test]
  fn switch() {
    named!(sw,
      switch!(take!(4),
        b"abcd" => take!(2) |
        b"efgh" => take!(4)
      )
    );

    let a = &b"abcdefgh"[..];
    assert_eq!(sw(a), Done(&b"gh"[..], &b"ef"[..]));

    let b = &b"efghijkl"[..];
    assert_eq!(sw(b), Done(&b""[..], &b"ijkl"[..]));
    let c = &b"afghijkl"[..];
    assert_eq!(sw(c), Error(Position(ErrorKind::Switch, &b"afghijkl"[..])));
  }

  #[test]
  fn opt() {
    named!(opt_abcd<&[u8],Option<&[u8]> >, opt!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    let c = &b"ab"[..];
    assert_eq!(opt_abcd(a), Done(&b"ef"[..], Some(&b"abcd"[..])));
    assert_eq!(opt_abcd(b), Done(&b"bcdefg"[..], None));
    assert_eq!(opt_abcd(c), Incomplete(Needed::Size(4)));
  }

  #[test]
  fn opt_res() {
    named!(opt_res_abcd<&[u8], Result<&[u8], Err<&[u8]>> >, opt_res!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    let c = &b"ab"[..];
    assert_eq!(opt_res_abcd(a), Done(&b"ef"[..], Ok(&b"abcd"[..])));
    assert_eq!(opt_res_abcd(b), Done(&b"bcdefg"[..], Err(Position(ErrorKind::Tag, b))));
    assert_eq!(opt_res_abcd(c), Incomplete(Needed::Size(4)));
  }

  #[test]
  fn cond() {
    let f_true: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( true, tag!("abcd") ) ));
    let f_false: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( false, tag!("abcd") ) ));
    //let f_false = closure!(&'static [u8], cond!( false, tag!("abcd") ) );

    assert_eq!(f_true(&b"abcdef"[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));
    assert_eq!(f_true(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(f_true(&b"xxx"[..]), Done(&b"xxx"[..], None));

    assert_eq!(f_false(&b"abcdef"[..]), Done(&b"abcdef"[..], None));
    assert_eq!(f_false(&b"ab"[..]), Done(&b"ab"[..], None));
    assert_eq!(f_false(&b"xxx"[..]), Done(&b"xxx"[..], None));
  }

  #[test]
  fn cond_wrapping() {
    // Test that cond!() will wrap a given identifier in the call!() macro.

    named!(silly, tag!("foo"));

    let b = true;
    //let f = closure!(&'static [u8], cond!( b, silly ) );
    let f: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( b, silly ) ));
    assert_eq!(f(b"foobar"), Done(&b"bar"[..], Some(&b"foo"[..])));
  }

  #[test]
  fn peek() {
    named!(peek_tag<&[u8],&[u8]>, peek!(tag!("abcd")));

    assert_eq!(peek_tag(&b"abcdef"[..]), Done(&b"abcdef"[..], &b"abcd"[..]));
    assert_eq!(peek_tag(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(peek_tag(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn pair() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( pair_abc_def<&[u8],(&[u8], &[u8])>, pair!(tag_abc, tag_def) );

    assert_eq!(pair_abc_def(&b"abcdefghijkl"[..]), Done(&b"ghijkl"[..], (&b"abc"[..], &b"def"[..])));
    assert_eq!(pair_abc_def(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(pair_abc_def(&b"abcd"[..]), Incomplete(Needed::Size(6)));
    assert_eq!(pair_abc_def(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(pair_abc_def(&b"xxxdef"[..]), Error(Position(ErrorKind::Tag, &b"xxxdef"[..])));
    assert_eq!(pair_abc_def(&b"abcxxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn separated_pair() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( tag_separator, tag!(",") );
    named!( sep_pair_abc_def<&[u8],(&[u8], &[u8])>, separated_pair!(tag_abc, tag_separator, tag_def) );

    assert_eq!(sep_pair_abc_def(&b"abc,defghijkl"[..]), Done(&b"ghijkl"[..], (&b"abc"[..], &b"def"[..])));
    assert_eq!(sep_pair_abc_def(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(sep_pair_abc_def(&b"abc,d"[..]), Incomplete(Needed::Size(7)));
    assert_eq!(sep_pair_abc_def(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(sep_pair_abc_def(&b"xxx,def"[..]), Error(Position(ErrorKind::Tag, &b"xxx,def"[..])));
    assert_eq!(sep_pair_abc_def(&b"abc,xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn preceded() {
    named!( tag_abcd, tag!("abcd") );
    named!( tag_efgh, tag!("efgh") );
    named!( preceded_abcd_efgh<&[u8], &[u8]>, preceded!(tag_abcd, tag_efgh) );

    assert_eq!(preceded_abcd_efgh(&b"abcdefghijkl"[..]), Done(&b"ijkl"[..], &b"efgh"[..]));
    assert_eq!(preceded_abcd_efgh(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(preceded_abcd_efgh(&b"abcde"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(preceded_abcd_efgh(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(preceded_abcd_efgh(&b"xxxxdef"[..]), Error(Position(ErrorKind::Tag, &b"xxxxdef"[..])));
    assert_eq!(preceded_abcd_efgh(&b"abcdxxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn terminated() {
    named!( tag_abcd, tag!("abcd") );
    named!( tag_efgh, tag!("efgh") );
    named!( terminated_abcd_efgh<&[u8], &[u8]>, terminated!(tag_abcd, tag_efgh) );

    assert_eq!(terminated_abcd_efgh(&b"abcdefghijkl"[..]), Done(&b"ijkl"[..], &b"abcd"[..]));
    assert_eq!(terminated_abcd_efgh(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(terminated_abcd_efgh(&b"abcde"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(terminated_abcd_efgh(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(terminated_abcd_efgh(&b"xxxxdef"[..]), Error(Position(ErrorKind::Tag, &b"xxxxdef"[..])));
    assert_eq!(terminated_abcd_efgh(&b"abcdxxxx"[..]), Error(Position(ErrorKind::Tag, &b"xxxx"[..])));
  }

  #[test]
  fn delimited() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( tag_ghi, tag!("ghi") );
    named!( delimited_abc_def_ghi<&[u8], &[u8]>, delimited!(tag_abc, tag_def, tag_ghi) );

    assert_eq!(delimited_abc_def_ghi(&b"abcdefghijkl"[..]), Done(&b"jkl"[..], &b"def"[..]));
    assert_eq!(delimited_abc_def_ghi(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(delimited_abc_def_ghi(&b"abcde"[..]), Incomplete(Needed::Size(6)));
    assert_eq!(delimited_abc_def_ghi(&b"abcdefgh"[..]), Incomplete(Needed::Size(9)));
    assert_eq!(delimited_abc_def_ghi(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"xxxdefghi"[..]), Error(Position(ErrorKind::Tag, &b"xxxdefghi"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"abcxxxghi"[..]), Error(Position(ErrorKind::Tag, &b"xxxghi"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"abcdefxxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn separated_list() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_list!(tag!(","), tag!("abcd")));
    named!(multi_empty<&[u8],Vec<&[u8]> >, separated_list!(tag!(","), tag!("")));

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];
    let d = &b",,abc"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
    let res3 = vec![&b""[..], &b""[..], &b""[..]];
    //assert_eq!(multi_empty(d), Done(&b"abc"[..], res3));
  }

  #[test]
  fn separated_nonempty_list() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_nonempty_list!(tag!(","), tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Error(Position(ErrorKind::Tag,c)));
  }

  #[test]
  fn many0() {
    named!(multi<&[u8],Vec<&[u8]> >, many0!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdefgh"[..];
    let c = &b"azerty"[..];
    let d = &b"abcdab"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res2));
    assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
    assert_eq!(multi(d), Incomplete(Needed::Size(8)));
  }

  #[cfg(feature = "nightly")]
  use test::Bencher;

  #[cfg(feature = "nightly")]
  #[bench]
  fn many0_bench(b: &mut Bencher) {
    named!(multi<&[u8],Vec<&[u8]> >, many0!(tag!("abcd")));
    b.iter(|| {
      multi(&b"abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"[..])
    });
  }

  #[test]
  fn many1() {
    named!(multi<&[u8],Vec<&[u8]> >, many1!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdefgh"[..];
    let c = &b"azerty"[..];
    let d = &b"abcdab"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res2));
    assert_eq!(multi(c), Error(Position(ErrorKind::Many1,c)));
    assert_eq!(multi(d), Incomplete(Needed::Size(8)));
  }

  #[test]
  fn infinite_many() {
    fn tst(input: &[u8]) -> IResult<&[u8], &[u8]> {
      println!("input: {:?}", input);
      Error(Position(ErrorKind::Custom(0),input))
    }

    // should not go into an infinite loop
    named!(multi0<&[u8],Vec<&[u8]> >, many0!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi0(a), Done(a, Vec::new()));

    named!(multi1<&[u8],Vec<&[u8]> >, many1!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi1(a), Error(Position(ErrorKind::Many1,a)));
  }

  #[test]
  fn many_m_n() {
    named!(multi<&[u8],Vec<&[u8]> >, many_m_n!(2, 4, tag!("Abcd")));

    let a = &b"Abcdef"[..];
    let b = &b"AbcdAbcdefgh"[..];
    let c = &b"AbcdAbcdAbcdAbcdefgh"[..];
    let d = &b"AbcdAbcdAbcdAbcdAbcdefgh"[..];
    let e = &b"AbcdAb"[..];

    assert_eq!(multi(a), Error(Err::Position(ErrorKind::ManyMN,a)));
    let res1 = vec![&b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res1));
    let res2 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(c), Done(&b"efgh"[..], res2));
    let res3 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(d), Done(&b"Abcdefgh"[..], res3));
    assert_eq!(multi(e), Incomplete(Needed::Size(8)));
  }

  #[test]
  fn count() {
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( cnt_2<&[u8], Vec<&[u8]> >, count!(tag_abc, TIMES ) );

    assert_eq!(cnt_2(&b"abcabcabcdef"[..]), Done(&b"abcdef"[..], vec![&b"abc"[..], &b"abc"[..]]));
    assert_eq!(cnt_2(&b"ab"[..]), Incomplete(Needed::Unknown));
    assert_eq!(cnt_2(&b"abcab"[..]), Incomplete(Needed::Unknown));
    assert_eq!(cnt_2(&b"xxx"[..]), Error(Position(ErrorKind::Count, &b"xxx"[..])));
    assert_eq!(cnt_2(&b"xxxabcabcdef"[..]), Error(Position(ErrorKind::Count, &b"xxxabcabcdef"[..])));
    assert_eq!(cnt_2(&b"abcxxxabcdef"[..]), Error(Position(ErrorKind::Count, &b"abcxxxabcdef"[..])));
  }

  #[test]
  fn count_zero() {
    const TIMES: usize = 0;
    named!( tag_abc, tag!("abc") );
    named!( counter_2<&[u8], Vec<&[u8]> >, count!(tag_abc, TIMES ) );

    let done = &b"abcabcabcdef"[..];
    let parsed_done = Vec::new();
    let rest = done;
    let incomplete_1 = &b"ab"[..];
    let parsed_incompl_1 = Vec::new();
    let incomplete_2 = &b"abcab"[..];
    let parsed_incompl_2 = Vec::new();
    let error = &b"xxx"[..];
    let error_remain = &b"xxx"[..];
    let parsed_err = Vec::new();
    let error_1 = &b"xxxabcabcdef"[..];
    let parsed_err_1 = Vec::new();
    let error_1_remain = &b"xxxabcabcdef"[..];
    let error_2 = &b"abcxxxabcdef"[..];
    let parsed_err_2 = Vec::new();
    let error_2_remain = &b"abcxxxabcdef"[..];

    assert_eq!(counter_2(done), Done(rest, parsed_done));
    assert_eq!(counter_2(incomplete_1), Done(incomplete_1, parsed_incompl_1));
    assert_eq!(counter_2(incomplete_2), Done(incomplete_2, parsed_incompl_2));
    assert_eq!(counter_2(error), Done(error_remain, parsed_err));
    assert_eq!(counter_2(error_1), Done(error_1_remain, parsed_err_1));
    assert_eq!(counter_2(error_2), Done(error_2_remain, parsed_err_2));
  }

  #[test]
  fn count_fixed() {
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( cnt_2<&[u8], [&[u8]; TIMES] >, count_fixed!(&[u8], tag_abc, TIMES ) );

    assert_eq!(cnt_2(&b"abcabcabcdef"[..]), Done(&b"abcdef"[..], [&b"abc"[..], &b"abc"[..]]));
    assert_eq!(cnt_2(&b"ab"[..]), Incomplete(Needed::Unknown));
    assert_eq!(cnt_2(&b"abcab"[..]), Incomplete(Needed::Unknown));
    assert_eq!(cnt_2(&b"xxx"[..]), Error(Position(ErrorKind::Count, &b"xxx"[..])));
    assert_eq!(cnt_2(&b"xxxabcabcdef"[..]), Error(Position(ErrorKind::Count, &b"xxxabcabcdef"[..])));
    assert_eq!(cnt_2(&b"abcxxxabcdef"[..]), Error(Position(ErrorKind::Count, &b"abcxxxabcdef"[..])));
  }

  use nom::{le_u16,eof};
  #[allow(dead_code)]
  pub fn compile_count_fixed(input: &[u8]) -> IResult<&[u8], ()> {
    chain!(input,
      tag!("abcd")                   ~
      count_fixed!( u16, le_u16, 4 ) ~
      eof                            ,
      || { () }
    )
  }

  #[test]
  fn count_fixed_no_type() {
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( counter_2<&[u8], [&[u8]; TIMES], () >, count_fixed!(&[u8], tag_abc, TIMES ) );

    let done = &b"abcabcabcdef"[..];
    let parsed_main = [&b"abc"[..], &b"abc"[..]];
    let rest = &b"abcdef"[..];
    let incomplete_1 = &b"ab"[..];
    let incomplete_2 = &b"abcab"[..];
    let error = &b"xxx"[..];
    let error_1 = &b"xxxabcabcdef"[..];
    let error_1_remain = &b"xxxabcabcdef"[..];
    let error_2 = &b"abcxxxabcdef"[..];
    let error_2_remain = &b"abcxxxabcdef"[..];

    assert_eq!(counter_2(done), Done(rest, parsed_main));
    assert_eq!(counter_2(incomplete_1), Incomplete(Needed::Unknown));
    assert_eq!(counter_2(incomplete_2), Incomplete(Needed::Unknown));
    assert_eq!(counter_2(error), Error(Position(ErrorKind::Count, error)));
    assert_eq!(counter_2(error_1), Error(Position(ErrorKind::Count, error_1_remain)));
    assert_eq!(counter_2(error_2), Error(Position(ErrorKind::Count, error_2_remain)));
  }

  use nom::{be_u8,be_u16};
  #[test]
  fn length_value_test() {
    named!(tst1<&[u8], Vec<u16> >, length_value!(be_u8, be_u16));
    named!(tst2<&[u8], Vec<u16> >, length_value!(be_u8, be_u16, 2));

    let i1 = vec![0, 5, 6];
    let i2 = vec![1, 5, 6, 3];
    let i3 = vec![2, 5, 6, 3];
    let i4 = vec![2, 5, 6, 3, 4, 5, 7];
    let i5 = vec![3, 5, 6, 3, 4, 5];

    let r1: Vec<u16> = Vec::new();
    let r2: Vec<u16> = vec![1286];
    let r4: Vec<u16> = vec![1286, 772];
    assert_eq!(tst1(&i1), IResult::Done(&i1[1..], r1));
    assert_eq!(tst1(&i2), IResult::Done(&i2[3..], r2));
    assert_eq!(tst1(&i3), IResult::Incomplete(Needed::Size(5)));
    assert_eq!(tst1(&i4), IResult::Done(&i4[5..], r4));
    assert_eq!(tst1(&i5), IResult::Incomplete(Needed::Size(7)));

    let r6: Vec<u16> = Vec::new();
    let r7: Vec<u16> = vec![1286];
    let r9: Vec<u16> = vec![1286, 772];
    assert_eq!(tst2(&i1), IResult::Done(&i1[1..], r6));
    assert_eq!(tst2(&i2), IResult::Done(&i2[3..], r7));
    assert_eq!(tst2(&i3), IResult::Incomplete(Needed::Size(5)));
    assert_eq!(tst2(&i4), IResult::Done(&i4[5..], r9));
    assert_eq!(tst1(&i5), IResult::Incomplete(Needed::Size(7)));
  }

  #[test]
  fn tuple_test() {
    named!(tuple_3<&[u8], (u16, &[u8], &[u8]) >,
    tuple!( be_u16 , take!(3), tag!("fg") ) );

    assert_eq!(tuple_3(&b"abcdefgh"[..]), Done(&b"h"[..], (0x6162u16, &b"cde"[..], &b"fg"[..])));
    assert_eq!(tuple_3(&b"abcd"[..]), Incomplete(Needed::Size(5)));
    assert_eq!(tuple_3(&b"abcde"[..]), Incomplete(Needed::Size(7)));
    assert_eq!(tuple_3(&b"abcdejk"[..]), Error(Position(ErrorKind::Tag, &b"jk"[..])));
  }
}
