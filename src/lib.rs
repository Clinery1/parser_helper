//! # About
//! A helpful little library for hand writing recursive ascent/descent parsers. Makes lookahead
//! much easier so you don't have to write a lookahead lexer yourself.
//!
//! # Recommended practices
//! Creating a newtype wrapper around [`LookaheadLexer`] and implementing [`Deref`](std::ops::Deref)
//! and [`DerefMut`](std::ops::DerefMut) on it for easy `self.take_token()` and other methods.
//!
//! I also recommend not using entirely recursive ascent like a parser generator would, but instead
//! using helper functions to consolidate a lot of the pattern matching and make it similar to
//! recursive descent, but also keeping enough pattern matching in the main functions to avoid
//! left-recursion problems.
//!
//! # Helpful patterns
//! ## Left-associative ASTs
//! When using recursive ascent, it is very easy to make right-associative ASTs, but creating a
//! left-associative AST is not immediately obvious. One way is to have two functions.
//! ```ignore
//! // A non-recursive helper method that simply makes calling the recursive function easier
//! fn left_associative(&mut self)->Expr<'a> {
//!     let left=self.expr();
//!     return self.left_associative_inner(left);
//! }
//!
//! // The recursive method that actually builds the left-associative AST
//! fn left_associative_inner(&mut self,left:Expr<'a>)->Expr<'a> {
//!     // Lookahead to see if the token is what we want.
//!     match self.lookahead(0) {
//!         Token::Add=>{},
//!
//!         // Return the left side if we don't find the right token
//!         _=>return Ok(left),
//!     }
//!
//!     // Take the token since we only used lookahead to verify its the right one
//!     self.take_token();
//!
//!     // Get the right side of the expression. This is where the magic is. If we get the right
//!     // AND left side before recursing, then both are considered as the "new left side" when we
//!     // do finally recurse.
//!     let right=self.expr();
//!
//!     // Map the current left and right for recursive calling
//!     let out=Expr::Add(Box::new([left,right]));
//!
//!     return self.left_associative_inner(out);
//! }
//! ```
//! For the more visual learners, here is a tree structure representing the function calls for the
//! left-associative methods:
//! ```text
//!   left
//!      /\
//!     /  inner ----> expr
//!    |        \     /
//!    |         right
//!     \       /
//!      combine
//!     /
//! left
//!     \
//!      inner
//! ```
//!
//! ## Right-associative ASTs
//! These are much easier to do, so ill only provide a simple example.
//! ```ignore
//! // Right-associative parsers can be done much more easily.
//! fn right_associative(&mut self)->Expr<'a> {
//!     // Get the left expression
//!     let left=self.expr();
//!
//!     // Match the lookahead and take the token like in the left-associative example.
//!     match self.lookahead(0) {
//!         Token::Add=>{},
//!         _=>return Ok(left),
//!     }
//!     self.take_token();
//!
//!     // Here we recurse to get the right side instead of passing the right and left to the
//!     // recursive call.
//!     let right=self.right_associative();
//!
//!     return Expr::Add(Box::new([left,right]));
//! }
//! ```
//! Another visual graph:
//! ```text
//!      inner
//!     /     \
//! expr       inner
//!     \     /
//!     combine
//!            \
//!             output
//! ```


#[cfg(feature="logos")]
use logos::Logos;
use std::{
    fmt::Debug,
    ops::Range,
    str::CharIndices,
    mem,
};


#[macro_export]
macro_rules! new_parser {
    ($is_pub:vis struct $name:ident<$lt:lifetime, $count:literal, $token:ty, $lexer:ty>)=>{
        new_parser!($is_pub struct $name<$lt, $count, $token, $lexer, ()>);
    };
    ($is_pub:vis struct $name:ident<$lt:lifetime, $count:literal, $token:ty, $lexer:ty, $data:ty>)=>{
        $is_pub struct $name<$lt>($crate::LookaheadLexer<$count,$token,$lexer,$data>);
        impl<$lt> $name<$lt> {
            pub fn new(lexer: $lexer, data: $data)->Self {
                Self(LookaheadLexer::new(lexer, data))
            }
        }
        impl<$lt> std::ops::Deref for $name<$lt> {
            type Target=$crate::LookaheadLexer<$count,$token,$lexer,$data>;
            fn deref(&self)->&Self::Target {
                &self.0
            }
        }
        impl<$lt> std::ops::DerefMut for $name<$lt> {
            fn deref_mut(&mut self)->&mut Self::Target {
                &mut self.0
            }
        }
    };
    ($is_pub:vis struct $name:ident<$count:literal, $token:ty, $lexer:ty, $data:ty>)=>{
        new_parser!($is_pub struct $name<$count, $token, $lexer, ()>);
    };
    ($is_pub:vis struct $name:ident<$count:literal, $token:ty, $lexer:ty, $data:ty>)=>{
        $is_pub struct $name($crate::LookaheadLexer<$count,$token,$lexer,$data>);
        impl<$lt> $name<$lt> {
            pub fn new(lexer: $lexer, data: $data)->Self {
                Self(LookaheadLexer::new(lexer, data))
            }
        }
        impl std::ops::Deref for $name {
            type Target=$crate::LookaheadLexer<$count,$token,$lexer,$data>;
            fn deref(&self)->&Self::Target {
                &self.0
            }
        }
        impl std::ops::DerefMut for $name {
            fn deref_mut(&mut self)->&mut Self::Target {
                &mut self.0
            }
        }
    };
}

new_parser!(pub struct MyParser<'a, 1, char, CharTokenStream<'a>, String>);


pub type Span=Range<usize>;


/// Required for a token to be used.
pub trait Token:Debug {
    fn eof()->Self;
}
impl Token for char {
    /// We use the null char to indicate EOF since there isn't a better option
    fn eof()->Self {
        '\0'
    }
}

/// A stream of tokens with a few helpful functions.
pub trait TokenStream<T:Token>:Iterator<Item=T> {
    type Slice;
    /// The span of the current token
    fn span(&self)->Span;

    /// The full source
    fn source(&self)->Self::Slice;

    /// The remaining string
    fn remaining(&self)->Self::Slice;

    /// The string slice of the current token
    fn slice(&self)->Self::Slice;

    /// The span of the last token (EOF)
    fn end_span(&self)->Span;
}

#[cfg(feature="logos")]
impl<'a,T:Token+Logos<'a,Source=str>> TokenStream<T> for LogosWrapper<'a,T> {
    type Slice=&'a str;
    fn span(&self)->Span {
        self.0.span()
    }
    fn source(&self)->&'a str {
        self.0.source()
    }
    fn remaining(&self)->&'a str {
        self.0.remainder()
    }
    fn slice(&self)->&'a str {
        self.0.slice()
    }
    fn end_span(&self)->Span {
        self.0.source().len()..self.0.source().len()
    }
}


/// A helper for returning two different types from a parser.
#[derive(Debug,PartialEq)]
pub enum Either<A,B> {
    A(A),
    B(B),
}

/// A helper for returning three different types from a parser.
#[derive(Debug,PartialEq)]
pub enum Either3<A,B,C> {
    A(A),
    B(B),
    C(C),
}

/// A helper for returning three different types from a parser.
#[derive(Debug,PartialEq)]
pub enum Either4<A,B,C,D> {
    A(A),
    B(B),
    C(C),
    D(D),
}


#[cfg(feature="logos")]
#[repr(transparent)]
pub struct LogosWrapper<'a, T: Logos<'a>>(pub logos::Lexer<'a, T>);

#[cfg(feature="logos")]
impl<'a, T: Logos<'a>> Iterator for LogosWrapper<'a, T> {
    type Item = T;
    fn next(&mut self)->Option<T> {
        if let Ok(t) = self.0.next()? {
            return Some(t);
        }
        return None;
    }
}

#[cfg(feature="logos")]
impl<'a, T: Logos<'a>> From<logos::Lexer<'a, T>> for LogosWrapper<'a, T> {
    fn from(o: logos::Lexer<'a, T>)->Self {
        Self(o)
    }
}

pub struct CharTokenStream<'a> {
    s:&'a str,
    cur_offset:usize,
    iter:CharIndices<'a>,
}
impl<'a> CharTokenStream<'a> {
    pub fn new(source:&'a str)->Self {
        Self {
            s:source,
            cur_offset:0,
            iter:source.char_indices(),
        }
    }

    fn next_char_index(&self)->usize {
        let start=self.cur_offset+1;
        for o in 0..4 {
            if start+o>=self.s.len() {
                return self.s.len();
            }
            if self.s.is_char_boundary(start+o) {
                return (start+o).min(self.s.len());
            }
        }
        unreachable!();
    }
}
impl<'a> Iterator for CharTokenStream<'a> {
    type Item=char;
    fn next(&mut self)->Option<char> {
        let (cur_offset,c)=self.iter.next()?;
        self.cur_offset=cur_offset;
        return Some(c);
    }
}
impl<'a> TokenStream<char> for CharTokenStream<'a> {
    type Slice=&'a str;
    fn source(&self)->Self::Slice {
        self.s
    }
    fn span(&self)->Span {
        return self.cur_offset..self.next_char_index();
    }
    fn remaining(&self)->Self::Slice {
        &self.s[self.cur_offset..]
    }
    fn slice(&self)->Self::Slice {
        &self.s[self.cur_offset..self.next_char_index()]
    }
    fn end_span(&self)->Span {
        self.s.len()..self.s.len()
    }
}

/// A parser with `K` tokens of lookahead and a few helpful methods. Can contain user data for
/// context-dependent parsing like significant whitespace or nested languages.
///
/// Note: K MUST BE greater than 0 or the lexer will always panic when attempting to access a
/// zero-length lookahead buffer.
pub struct LookaheadLexer<const K:usize,T:Token,L:TokenStream<T>,D> {
    /// If it returns true, then we ignore the token
    ignore_fn:Box<dyn Fn(&T)->bool>,
    enable_ignore:bool,
    pub user_data:D,
    inner:L,
    buffer:[(T,Span);K],
    current_token_span:Span,
    is_eof:bool,
}
impl<const K:usize,T:Token,L:TokenStream<T>,D> LookaheadLexer<K,T,L,D> {
    /// Create a new LookaheadLexer with the given lexer and user data.
    pub fn new(lexer:L,user_data:D)->Self {
        debug_assert!(K!=0);
        let buf=(0..K).map(|_|(T::eof(),lexer.end_span())).collect::<Vec<_>>();

        let buffer=if let Ok(b)=buf.try_into() {
            b
        } else {
            unreachable!()
        };

        let mut ret=Self {
            ignore_fn:Box::new(|_|false),
            enable_ignore:true,
            user_data,
            inner:lexer,
            buffer,
            current_token_span:0..0,
            is_eof:false,
        };

        ret.init_buffer();

        return ret;
    }

    pub fn finish(self)->D {
        self.user_data
    }

    /// Get a reference to the token stream
    #[inline]
    pub fn token_stream(&self)->&L {
        &self.inner
    }

    /// Get the span of the current token.
    pub fn span(&self)->Span {
        self.current_token_span.clone()
    }

    /// Enable the ignore function
    pub fn enable_ignore(&mut self) {
        self.enable_ignore=true;
    }

    /// Disables the ignore function until reactivated.
    pub fn disable_ignore(&mut self) {
        self.enable_ignore=false;
    }

    /// Sets the ignore function. By default, `self.enable_ignore` is true, so this function will
    /// be active immediately.
    pub fn set_ignore_fn<F:Fn(&T)->bool+'static>(&mut self,f:F) {
        self.ignore_fn=Box::new(f);
    }

    /// Creates an error with the given message at the current location.
    pub fn error<M>(&self,msg:M)->SimpleError<M> {
        SimpleError {
            span:self.span(),
            msg,
        }
    }

    /// Returns a reference to the token at the given index.
    pub fn lookahead(&mut self,index:usize)->&T {
        &self.raw_lookahead(index).0
    }

    /// Returns a reference to the span at the given index.
    pub fn lookahead_span(&mut self,index:usize)->Span {
        self.raw_lookahead(index).1.clone()
    }

    /// Returns a reference to the internal lookahead buffer at the given index.
    pub fn raw_lookahead(&mut self,index:usize)->&(T,Span) {
        debug_assert!(index<K,"Index out of bounds. There are only {} token(s) of lookahead",K);
        while self.should_skip(&self.buffer[index].0) {
            self.shift_lookahead(index);
        }
        &self.buffer[index]
    }

    /// Debug prints the internal lookahead buffer
    pub fn dbg_lookahead(&self,line:u32) {
        println!("DBG on line {}",line);
        for (i,t) in self.buffer.iter().enumerate() {
            println!("{}: {:?}",i,t);
        }
        println!();
    }

    /// Takes the next token without the span
    #[inline]
    pub fn take_token(&mut self)->T {
        self.take_token_span().0
    }

    #[inline]
    pub fn is_eof(&self)->bool {
        self.is_eof
    }

    /// Takes the next token and span
    pub fn take_token_span(&mut self)->(T,Span) {
        let mut tmp_tok=self.shift_lookahead(0);
        while self.should_skip(&tmp_tok.0) {
            tmp_tok=self.shift_lookahead(0);
        }
        self.current_token_span=tmp_tok.1.clone();
        return tmp_tok;
    }

    /// Attempt to match the given token to the next token. If it does not match, then return a
    /// [`SimpleError`] with the given error message.
    pub fn match_token<E>(&mut self,token:T,err_msg:E)->Result<(),SimpleError<E>>
    where T:PartialEq {
        let new_token=self.take_token();
        if new_token!=token {
            return Err(self.error(err_msg));
        }
        return Ok(());
    }

    // private helper functions

    fn init_buffer(&mut self) {
        for i in 0..K {
            self.buffer[i]=self.get_next_token();
        }
    }

    fn should_skip(&self,tok:&T)->bool {
        if self.enable_ignore {
            return (self.ignore_fn)(&tok);
        }
        return false;
    }

    fn get_next_token(&mut self)->(T,Span) {
        if let Some(t)=self.inner.next() {
            let span=self.inner.span();
            return (t,span);
        } else {
            self.is_eof=true;
            let span=self.inner.span();
            return (T::eof(),span);
        }
    }

    fn shift_lookahead(&mut self,from:usize)->(T,Span) {
        loop {
            let mut tmp_tok=self.get_next_token();
            for i in (from..K).rev() {
                mem::swap(&mut tmp_tok,&mut self.buffer[i]);
            }
            return tmp_tok;
        }
    }
}

/// A sane, simple error type made easy for parsing
#[derive(Debug)]
pub struct SimpleError<M=&'static str> {
    pub span:Span,
    pub msg:M,
}
impl SimpleError {
    pub fn eprint(&self) {
        eprintln!("{}",self.msg);
    }

    pub fn eprint_with_source(&self,source:&str,filename:&str) {
        let mut line_start=0;
        let mut line_end=0;
        let mut line_num=0;
        for line in source.lines() {
            line_num+=1;
            line_start=line_end;
            line_end+=line.len()+1;
            if line_end>self.span.start&&line_start<=self.span.start {
                break;
            }
        }

        let line_str=&source[line_start..line_end.saturating_sub(1)];
        let char_num=self.span.start-line_start;
        eprintln!("╭╢ [{}:{}] in {}",line_num,char_num,filename);

        eprintln!("│{}",line_str);

        eprint!(  "╰");
        for _ in 0..char_num {
            eprint!("─");
        }
        let end=self.span.end.min(line_end);
        for _ in 1..(end-self.span.start) {
            eprint!("┴");
        }
        eprintln!("┴╢ {}",self.msg);
    }
}
