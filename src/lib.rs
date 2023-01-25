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
//! left-associative AST is not immediatly obvious. One way is to have a two functions.
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


#[cfg(feature="logos_token_stream")]
use logos::{
    Lexer,
    Logos,
};
use std::{
    fmt::Debug,
    ops::Range,
    marker::PhantomData,
    mem,
};


pub type Span=Range<usize>;


/// Required for a token to be used.
pub trait Token:Debug {
    fn eof()->Self;
}

/// A stream of tokens with a few helpful functions.
pub trait TokenStream<'a,T:Token>:Iterator<Item=T> {
    /// The span of the current token
    fn span(&self)->Span;

    /// The full source
    fn source(&self)->&'a str;

    /// The remaining string
    fn remaining(&self)->&'a str;

    /// The string slice of the current token
    fn slice(&self)->&'a str;

    /// The span of the last token (EOF)
    fn end_span(&self)->Span {
        let source=self.source();
        source.len()..source.len()
    }
}
#[cfg(feature="logos_token_stream")]
impl<'a,T:Token+Logos<'a,Source=str>> TokenStream<'a,T> for Lexer<'a,T> {
    fn span(&self)->Span {
        self.span()
    }
    fn source(&self)->&'a str {
        self.source()
    }
    fn remaining(&self)->&'a str {
        self.remainder()
    }
    fn slice(&self)->&'a str {
        self.slice()
    }
}


/// A helper for returning two different types from a parser.
#[derive(Debug,PartialEq)]
pub enum Either<A,B> {
    /// One possible type.
    A(A),
    /// Another possible type.
    B(B),
}


/// For internal use in the lookahead buffer.
#[derive(Debug)]
struct TokenChange<T> {
    pub tok_span:(T,Span),
    /// Relative to the current line/column
    pub line:usize,
    /// Relative to the current line/column
    pub col:usize,
}

/// A parser with `K` tokens of lookahead and a few helpful methods. Can contain user data for
/// context-dependent parsing like significant whitespace or nested languages.
///
/// Note: K MUST BE greater than 0 or the lexer will always panic when attempting to access a
/// zero-length lookahead buffer.
pub struct LookaheadLexer<'a,const K:usize,T:Token,L:TokenStream<'a,T>,D> {
    /// If it returns true, then we ignore the token
    ignore_fn:Box<dyn Fn(&T)->bool>,
    enable_ignore:bool,
    user_data:D,
    inner:L,
    buffer:[TokenChange<T>;K],
    current_token_span:Span,
    line:usize,
    col:usize,
    _phantom:PhantomData<&'a ()>,
}
impl<'a,const K:usize,T:Token,L:TokenStream<'a,T>,D> LookaheadLexer<'a,K,T,L,D> {
    /// Create a new LookaheadLexer with the given lexer and user data.
    pub fn new(lexer:L,user_data:D)->Self {
        debug_assert!(K!=0);
        let buf=(0..K).map(|_|TokenChange {
            tok_span:(T::eof(),lexer.end_span()),
            line:0,
            col:0,
        }).collect::<Vec<_>>();

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
            line:0,
            col:0,
            _phantom:PhantomData,
        };

        ret.init_buffer();

        return ret;
    }

    /// Get a reference to the user data.
    pub fn user_data(&self)->&D {
        &self.user_data
    }

    /// Get a mutable reference to the user data.
    pub fn user_data_mut(&mut self)->&mut D {
        &mut self.user_data
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

    /// The 1-indexed column. Useful for displayable code.
    pub fn column(&self)->usize {
        self.col+1
    }

    /// The 1-indexed line. Useful for displayable code.
    pub fn line(&self)->usize {
        self.line+1
    }

    /// Creates an error with the given message at the current location.
    pub fn error(&self,msg:&'static str)->SimpleError {
        SimpleError {
            span:self.span(),
            line_1:self.line(),
            col_1:self.column(),
            msg,
        }
    }

    /// Returns a reference to the internal lookahead buffer at the given index.
    pub fn lookahead(&mut self,index:usize)->&(T,Span) {
        debug_assert!(index<K,"Index out of bounds. There are only {} token(s) of lookahead",K);
        if self.should_skip(&self.buffer[index].tok_span.0) {
            self.shift_lookahead(index);
        }
        &self.buffer[index].tok_span
    }

    /// Debug prints the internal lookahead buffer
    pub fn dbg_lookahead(&self) {
        println!();
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

    /// Takes the next token and span
    pub fn take_token_span(&mut self)->(T,Span) {
        let mut tmp_tok=self.shift_lookahead(0);
        while self.should_skip(&tmp_tok.0) {
            tmp_tok=self.shift_lookahead(0);
        }
        self.current_token_span=tmp_tok.1.clone();
        return tmp_tok;
    }

    /// The 0-indexed column
    pub fn column_raw(&self)->usize {
        self.col
    }

    /// The 0-indexed line
    pub fn line_raw(&self)->usize {
        self.line
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

    fn get_next_token(&mut self)->TokenChange<T> {
        if let Some(t)=self.inner.next() {
            let span=self.inner.span();
            let slice=self.inner.slice();
            let mut last=None;
            let mut line=0;
            let col;
            for (index,_) in slice.match_indices('\n') {
                line+=1;
                last=Some(index+1);
            }
            if let Some(newline_idx)=last {
                let remainder=&slice[newline_idx..];
                col=remainder.chars().count();
            } else {
                col=slice.chars().count();
            }
            return TokenChange {
                tok_span:(t,span),
                line,
                col,
            };
        } else {
            let span=self.inner.span();
            return TokenChange {
                tok_span:(T::eof(),span),
                line:0,
                col:0,
            };
        }
    }

    fn shift_lookahead(&mut self,from:usize)->(T,Span) {
        loop {
            let mut tmp_tok=self.get_next_token();
            for i in (from..K).rev() {
                mem::swap(&mut tmp_tok,&mut self.buffer[i]);
            }
            if from==0 {
                if tmp_tok.line!=0 {
                    self.line+=tmp_tok.line;
                    self.col=tmp_tok.col;
                } else {
                    self.col+=tmp_tok.col;
                }
            } else {
                self.buffer[from].line+=tmp_tok.line;
                self.buffer[from].col+=tmp_tok.col;
            }
            return tmp_tok.tok_span;
        }
    }
}

/// A sane, simple error type made easy for parsing
#[derive(Debug)]
pub struct SimpleError {
    pub span:Span,
    pub line_1:usize,
    pub col_1:usize,
    pub msg:&'static str,
}
impl SimpleError {
    pub fn eprint(&self) {
        eprintln!("[{}:{}]: {}",self.line_1,self.col_1,self.msg);
    }
}
