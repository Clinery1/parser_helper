use logos::Logos;
use crate::{
    Span,
    Token,
    TokenStream,
};


#[repr(transparent)]
pub struct LogosTokenStream<'a, T: Logos<'a>>(pub logos::Lexer<'a, T>);
impl<'a, T: Logos<'a>> Iterator for LogosTokenStream<'a, T> {
    type Item = T;
    fn next(&mut self)->Option<T> {
        if let Ok(t) = self.0.next()? {
            return Some(t);
        }
        return None;
    }
}
impl<'a, T: Logos<'a>> From<logos::Lexer<'a, T>> for LogosTokenStream<'a, T> {
    fn from(o: logos::Lexer<'a, T>)->Self {
        Self(o)
    }
}
impl<'a, T: Token + Logos<'a, Source = str>> TokenStream<T> for LogosTokenStream<'a,T> {
    type Slice = &'a str;
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
