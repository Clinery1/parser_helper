# About
A helpful little library for hand writing recursive ascent/descent parsers.
Makes lookahead much easier since you don't have to write a lookahead lexer
yourself.

# Recommended practices
Creating a newtype wrapper around [`LookaheadLexer`] and implementing [`Deref`](std::ops::Deref)
and [`DerefMut`](std::ops::DerefMut) on it for easy `self.take_token()` and other methods.

I also recommend not using entirely recursive ascent like a parser generator would, but instead
using helper functions to consolidate a lot of the pattern matching and make it similar to
recursive descent, but also keeping enough pattern matching in the main functions to avoid
left-recursion problems.

# Helpful patterns
## Left-associative ASTs
When using recursive ascent, it is very easy to make right-associative ASTs, but creating a
left-associative AST is not immediatly obvious. One way is to have a two functions.
```rust
// A non-recursive helper method that simply makes calling the recursive function easier
fn left_associative(&mut self)->Expr<'a> {
    let left=self.expr();
    return self.left_associative_inner(left);
}

// The recursive method that actually builds the left-associative AST
fn left_associative_inner(&mut self,left:Expr<'a>)->Expr<'a> {
    // Lookahead to see if the token is what we want.
    match self.lookahead(0) {
        Token::Add=>{},

        // Return the left side if we don't find the right token
        _=>return Ok(left),
    }

    // Take the token since we only used lookahead to verify its the right one
    self.take_token();

    // Get the right side of the expression. This is where the magic is. If we get the right
    // AND left side before recursing, then both are considered as the "new left side" when we
    // do finally recurse.
    let right=self.expr();

    // Map the current left and right for recursive calling
    let out=Expr::Add(Box::new([left,right]));

    return self.left_associative_inner(out);
}
```
For the more visual learners, here is a tree structure representing the function calls for the
left-associative methods:
```
  left
     /\
    /  inner ----> expr
   |        \     /
   |         right
    \       /
     combine
    /
left
    \
     inner
```

## Right-associative ASTs
These are much easier to do, so ill only provide a simple example.
```rust
// Right-associative parsers can be done much more easily.
fn right_associative(&mut self)->Expr<'a> {
    // Get the left expression
    let left=self.expr();

    // Match the lookahead and take the token like in the left-associative example.
    match self.lookahead(0) {
        Token::Add=>{},
        _=>return Ok(left),
    }
    self.take_token();

    // Here we recurse to get the right side instead of passing the right and left to the
    // recursive call.
    let right=self.right_associative();

    return Expr::Add(Box::new([left,right]));
}
```
Another visual graph:
```
     inner
    /     \
expr       inner
    \     /
    combine
           \
            output
```
