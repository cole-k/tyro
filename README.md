# tyro
Tyro is a toy language demonstrating bidirectional type checking of a row polymorphic lambda calculus.

# Type System
The type system is currently being extended, but it is based on [_Complete and Easy Bidirectional 
Typechecking for Higher-Rank Polymorphism_](https://arxiv.org/abs/1306.6032) by Dunfield and Krishnaswami.

# Evaluation
Tyro presently is call-by-value and directly substitutes terms for bound variables.

# Syntax
The syntax is presently basic, incomplete, and subject to change.

It pretty much looks like a simple lambda calculus with explicit parethesization to make parsing easier.

## Lambdas
Define lambdas as
```
(\x -> body)
```
where `x` is the variable being bound and `body` is a subexpression. The parentheses are not optional.
Note that there is no easy way to curry multiple arguments (e.g. `\x y z ->`); you must create a new lambda
for each.

## Application

Apply an expression to another by placing the two in parentheses with a space separating, as shown below.

```
(e1 e2)
```

## Unit

The only concrete term is unit, which is represented as `()`.

## Comments
Use `-- comment` for line comments and `{- comment -}` for block comments.

## Sample Code

Consider the expression below.
```
(((\f -> (\x -> (f x))) (\x -> x)) () )
```
After one beta reduction, it will be
```
((\x -> ((\x -> x) x)) ())
```
which will beta reduce after some steps to `()`.

# Usage
Presently the only way to interface with tyro is via some debug functions (found mostly in `Typing`).
This language will be polished once its type system is more fleshed out. I'll update this README once
it gets to the stage where it can actually be used. The descriptions of syntax primarily serve as reference
for contributors.
