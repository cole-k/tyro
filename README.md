# tyro
Tyro is a toy language demonstrating bidirectional type checking of a row polymorphic lambda calculus.

# Type System
The type system is currently being extended, but it is based on [_Complete and Easy Bidirectional 
Typechecking for Higher-Rank Polymorphism_](https://arxiv.org/abs/1306.6032) by Dunfield and Krishnaswami.

You can find descriptions of the type system in [docs/](/docs/)

# Usage

Build the project by running from the root

```
$ stack build
```

Presently the only way to interface with tyro is via the REPL, which can be
accessed by running from the root

```
$ stack exec tyro-exe
```

# Evaluation
Tyro presently is call-by-value and directly substitutes terms for bound variables.

# Syntax
The syntax is presently basic, incomplete, and *subject to change*.

It pretty much looks and acts like a simple lambda calculus.

## Lambdas
Define lambdas as
```
\x -> body
```
where `x` is the variable being bound and `body` is a subexpression. The parentheses are not optional.
Note that there is no easy way to curry multiple arguments (e.g. `\x y z ->`); you must create a new lambda
for each.

## Application

Apply an expression to another by placing the two next to each other - the only separator needed is whitespace.

```
e1 e2
```

## Unit

The only concrete term is unit, which is represented as `()`.

## Parentheses

Parenthesize an expression that you want to be evaluated first. Due to the way
parsing works, lambdas typically need to be parenthesized, too.

```
(\x -> (\y -> x)) ((\z -> z) ())
```
evaluates to
```
\y -> ()
```
whereas
```
((\x -> (\y -> x)) (\z -> z)) ()
```
evaluates to
```
\z -> z
```

## Records

Create records using the syntax

```
{label1: term1, label2: term2}
```

for as many labels and terms as you want.

You can create the empty record by giving no content, i.e.

```
{}
```

## Record Projection

You can project a term from a record by usingt the syntax

```
record.label
```

e.g.

```
{a : (), b : (\x -> x)}.a
```
gives
```
()
```
and
```
{a : (), b : (\x -> x)}.b
```
gives

```
\x -> x
```

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
