# Eriun

This is my attempt to do a dependently typed programming language. It is inspired by:  
- [Homotopy Type Theory](https://homotopytypetheory.org/book/)
- [Simpler, Easier!](https://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html?m=1)
- [From realizability to induction via dependent intersection](https://www.sciencedirect.com/science/article/pii/S0168007218300277?ref=pdf_download&fr=RR-2&rr=8a9706eecc573c95)

**Table of contents:**
- [Syntax highlighting](#Syntax-highlihting)
- [Grammar](#Grammar)
- [Erasure](#erasure)
  - [Erasure mark on lambda](#Erasure-mark-on-lambda)
- [Cumulative Universes](#Cumulative-Universes)
  - [Level](Level)
- [Dependent intersection](#Dependent-intersection)
- [Beta equivalence](#Beta-equivalence)
- [Examples](#Examples)
  - [Todo](#Todo)
    - [Nat](#Nat)

## Name

The name is symply the first letters of the main compenents of this language:
- er: Erasure
- i: Intersections (dependent ones)
- un: Universes

## Syntax highlihting

There is a tree-sitter parser in this repository [tree-sitter-eriun](https://github.com/xayon40-12/eriun/tree/main/tree-sitter-eriun) which can be used for syntax highlighting.

### Helix

Here is a setup for the [Helix editor](https://helix-editor.com/).

- In your helix `language.toml` (probably in `~/.config/helix/`), add a language entry
  ```toml
  [[language]]
  name = "eriun"
  scope = "source.eriun"
  roots = ["main.eriun"]
  file-types = ["eriun"]
  comment-tokens = "--"
  block-comment-tokens = { start = "{- ", end = " -}" }
  injection-regex = "^eriun$"
  ```
  so that the language is recognised correctly.
- Then add a grammar entry for the tree-sitter parser:
  ```toml
  [[grammar]]
  name="eriun"
  source={git="https://github.com/xayon40-12/eriun.git", subpath="tree-sitter-eriun", rev="main"}
  ```
- Once the grammar is added to `language.toml`, you need to fetch it and build it with
  ```bash
  helix -g fetch
  helix -g build
  ```
- And finally, you need to make the tree-sitter queries accessible.  
  - First, create a `queries/` folder if it does not already exists in your helix `runtime/` folder (most likely next to `language.toml` in `~/.config/helix/`).
  - Then, from inside the `queries/` folder, create a symbolic link to the queries which where fetched by helix:
    ```bash
    ln -s ../grammars/sources/eriun/tree-sitter-eriun/queries/ eriun
    ```

**NOTE**: If the tree-sitter in this repository changes, you might need to first delete the grammar repository fetched by Helix in the `runtime` repository (`runtime/grammars/sources/eriun`) and then use `helix -g fetch` and `helix -g build` again.

#### Themes

Tree-sitter allows to provide a large variety of highlight queries. However, every themes only handle a handful of all these available queries. I recommend to try the theme "catppuccin_mocha" for this language as it covers most of the highlight queries used in this language. It is set as default in this github repository thanks to the `.helix/config.toml`, so opening any `.eriun` with `helix` from inside this repository will use the "catppuccin_mocha" theme.

## Grammar

In the definition of the grammar for this language, a symbol denoted by `S` corresponds to any non empty sequence of characters which does not include any whitespaces and which does not already appear as literal in the later grammar.
A context is a list of symbols.
A symbol `S` that appears in a context named `l` is denoted by `elem(S,l)`.
A symbol matching any symbol in the context `l` is denoted by `any(l)`.
An expression with an attached context `l` is denoted by `expr[l]`.
An expression with an available symbol `S` in addition to a context `l` is denoted by `expr[l,S]`.
A valid expression with context `l` is any sequence of character matching the following 8 lines, where any letter or symbol which was not introduced betneen backticks in the previous centenses has to be matched literally (except the line number):
```
 1. @S = expr[l]; expr[l,S]
 2. #L
 3. #U 'levels'
 4. (S: expr[l]) expr[l,S]
 5. <S: expr[l]> expr[l,S]
 6. expr[l] :> expr[l]
 7. expr[l] expr[l]
 8. expr[l] 'expr[l]
 9. any(l)
10. S: expr[l] /\ expr[l,S]
11. expr[l].1
12. expr[l].2
13. [expr[l]]
```
The `;` can be replaced by a newline followed by at least one space.
Each line in order correspond to:
1. declaration of a named expression that can be used in later expressions
2. type of universe levels
3. a universe whose rank correspond to the provided 'levels' which should be a comma separated list of level (see [Level](#Level)) which represent the maximum of each provided levels.
4. decleration of a dependent lambda `(symbol: type) expr`
5. decleration of a dependent lambda whose parameter is erased `<symbol: type> expr`
6. typing of the right expression with the first one as its type
7. application, left associative
8. application of an erased value, left associative
9. a symbol available in the context l
10. a dependent intersection
11. term of the dependent intersection converted to the type of the left part
12. term `t` of the dependent intersection converted to the type of the right part (where the symbol `S` is replaced by `t.1`)
13. parens to force a particular association order

## Erasure
The erasure correpsond to the computation part of an expression. For instance, the identity is the function that returns its input unchanged. However, in the formalism proporsed here, additional components are needed to preperly type the identity function:
```eriun
<i: #L> <T: #U i> (t: T) T :> t
```
a level `i` and a generic type `T` are needed to type the identity function. They are therefor marked as erased with `'`. Erasing this expression will remove all symbols marked as erased and will strip all the remaning symbols of their types. After erasure, the above identity function becomes:
```eriun
t :-> t
```
which is the identity function in untyped lambda calculus.

## Cumulative Universes
A universe is a type of type indexed by a level. For a level `l`, the corresponding universe is denoted by `U l`.
A valid level can be: a literal positive integer, a symbol of the special level type `L`, the sum of a level with a literal positive integer, the max of two levels.

Cumulative universes are such that for any level `l1` strictly smaller than `l2` we have `U l1` of type `U l2`. A non-cumulative universe system would only allow that `U l1` is of type `U l2` when `l2 = l1 + 1`.

```eriun
(l1: #L) (l2: #L) (A: #U l1) (B: #U l2) U l1,l2
```
where `l1,l2` correspond to the maximum of `l1` and `l2`

### Level

A valid level can be a symbol of type `#L`, a literal natural number, the sum of a level and a literal natural number, or the maximum of two levels.

## Dependent intersection
For a value `a` of type `A` and a value `b` of type `B a`, the pair `a ^ b` is of type `a: A /\ B a` if the erasure of `a` and `b` are equal.
A value `x` of type `a: A /\ B a` can be changed to be of type `A` with the notation `x.1` and it can be changed to be of type `B x.1` with notation `x.2`. In both cases, the value can be returned to the original intersection type by appending a `.0`. Thus `x.1.0` and `x.2.0` are both of type `a: A /\ B a`.

## Beta equivalence
Two values (term or type) are beta-equivalent if the normal form of their erasure is the same. for instance:
```eriun
[c2nat [CSucc n]].1 => [CSucc n] Nat Succ Zero => [P :-> s :-> z :-> s [n P s z]] Nat Succ Zero => Succ [n Nat Succ Zero] => P :-> s :-> z :-> s [[n Nat Succ Zero] P s z]
CSucc [c2nat n].1 => CSucc [n Nat Succ Zero] => P :-> s :-> z :-> s [[n Nat Succ Zero] P s z]
```
where the symbol `=>` here separates the transformation steps.

If two types `A` and `B` are beta-equivalent `A =_beta B`, then a value `a` of type `A` can be converted to type `B` with `Beta a`.

## Examples

See files with `.eriun` extension in the [math](math/) folder.
