# Plan (WIP)

Week 1--12, pick a weekday evening, ~ 90 min / week

## Introduction to Formal Mathematics and the Lean Theorem Prover

blah

## Hello World

- Use the interactive window

- A typical Lean file

- Setting up the environment

  - Lean 4 Web
  - Github Codespace
  - local install

## Logic
  
- `exact`
- IMPLIES: `intro` (construct IMPLIES / FORALL), `specialize` `apply` (eliminate IMPLIES / FORALL)
- AND / OR: `constructor` (construct AND), `left` `right` (construct OR), `rcases` (eliminate AND & OR)
- EXISTS: `use` (construct EXISTS), `rcases` (eliminate EXISTS)
- NOT: `push_neg`, `exfalso`, `by_contra`, `by_contrapose`
- `have` `let` `set`

[Tactic cheatsheet](https://github.com/fpvandoorn/LeanCourse24/blob/master/lean-tactics.pdf)

## Numbers, Functions and Sets

$\mathbb N$, $\mathbb R$ and $\mathbb C$:

- `rfl`, `rw`, use existing theorems like `add_assoc`
- `ring`
- Inequality: `le_trans` `calc`, `linearith`

Functions:

- Different ways to declare, to construct functions
- `funext`

Sets:

- type + prop

- First steps on coercions

## Dependent Type Theory in Lean 4
  
- Everything has a type: Universe hierarchy
- Dependence: FORALL, EXISTS
- First-class symbols: IMPLIES
- Review: Proof as an element of a proposition, IMPLIES as a function
- Curry--Howard correspondence
- Review: Construction and elimination in the `Prop` universe
- Construction and elimination in the `Type` universe (Inductive types intro)
- Equality
  - Definitional one and propositional one
  - `rfl` = `Eq.refl`, `congr`

## Mathematical Analysis: Taking Limits on the Real Numbers

- Absolute value: How to Find Theorems?
  
  - name guessing
  - `exact?`, `apply?`
  - Mathlib 4 Doc 
  - LLM / AI Search: LeanSearch, LeanExplore
  - Directly use AI

- TendsTo

## Random Lean 4 Tips
  
Useful Tactics:

- `symm`
- `apply_fun`
- `simp`, `dsimp`, `simp_rw`
- `linearith`, `omega`, `aesop`, `grind`, `tauto`
- `change`, `replace`, `refine`
- `ext`, `funext`
- `congr`, `gcongr`, `grw`
- `suffices`

Conversion mode

Structuring a Lean project

- `section`, `namespace`
- `import`, `xxx.xxx`

Implicit Arguments

- `{x : Nat}`, `@`, `(x := 3)`

## Abstract Algebra: Group, rings and fields

- `field_simp`

## Quotient Types and Universal properties

## Inductive Types and Induction methods

## Classes and Instances

## Coercions
  
- `norm_cast`, `push_cast`
- `lift`, `rify`