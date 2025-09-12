# Plan (WIP)

Week 1--12, pick a weekday evening, ~ 90 min / week

## Introduction to Formal Mathematics and the Lean Theorem Prover

- What is formalization

  - Curry--Howard correspondence

    - Mathematical proofs are in one-to-one correspondence with computer programs

- What (is Lean 4)

  - A typical Lean file

- Why formalize

  - The rise of AI
    
    AI excels in Python. Why not Lean?

    - Automated theorem proving

      - especially those "abstract nonsense"
    
    - Natural language to formal language

      - automatically transplanting textbooks and papers into Lean
      - Converse? Already happening!

    - Proposing conjectures

      - On which facts should we care about

  - Rigor matters

    - It's the foundation of mathematics
    
    - Inprecise natural language often leads to misunderstandings and glitches

      - Especially when proofs get longer and longer

    - formalization fully confirms the correctness of a theorem
      
      - things that are too "technical" (boring) or simply impossible to verify by oneself
      
        - e.g. classification of finite simple groups

        - e.g. "technical"

        > "I spent much of 2019 obsessed with the proof of this theorem, almost getting crazy over it. In the end, we were able to get an argument pinned down on paper, but I think nobody else has dared to look at the details of this, and so I still have some small lingering doubts." --- [Peter Scholze](https://www.nature.com/articles/d41586-021-01627-2)

  - manipulating tons of theorems and proofs with mature software engineering techniques

    - referencing existing theorems as dependencies

    - collaborative work across the globe

    > The beauty of the system: you do not have to understand the whole proof of FLT in order to contribute. The blueprint breaks down the proof into many many small lemmas, and if you can formalise a proof of just one of those lemmas then I am eagerly awaiting your pull request. --- [Kevin Buzzard on the FLT Project](https://leanprover-community.github.io/blog/posts/FLT-announcement/)

  - Formalization as learning

    - proofs with infinite detail

      - intuitive textbooks, rigorous formalization

    - makes us understand things better

      - Global: How to build natural numbers from scratch?

        - [natural number game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
        - [A journey to the world of numbers, by Riccardo Brasca](https://github.com/riccardobrasca/Numbers)
      
      - Local: reducing the cognitive load

        - (With good organization at the beginning) you can focus on small parts of the proof at a time

- Why now formalize

  - mathematician-friendly languages, interfaces, tools and community emerges

  - Mathlib 4 is expanding explosively
 
    - undergraduate may contribute: some low fruits

- What you will learn

- Drawbacks

  - Formalization is tedious in its nature, Lean 4 is no exception

  - Type conversions can be an extra burden (exclusive for type-theory-based systems)

  - Knowledge needs to be re-learned before being referenced

- References

  - Introductory:
  
    - [CAV2024](https://leodemoura.github.io/files/CAV2024.pdf)
    - [Terence Tao at IMO 2024: AI and Mathematics](https://www.youtube.com/watch?v=e049IoFBnLA)
  
  - Bibles

    - Theorem Proving in Lean 4 (Emphasize type theory)
    - Mathematics in Lean 4 (Practical bible for mathematicians)
    - Lean Language Manual (Details)

  - Community

    - Lean Zulip

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