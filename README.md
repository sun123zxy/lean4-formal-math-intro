This book, or repository, contains the lecture notes and supplementary materials for the hobby course *Introduction to Formal Mathematics with Lean 4*, offered in Fall 2025 at Beijing Institute of Technology. It is designed as a companion to the course *Abstract Algebra* offered in the same semester, mainly intended for students with a background in undergraduate-level pure mathematics.

## Goals

The main goals of this course are

- to get used to think formally
- to migrate from set theory to dependent type theory
- to practice basic skills to translate statements and proofs into Lean 4
- to familiarize with the Mathlib 4 library
- to know how to find existing theorems, how the community works
- to acquire enough common senses to read the bibles (MiL, TPiL, Mathlib 4 Doc, etc.) by yourself for future formalization projects

## Approach

The style of this course is inspired by Kevin Buzzard's 2024 course on formalising mathematics in the Lean theorem prover and many other courses, that is: dozens of Lean files packed with well-organized examples and exercises should get you started. In fact, almost all chapters of this book is just a single Lean file with comments, converted into other formats later on. It is best to download the course repository and read it alongside a Lean 4 environment, so that you can try out the code examples and exercises interactively.

We try to organize the materials in a way that balances theory and practice. The main feature of this book is that we introduce Lean 4 and formalized mathematics by "illustrating the theory", that is: we accept the Mathlib definitions "as is", but reprove the major consequences that constitute the theory. Once a result is proved, we immediately relate it back to its Mathlib version (via a definitional equality, mostly), and use the Mathlib version in the subsequent developments. Hopefully, this may help you familiarize with the Mathlib API more quickly, while at the same time understand how the theory is builded up mathematically, without being lost in the huge Mathlib codebase.

We try to keep the materials well-organized, but due to the extra-curricular nature of the course, the lecture notes are often prepared in a hurry, so please forgive the messiness here and there. Due to the scope of the course, the limited time and my personal inability, several important topics, such as inductive types and inductive proofs, discrete mathematics, type classes and coercions, are only briefly touched upon or omitted. The readers are encouraged to explore these topics by themselves using the references provided at the end of this preface. We might fill in these gaps in the next versions of this book.

## Structure

The book is divided into four parts^[each entitled with a valid Lean 4 keyword]. The first part is purely introductory, advertising that formal mathematics and the Lean language is interesting and increasingly important nowadays. In the second part, we illustrate how first-order logic is built up in Lean's dependent type theory. Alongside the way, the readers are familiarized with Lean 4's syntax, semantics, and basic proof techniques. In the third part, we advance from `Prop` to `Type`, introducing numbers, functions, equalities and inequalities. This cultimates in [@sec-mathematical-analysis], where we do some mathematical analysis in Lean 4. The last part is devoted to algebraic structures, where we introduce the Mathlib philosophy of organizing algebraic structures, morphisms, substructures, and quotients, especially in the case of groups. We prove the first isomorphism theorem for groups as a grand finale.

## Instructions

We maintain an online version of the lecture notes with embedded Lean code if you prefer to read it in your browser. A printed PDF version is also provided as a souvenir, though no special effort has been made to resolve the hyperlinks.

For installation, first make sure you have installed Git, VSCode and Lean 4 extension for VSCode correctly. Refer to the installation guide <https://lean-lang.org/install/> if you haven't done so. Then execute the following commands in your terminal:

```bash
git clone git@github.com:sun123zxy/2025fall-lean4-teach.git # download the repository
cd 2025fall-lean4-teach
lake update # download Mathlib source files
lake exe cache get # download compiled Mathlib artifacts
```

To update the repository, make sure you have discarded any local changes (otherwise you may need to merge manually). Then execute the following commands in your terminal:

```bash
git pull
```

## Compiling the Book

Both the online and the PDF version of this book are prepared by \SunQuarTeX, a publishing system based on Quarto and \LaTeX. Refer to <https://github.com/sun123zxy/sunquartex> for more information.

## Portals

- Course repository: <https://github.com/sun123zxy/2025fall-lean4-teach>

- Online lecture notes: <https://sun123zxy.github.io/2025fall-lean4-teach/>

- Online compiler: <https://live.lean-lang.org>

- Community (Lean Zulip): <https://leanprover.zulipchat.com/>

- Lean 4 tactics cheatsheet: <https://leanprover-community.github.io/papers/lean-tactics.pdf>

## References

We recommend the following resources for further study of Lean and formalized mathematics.

Introductory videos and articles:

- CAV2024: <https://leodemoura.github.io/files/CAV2024.pdf>
- Terence Tao at IMO 2024: AI and Mathematics: <https://www.youtube.com/watch?v=e049IoFBnLA>
- Lean 的前世今生: <https://zhuanlan.zhihu.com/p/183902909>
- Natural Number Game: <https://adam.math.hhu.de/#/g/leanprover-community/nng4>
- Computational Trilogy - nLab: <https://ncatlab.org/nlab/show/computational+trilogy>

Bibles for further study:

- Mathematics in Lean (MIL): <https://leanprover-community.github.io/mathematics_in_lean/>

  A comprehensive tutorial for mathematicians to get started with Lean and the mathlib library. Focuses on building up mathematical structures.

- Theorem Proving in Lean 4: <https://leanprover.github.io/theorem_proving_in_lean4/>

  Strong emphasis on logic and dependent type theory. Excellent for both mathematicians and computer scientists.

- Lean Language Manual: <https://lean-lang.org/doc/reference/latest/>

  Comprehensive, precise description of Lean: a reference work in which Lean users can look up detailed information, rather than a tutorial intended for new users.

- Type Theory - nLab: <https://ncatlab.org/nlab/show/type+theory>

  If you want to understand the theoretical foundations of Lean, this is a good place to start.

- Other bibles: <https://lakesare.brick.do/all-lean-books-and-where-to-find-them-x2nYwjM3AwBQ>

Courses and lecture notes:

- Kevin Buzzard's 2024 course on formalising mathematics in the Lean theorem prover: <https://github.com/ImperialCollegeLondon/formalising-mathematics-2024>
