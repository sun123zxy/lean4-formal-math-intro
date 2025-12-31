/-
Diffrent people formalize things differently.
This is especially true when it comes to substructures and quotients.

In this file, we show how to use the Mathlib's API for substructures, from subsets to subgroups.
It's a sophisticated hierarchy that I'm still trying to fully understand myself.
For the philosophy behind this design,
see [MiL](https://leanprover-community.github.io/mathematics_in_lean/) chapter 8.
-/

import Mathlib

/-
## Subsets

### Objects

In the previous lectures, we regarded types as sets intuitively.
This is not flexible when one wishes to restrict to only a fraction of the elements of a type.
It's also hard to implement unions and intersections of sets this way.
Mathlib provides a dedicated type `Set α`, consists of all the subsets of a type `α`.
-/
section

variable (α : Type*) (s t u : Set α) (a : α)

#print Set
/-
You can see that `Set α` is defined as `α → Prop`.

This means a subset `s : Set α` tells you, for each `a : α`,
whether `a` belongs to `s` or not.
This proposition is denoted by `a ∈ s`, `Set.mem s a`, or `s.Mem a`.

Note that you are not supposed to write `s a` directly.
The function definition of `Set α` should be regarded as an implementation detail.
-/
#check a ∈ s
#check s.Mem a

/-
A subset can be constructed using the set-builder notation
`{x : α | p x}` or `setOf p`,
where `p : α → Prop` is a predicate on `α`.
-/
#check setOf (fun x ↦ x = a)
example : setOf (fun x ↦ x = a) = {x : α | x = a} := by rfl
example : setOf (fun x ↦ x = a) = {a} := by rfl
example : setOf (fun x ↦ x = a) = Set.singleton a := by rfl

example : Set ℕ := {n | n > 514}
example (n : ℕ) : n ∈ {x | x > 514} ↔ n > 514 := by rfl

/- the empty subset -/
#check (∅ : Set α)
example : ∅ = {x : α | False} := by rfl
example : a ∈ (∅ : Set α) ↔ False := by rfl
#check Set.mem_empty_iff_false -- corresponding `simp` lemma

/- the universal subset -/
#check (Set.univ : Set α)
example : Set.univ = {x : α | True} := by rfl
example : a ∈ Set.univ := by trivial
#check Set.mem_univ -- corresponding `simp` lemma

/- the complement of a subset -/
#check Set.compl s
#check sᶜ
example : sᶜ = {x | x ∉ s} := by rfl
example : a ∈ sᶜ ↔ a ∉ s := by rfl
#check Set.mem_compl -- corresponding `simp` lemma

/-
Subset relation.
Somehow you may use any proof of `s ⊆ t` like a function.
It eats a proof of `a ∈ s` and produces a proof of `a ∈ t`.
-/
#check Set.Subset s t
#check s ⊆ t
example : s ⊆ t ↔ ∀ x : α, x ∈ s → x ∈ t := by rfl
example (ha : a ∈ s) (hst : s ⊆ t) : a ∈ t := hst ha
#check Set.mem_of_subset_of_mem -- corresponding Mathlib lemma

/- intersection of two subsets -/
#check Set.inter s t
#check s ∩ t
example : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := by rfl
#check Set.mem_inter_iff -- corresponding `simp` lemma

/- union of two subsets -/
#check Set.union s t
#check s ∪ t
example : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := by rfl
#check Set.mem_union -- corresponding `simp` lemma

/-
`ext` tactic reduces subset equality to element membership.
Fundamentally this is implemented using function & propositional extensionality,
hence not a definitional one.
-/
#check Set.ext
example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

/- [EXR] De Morgan's law for sets -/
example : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  constructor
  · intro ⟨h₁, h₂⟩
    rcases h₂ with (h₂ | h₂)
    · left
      exact ⟨h₁, h₂⟩
    · right
      exact ⟨h₁, h₂⟩
  · tauto_set

#help tactic tauto_set -- Wheelchair tactic for set equations

end

/-
### Morphisms

Functions between types induce functions between subsets.
-/
section

variable {α β : Type*} (f : α → β) (s : Set α) (t : Set β) (a : α) (b : β)

/- range of a function `Set.range f` -/
#check Set.range f
example : Set.range f = {y | ∃ x, f x = y} := by rfl
example : Set.range f = {f x | x : α} := by rfl -- set-builder notation for range
example : b ∈ Set.range f ↔ ∃ x, f x = b := by rfl
#check Set.mem_range -- corresponding `simp` lemma

/- image of a subset `Set.image f s` -/
#check f '' s
#check Set.image f s
example : f '' s = {y | ∃ x ∈ s, f x = y} := by rfl
example : f '' s = {f x | x ∈ s} := by rfl -- set-builder notation for image
example : b ∈ f '' s ↔ ∃ x ∈ s, f x = b := by rfl
#check Set.mem_image -- corresponding `simp` lemma

/- Preimage of a subset `Set.preimage f t` -/
#check f ⁻¹' t
#check Set.preimage f t
example : f ⁻¹' t = {x | f x ∈ t} := by rfl
example : a ∈ f ⁻¹' t ↔ f a ∈ t := by rfl
#check Set.mem_preimage -- corresponding `simp` lemma

/-
Note the following is not a definitional equality.
The last step invokes `propext`, which destroys definitional equality.
It has some unfortunate consequences in later discussions,
when additional structure is involved.
-/
example : f '' Set.univ = Set.range f := by
  ext x
  rw [Set.mem_range, Set.mem_image]
  simp only [Set.mem_univ, true_and]
#check Set.image_univ -- corresponding `simp` lemma

/-
We teach an syntax sugar of `rcases` here:
Say we are given `h : y ∈ Set.range f`,
it is by definition `h : ∃ x, f x = y`.
`rcases h with ⟨x, rfl⟩` will create a new variable `x : α`,
and replace all occurrences of `y` in the context with `f x`.

Feel free to combine it with `rintro`.
-/
example : Set.range f ⊆ t ↔ ∀ x, f x ∈ t := by
  constructor
  · intro h x
    apply h
    use x
  · intro h y hy
    rcases hy with ⟨x, rfl⟩
    exact h x
#check Set.range_subset_iff -- corresponding Mathlib theorem

/- [EXR] The so-called Galois connection between image and preimage. -/
example : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  constructor
  · intro h x hx
    simp only [Set.mem_preimage]
    apply h
    simp only [Set.mem_image]
    use x
  · rintro h y ⟨x, hxs, rfl⟩
    specialize h hxs
    simp only [Set.mem_preimage] at h
    exact h
#check Set.image_subset_iff -- corresponding `simp` lemma

end

/-
### Exercises on functions and subsets

As an (a little bit advanced) exercise, prove that `f` has both inverses iff it is bijective.
You might need the axiom of choice to construct such inverses.
Familarize yourself with the following definitions if you haven't seen them before.
-/
section

#check Function.comp
#check Function.Injective
#check Function.Surjective
#check Function.Bijective

#check Function.LeftInverse
#check Function.RightInverse

#check Classical.choose

#check Equiv

/- [EXR] your goal -/
#check Equiv.ofBijective

/-
For those seeking a more challenging exercise, try proving the Bernstein–Schroeder theorem.
See MiL chapter 3 for an answer.
-/
#check Function.Embedding.schroeder_bernstein

end

/-
### Subset as a type

At most of the time, we prefer to write `a ∈ s`-like expressions,
to indicate that `a : α` belongs to the subset `s : Set α`.
We prefer this way because this does not create an extra psychological hierarchy in types:
(recall that `Set α := α → Prop`, which is in the same universe as `α`)

```default
Type u    α    Set α
          |      |
Term      a      s
```

However, there are situations where we want to treat `a` as an element of `s` directly:
for example, when we wish to obtain a surjection from a function to its range.

Lean provides a way to do this:
directly write `a : s` to say `a` is an element of the subset `s`.
-/
section

variable {α : Type*} (s : Set α)

variable (a : s)
#check a

/-
Note that `a` is now of type `↑s`, not `α`.
This means that `a` is actually a bundled structure consisting of

- an element of type `α`, denoted by `a.val` or `↑a`
- a proof of `a.val ∈ s`, denoted by `a.property`
-/
#check a.val
#check a.property

/-
In tactic mode, `rcases` may be used to destructure `a : s` into its components.
-/
example : a.val ∈ s := by
  rcases a with ⟨v, p⟩
  exact p

/-
Given an `v : α` and a proof `p : v ∈ s`,
we can construct an element of type `s` using `⟨v, p⟩`.
-/
example (v : α) (p : v ∈ s) : ∃ a : s, a.val = v := by use ⟨v, p⟩

/-
Mechanically, when Lean sees `a : s`, it automatically
coerces `s` to a subtype of `α`, defined as `{x : α // x ∈ s}`.
That is the coercion sign you see in the result `a : ↑s` of the type check.
And hence the `a.val` and `a.property` is acutally `Subtype.val a` and `Subtype.property a`.

Though psychologically we have `a : s` and `s : Set α`, the actual hierarchy remains flat:

```default
Type u      α       Set α        ↑s
            |         |          |
Term      a.val       s          a
```
-/
#check Subtype
#check {x : α // x ∈ s}
example : {x : α // x ∈ s} = ↑s := by rfl

/-
It's important to recognize that `Subtype.val : ↑s → α` is injective.

Note that `ext` is a general tactic to reduce
an equality of structures into equalities of their components.
You can use `rcases` to do this manually if you wish.
-/
example (a₁ a₂ : s) (h : a₁.val = a₂.val) : a₁ = a₂ := by ext; exact h
#check Subtype.val_injective

end

/-
### Functions restricted to subsets
-/
section

variable {α β : Type*} (f : α → β) (s : Set α) (s' : Set α) (t : Set β)

/-
Given a function `f : α → β`,
we can restrict its domain to a subset `s : Set α`.
-/
#check Set.restrict
/- the universal property of `Set.restrict` -/
example : s.restrict f = f ∘ Subtype.val := by rfl
#check Set.restrict_apply -- corresponding `simp` lemma

/- the range of a restricted function -/
example : Set.range (s.restrict f) = f '' s := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    dsimp
    use x.val, x.property
  · rintro ⟨x, hx, rfl⟩
    use ⟨x, hx⟩
    dsimp
#check Set.range_restrict -- corresponding `simp` lemma

/-
Given a function `f : α → β`,
we can also restrict its codomain to a subset `t : Set β`,
once we know that `Set.range f ⊆ t`.
-/
#check Set.range_subset_iff -- recall what we proved earlier
#check Set.codRestrict
example (h : ∀ x, f x ∈ t) : t.codRestrict f h = fun x ↦ ⟨f x, h x⟩ := by rfl

/- the universal property of `Set.codRestrict` -/
example (h : ∀ x, f x ∈ t) : Subtype.val ∘ (t.codRestrict f h) = f := by
  funext x
  rfl
#check Set.val_codRestrict_apply -- corresponding `simp` lemma

/- restriction on range -/
#check Set.rangeFactorization
example : Set.rangeFactorization f = (Set.range f).codRestrict f (by simp) := by rfl
#check Set.rangeFactorization_coe -- universal property of range restriction

end

/-
## Subsemigroups

### Objects

A `Subsemigroup G` is a subset of a `Semigroup G`
that is closed under the multiplication.

It's actually a bundled structure consisting of a
subset and a proof of closure.
To use it like a subset,
Mathlib registers `Subsemigroup G` as an instance of `SetLike G`.
It provides coercion from `Subsemigroup G` to `Set G`,
so for `H : Subsemigroup G`,
you can use `a ∈ H` to mean `a` belongs to the underlying subset of `H`.
-/
section

variable (G : Type*) [Semigroup G]
variable (H₁ H₂ : Subsemigroup G) (a b : G)
example (ha : a ∈ H₁) (hb : b ∈ H₁) : a * b ∈ H₁ := mul_mem ha hb

/- the whole semigroup as a subgroup -/
#check (⊤ : Subsemigroup G)
example : (⊤ : Subsemigroup G) = ⟨Set.univ, by simp⟩ := by rfl
#synth Top (Subsemigroup G)

/- the empty subset as a subgroup -/
#check (⊥ : Subsemigroup G)
example : (⊥ : Subsemigroup G) = ⟨∅, by simp⟩ := by rfl
#synth Bot (Subsemigroup G)

/-
The partial order structure on subsemigroups is
inherited from subset relation of subsets.
-/
example : H₁ ≤ H₂ ↔ H₁.carrier ⊆ H₂.carrier := by rfl

/- intersection of two subsemigroups -/
#check H₁ ⊓ H₂
#synth Min (Subsemigroup G)

example : H₁ ⊓ H₂ = ⟨H₁ ∩ H₂, by
  intro a b ha hb
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  constructor
  all_goals apply mul_mem
  all_goals assumption
⟩ := rfl

/- product of two subsemigroups. -/
#check H₁ ⊔ H₂
#synth Max (Subsemigroup G)

/-
Definition of `H₁ ⊔ H₂` is more involved, relying the lattice structure of `Subsemigroup G`.
it is defined as the infimum of all subsemigroups containing both `H₁` and `H₂`,
where the infimum is given by intersection.
-/
#synth CompleteLattice (Subsemigroup G)

/-
This is characterized by the following properties.
-/
#synth SemilatticeSup (Subsemigroup G)
example : H₁ ≤ H₁ ⊔ H₂ := by apply le_sup_left
example : H₂ ≤ H₁ ⊔ H₂ := by apply le_sup_right
example (K : Subsemigroup G) (h1 : H₁ ≤ K) (h2 : H₂ ≤ K) : H₁ ⊔ H₂ ≤ K :=
  sup_le h1 h2

end

/-
### Morphisms

Let's see how `MulHom` interacts with `Subsemigroup`.
-/
section

variable {G₁ G₂ : Type*} [Semigroup G₁] [Semigroup G₂]
         (f : G₁ →ₙ* G₂) (H₁ : Subsemigroup G₁) (H₂ : Subsemigroup G₂)

/-
The image of a subsemigroup under a `MulHom` is also a subsemigroup.
-/
#check Subsemigroup.map f H₁
#check H₁.map f

example : Subsemigroup.map f H₁ = ⟨f '' H₁, by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    use a * b, H₁.mul_mem ha hb
    rw [map_mul]
    ⟩ := by rfl

/-
The preimage of a subsemigroup under a `MulHom` is also a subsemigroup.
-/
#check Subsemigroup.comap
#check H₂.comap f

example : Subsemigroup.comap f H₂ = ⟨f ⁻¹' H₂, by
  intro x y hx hy
  simp only [Set.mem_preimage] at hx hy ⊢
  rw [map_mul]
  exact mul_mem hx hy
⟩ := by rfl

/-
To define the range of a `f : G₁ →ₙ* G₂`,
a common idea is to adopt `(⊤ : Subsemigroup G₁).map f`.
Unfortunately, this makes the underlying set being `f '' (univ : Set G₁)`,
which is not definitionally equal to `Set.range f`.
It will also cause `x ∈ ⊤` conditions in later proofs, redundant and annoying.

Hencee Mathlib define the range with some refinement:
They manually replace the underlying set of `(⊤ : Subsemigroup G₁).map f` with `Set.range f`.

See Note [range copy pattern](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Submonoid/Operations.html#MonoidHom.Mathlib.LibraryNote.%C2%ABrange%20copy%20pattern%C2%BB)
for an official explanation.
-/
#check MulHom.srange

/- the desired definitional equality -/
example : MulHom.srange f = ⟨Set.range f, by
  rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
  use a * b
  rw [map_mul]
⟩ := by rfl

example (x : G₂) : x ∈ MulHom.srange f ↔ x ∈ Set.range f := by rfl
#check MulHom.mem_srange -- corresponding Mathlib theorem

end

/-
### `Subsemigroup` as a type

Sometimes we treat subset as a type directly. The same applies to subsemigroups.
-/
section

variable {G : Type*} [Semigroup G] (H : Subsemigroup G)

variable (a : H)
#check a
example : ↥H = {x : G // x ∈ H} := by rfl -- Hence the meaning of `a : H` is coerced
#check a.val
#check a.property

end

/-
### `MulHom` restricted to subsemigroups

Upgraded version of `Set.restrict` and `Set.codRestrict` for `MulHom`.
-/
section

variable {G₁ G₂ : Type*} [Semigroup G₁] [Semigroup G₂]
         (f : G₁ →ₙ* G₂) (H₁ : Subsemigroup G₁) (H₂ : Subsemigroup G₂)

#check MulHom.restrict
#check MulHom.restrict_apply -- universal property of restriction
#check MulHom.codRestrict
#check MulHom.codRestrict_apply_coe -- universal property of codomain restriction

#check MulHom.srangeRestrict -- restriction on range

end

/-
## Submonoids

A `Submonoid M` is a subsemigroup of a `Monoid M` that contains the identity element.
-/
section

variable (G : Type*) [Monoid G]
variable (H₁ H₂ : Submonoid G) (a b : G)

example : a ∈ H₁ → b ∈ H₁ → a * b ∈ H₁ := by apply mul_mem
example : (1 : G) ∈ H₁ := by apply one_mem

/-
The whole monoid as a submonoid.
Note the use of `with`,
to extend the underlying `Subsemigroup` with the proof of containing `1`.
-/
#check (⊤ : Submonoid G)
example : (⊤ : Submonoid G) = {(⊤ : Subsemigroup G) with
  one_mem' := by
    change 1 ∈ (⊤ : Set G)
    apply Set.mem_univ
} := by rfl
#synth Top (Submonoid G)

/-
The trivial submonoid consisting of only the identity element.
Note the difference from `⊥ : Subsemigroup G`,
which is the empty set.
-/
#check (⊥ : Submonoid G)
example : (⊥ : Submonoid G) = {
  carrier := {1}
  one_mem' := by rfl
  mul_mem' := by
    rintro x y hx hy
    simp only [Set.mem_singleton_iff] at hx hy ⊢
    rw [hx, hy, one_mul]
} := by rfl
#synth Bot (Submonoid G)

/-
We don't repeat tedious lattice structure part, which is similar to those for `Subsemigroup`.
-/
#synth CompleteLattice (Submonoid G)

end

/-
### Morphisms

`MonoidHom` interacts with `Submonoid` similarly to `MulHom` and `Subsemigroup`.
-/
section

variable {G₁ G₂ : Type*} [Monoid G₁] [Monoid G₂]
         (f : G₁ →* G₂) (H₁ : Submonoid G₁) (H₂ : Submonoid G₂)

/-
We still have image and preimage of submonoids,
which can be built on top of those for subsemigroups,
with extra care to verify the identity element membership.
-/

#check Submonoid.map
example : Submonoid.map f H₁ = { Subsemigroup.map f.toMulHom H₁.toSubsemigroup with
  one_mem' := by
    simp
    use 1, H₁.one_mem
    rw [map_one]
} := by rfl

#check Submonoid.comap
example : Submonoid.comap f H₂ = { Subsemigroup.comap f.toMulHom H₂.toSubsemigroup with
  one_mem' := by simp
} := by rfl

/- Range is also specially handled as `MulHom.range`. -/
#check MonoidHom.mrange
example (x : G₂) : x ∈ MonoidHom.mrange f ↔ x ∈ Set.range f := by rfl
#check MonoidHom.mem_mrange -- corresponding Mathlib theorem

/-
With the presence of identity element, we can define the kernel of a `MonoidHom`.
-/
#check MonoidHom.mker
example : MonoidHom.mker f = (⊥ : Submonoid G₂).comap f := by rfl

/- [EXR] manual definition of `mker` -/
example : MonoidHom.mker f = {
  carrier := {x | f x = 1}
  one_mem' := by rw [Set.mem_setOf, map_one]
  mul_mem' := by
    rintro x y hx hy
    simp only [Set.mem_setOf] at hx hy ⊢
    rw [map_mul, hx, hy, one_mul]
} := by rfl

example (x : G₁) : x ∈ MonoidHom.mker f ↔ f x = 1 := by rfl
#check MonoidHom.mem_mker -- corresponding Mathlib theorem

end

/-
### Submonoid as a type, and `MonoidHom` restriction

Tedious upgrade again. Note that `MonoidHom.mker` and `MonoidHom.mrange` steps in.
-/
section

#check MonoidHom.restrict
#check MonoidHom.restrict_apply -- universal property of restriction

#check MonoidHom.codRestrict
#check MonoidHom.injective_codRestrict -- restriction on codomain preserves injectivity

#check MonoidHom.mrangeRestrict
#check MonoidHom.coe_mrangeRestrict -- universal property of range restriction
#check MonoidHom.mrangeRestrict_mker -- restriction on range preserves the kernel
end

/-
### Exercise

As an exercise,
let's define addition on `AddSubmonoid A` with the intrinsic definition,
and show that it coincides with the supremum.
-/
section

variable {A : Type*} [AddCommMonoid A]

instance : Add (AddSubmonoid A) := ⟨fun B₁ B₂ ↦ {
  carrier := {x | ∃ b₁ ∈ B₁, ∃ b₂ ∈ B₂, x = b₁ + b₂}
  zero_mem' := ⟨0, B₁.zero_mem, 0, B₂.zero_mem, by rw [add_zero]⟩
  add_mem' := by
    rintro x y ⟨b₁, hb₁, b₂, hb₂, rfl⟩ ⟨c₁, hc₁, c₂, hc₂, rfl⟩
    use b₁ + c₁, B₁.add_mem hb₁ hc₁
    use b₂ + c₂, B₂.add_mem hb₂ hc₂
    abel
}⟩

example (B₁ B₂ : AddSubmonoid A) : B₁ ⊔ B₂ = B₁ + B₂ := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      use x, hx, 0, B₂.zero_mem
      rw [add_zero]
    · intro x hx
      use 0, B₁.zero_mem, x, hx
      rw [zero_add]
  · intro x hx
    rcases hx with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    haveI : B₁ ≤ B₁ ⊔ B₂ := le_sup_left
    replace hb₁ : b₁ ∈ B₁ ⊔ B₂ := this hb₁
    haveI : B₂ ≤ B₁ ⊔ B₂ := le_sup_right
    replace hb₂ : b₂ ∈ B₁ ⊔ B₂ := this hb₂
    exact add_mem hb₁ hb₂

end

/-
## Subgroups

### Objects

There's nothing new about `Subgroup G` of a `Group G` compared to `Subsemigroup` and `Submonoid`.
It just adds the closure under taking inverses.
-/
section

variable (G : Type*) [Group G]
variable (H₁ H₂ : Subgroup G) (a b : G)
example : a ∈ H₁ → b ∈ H₁ → a * b ∈ H₁ := by apply mul_mem
example : (1 : G) ∈ H₁ := by apply one_mem
example : a ∈ H₁ → a⁻¹ ∈ H₁ := by apply inv_mem

/-
We skip the lattice structure again.
-/
end

/-
### Morphisms

`MonoidHom` works for `Subgroup` as well.
-/
section

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]
         (f : G₁ →* G₂) (H₁ : Subgroup G₁) (H₂ : Subgroup G₂)

/-
Image and preimage of subgroups, upgraded to show closure under inverses.
-/
#check Subgroup.map
#check Subgroup.comap

/-
For groups, `mker` and `mrange` has been upgraded to `ker` and `range` respectively.
-/
#check MonoidHom.ker
#check MonoidHom.range

example : MonoidHom.ker f = (⊥ : Subgroup G₂).comap f := by rfl
example : MonoidHom.ker f = {MonoidHom.mker f with
  inv_mem' := by simp
} := by rfl

/- [EXR] injectivity characterization via kernel -/
example : MonoidHom.ker f = ⊥ ↔ Function.Injective f := by
  constructor
  · intro h
    intro x y hxy
    apply_fun (· * (f y)⁻¹) at hxy
    simp only [mul_inv_cancel] at hxy
    rw [← map_inv, ← map_mul, ← MonoidHom.mem_ker, h, Subgroup.mem_bot] at hxy
    apply_fun (· * y) at hxy
    simp at hxy; exact hxy
  · intro h
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      rw [← map_one f] at hx
      exact h hx
    · intro hx
      rw [hx]
      exact map_one f
#check MonoidHom.ker_eq_bot_iff -- corresponding Mathlib theorem

end

/-
### Subgroup as a type, and `MonoidHom` restriction

Similar to those for `Submonoid`.
-/
section

#check MonoidHom.restrict
#check MonoidHom.restrict_apply -- universal property of restriction

#check MonoidHom.codRestrict
#check MonoidHom.ker_codRestrict -- restriction on codomain preserves the kernel
#check MonoidHom.injective_codRestrict -- restriction on codomain preserves injectivity

#check MonoidHom.rangeRestrict
#check MonoidHom.coe_rangeRestrict -- universal property of range restriction
#check MonoidHom.ker_rangeRestrict -- restriction on range preserves the kernel
#check MonoidHom.rangeRestrict_injective_iff -- restriction on range preserves injectivity

end

/-
### Normal Subgroups

For later discussions on quotient groups, we introduce normal subgroups here.
-/
section

#check Subgroup.Normal

/- `Subgroup.Normal` is a bundled structure consisting of a proof of normality. -/
example {G : Type*} [Group G] (H : Subgroup G) :
    H.Normal ↔ ∀ h ∈ H, ∀ g : G, g * h * g⁻¹ ∈ H := by
  constructor
  · intro ⟨h⟩
    exact h
  · intro h
    exact ⟨h⟩

/- The kernel of a group homomorphism is a normal subgroup. -/
example {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (f : G₁ →* G₂) : (f.ker).Normal := by
  constructor
  intro x hx y
  rw [MonoidHom.mem_ker]
  rw [map_mul, map_mul, hx, map_inv, mul_one, mul_inv_cancel]

/-
Actually, Mathlib contains an instance for kernels, so that Lean
automatically recognizes the normality of kernels.
-/
#check MonoidHom.normal_ker
example {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (f : G₁ →* G₂) : (f.ker).Normal := inferInstance

end

/-
[TODO]

- Indexed infimum and supremum of substructures
- `xxxClass` for substructures as canonical maps
-/
