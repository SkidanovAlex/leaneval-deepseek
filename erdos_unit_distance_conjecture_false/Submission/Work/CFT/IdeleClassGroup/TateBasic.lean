/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CFT.IdeleClassGroup
-/
import Mathlib

/-!
# Invariants, norms and the zeroth Tate cohomology

For a finite group `G` and a `ℤ`-representation `A` (a term of `Rep ℤ G`), this file names the
`G`-invariants `A^G ⊆ A`, the norm endomorphism `N = ∑_{g : G} g`, and the subgroup
`N A ⊆ A^G` of norms.  The zeroth Tate cohomology `Ĥ⁰(G, A) = A^G / N A` is the quotient
`invariants A ⧸ norms A`.

## Main definitions

* `Work.CFT.IdeleClassGroup.invariants A` : the `G`-invariants of `A`, as an `AddSubgroup`.
* `Work.CFT.IdeleClassGroup.normMap A` : the norm endomorphism `∑_{g : G} g` of `A`, as an
  additive homomorphism.
* `Work.CFT.IdeleClassGroup.norms A` : the norms `N A`, as an `AddSubgroup` of `invariants A`.
-/

namespace Work.CFT.IdeleClassGroup

open CategoryTheory

/-- The `G`-invariants of a `ℤ`-representation `A` of `G`, as an additive subgroup. -/
def invariants {G : Type} [Group G] (A : Rep ℤ G) : AddSubgroup A.V where
  carrier := {x | ∀ g : G, (A.ρ g) x = x}
  zero_mem' := by intro g; simp
  add_mem' := by intro x y hx hy g; rw [map_add, hx g, hy g]
  neg_mem' := by intro x hx g; rw [map_neg, hx g]

@[simp]
lemma mem_invariants {G : Type} [Group G] (A : Rep ℤ G) (x : A.V) :
    x ∈ invariants A ↔ ∀ g : G, (A.ρ g) x = x := Iff.rfl

/-- The norm endomorphism `N = ∑_{g : G} g` of a `ℤ`-representation `A` of a finite group `G`. -/
def normMap {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) : A.V →+ A.V where
  toFun x := ∑ g : G, (A.ρ g) x
  map_zero' := by simp
  map_add' x y := by simp [map_add, Finset.sum_add_distrib]

@[simp]
lemma normMap_apply {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) (x : A.V) :
    normMap A x = ∑ g : G, (A.ρ g) x := rfl

/-- The subgroup `N A` of norms, viewed as a subgroup of the invariants `A^G`. -/
def norms {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) : AddSubgroup (invariants A) :=
  (normMap A).range.comap (invariants A).subtype

/-- The zeroth Tate cohomology group, presented as the invariants modulo the norms. -/
abbrev H0Quotient {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) : Type :=
  (invariants A) ⧸ (norms A)

end Work.CFT.IdeleClassGroup
