/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Zassenhaus recognition of `PSL(2, q)`: the Borel / unipotent chapter

This file sets up the vocabulary for `zassenhaus_psl`.

Let `G` be a group acting 2-transitively on a type `X` with `Nat.card X = p ^ k + 1`,
every nonidentity element fixing at most two points, and the stabilizer of any two
distinct points of order `(p ^ k - 1) / 2` (with `p` an odd prime and `1 ≤ k`).

Write `q = p ^ k` and `h = (q - 1) / 2`.  For chosen points `inf` (the point `∞`) and
`zero` (the point `0`) we write

* `borel G inf = G_∞`, the *Borel subgroup* `B`;
* `pairStab G inf x = G_{x∞}`, the pointwise stabilizer of `{x, ∞}`;
* `fixesOnly G inf` for the elements of `B` whose only fixed point is `∞`;
* `fixesSome G inf` for the elements of `B` fixing some further point.

Following Mathlib's `MulAction.stabilizer`, the group `G` is an *explicit* argument of
`borel`, `pairStab`, `fixesOnly` and `fixesSome`: with an implicit `G` the typeclass
problem `MulAction ?G X` is stuck, which makes the type of e.g. `↑(pairStab inf x)`
undetermined.

The main results of the chapter are `zass_borel_unipotent` (Z1–Z4), `zass_field` (Z5) and
`zass_finish` (Z7 plumbing).
-/

import Mathlib

namespace Work.Zassenhaus

open scoped MatrixGroups

/-- The standing hypotheses of Zassenhaus' recognition theorem.

`G` acts on `X` with `Nat.card X = p ^ k + 1`; the action is 2-pretransitive; every
nonidentity element fixes at most two points; and the pointwise stabilizer of any two
distinct points has order `(p ^ k - 1) / 2`.  (`p` is an odd prime and `1 ≤ k`.) -/
structure ZassHyp (p k : ℕ) (G : Type) [Group G] [Finite G] (X : Type)
    [MulAction G X] [Finite X] : Prop where
  prime : Nat.Prime p
  odd : Odd p
  kpos : 1 ≤ k
  card : Nat.card X = p ^ k + 1
  pretrans : MulAction.IsMultiplyPretransitive G X 2
  fix_le_two : ∀ g : G, g ≠ 1 → {x : X | g • x = x}.ncard ≤ 2
  stab_pair : ∀ x y : X, x ≠ y →
    Nat.card ↥(MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) = (p ^ k - 1) / 2

section Defs

variable {G : Type} [Group G] {X : Type} [MulAction G X]

/-- The Borel subgroup `B = G_∞`, the stabilizer of the point `inf`. -/
def borel (G : Type) {X : Type} [Group G] [MulAction G X] (inf : X) : Subgroup G :=
  MulAction.stabilizer G inf

/-- The pointwise stabilizer `G_{x∞}` of the two points `x` and `inf`. -/
def pairStab (G : Type) {X : Type} [Group G] [MulAction G X] (inf x : X) : Subgroup G :=
  MulAction.stabilizer G x ⊓ MulAction.stabilizer G inf

/-- The elements of `B = G_∞` whose only fixed point is `inf`. -/
def fixesOnly (G : Type) {X : Type} [Group G] [MulAction G X] (inf : X) : Set G :=
  {g | g ∈ MulAction.stabilizer G inf ∧ ∀ x : X, x ≠ inf → g • x ≠ x}

/-- The elements of `B = G_∞` fixing some point other than `inf`. -/
def fixesSome (G : Type) {X : Type} [Group G] [MulAction G X] (inf : X) : Set G :=
  {g | g ∈ MulAction.stabilizer G inf ∧ ∃ x : X, x ≠ inf ∧ g • x = x}

end Defs

section Basic

variable {G : Type} [Group G] {X : Type} [MulAction G X]

@[simp] theorem mem_borel_iff {inf : X} {g : G} : g ∈ borel G inf ↔ g • inf = inf :=
  MulAction.mem_stabilizer_iff

theorem mem_pairStab_iff {inf x : X} {g : G} :
    g ∈ pairStab G inf x ↔ g • x = x ∧ g • inf = inf := by
  simp [pairStab, MulAction.mem_stabilizer_iff]

theorem pairStab_le_borel (inf x : X) : pairStab G inf x ≤ borel G inf := inf_le_right

@[simp] theorem mem_fixesOnly_iff {inf : X} {g : G} :
    g ∈ fixesOnly G inf ↔ g ∈ borel G inf ∧ ∀ x : X, x ≠ inf → g • x ≠ x :=
  Iff.rfl

@[simp] theorem mem_fixesSome_iff {inf : X} {g : G} :
    g ∈ fixesSome G inf ↔ g ∈ borel G inf ∧ ∃ x : X, x ≠ inf ∧ g • x = x :=
  Iff.rfl

theorem fixesOnly_disjoint_fixesSome (inf : X) :
    Disjoint (fixesOnly G inf) (fixesSome G inf) := by
  rw [Set.disjoint_left]
  intro g hg hg'
  obtain ⟨-, h2⟩ := mem_fixesOnly_iff.1 hg
  obtain ⟨-, x, hx, hgx⟩ := mem_fixesSome_iff.1 hg'
  exact h2 x hx hgx

theorem fixesOnly_union_fixesSome (inf : X) :
    fixesOnly G inf ∪ fixesSome G inf = (borel G inf : Set G) := by
  ext g
  simp only [Set.mem_union, mem_fixesOnly_iff, mem_fixesSome_iff, SetLike.mem_coe]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hg
    by_cases h : ∃ x : X, x ≠ inf ∧ g • x = x
    · exact Or.inr ⟨hg, h⟩
    · exact Or.inl ⟨hg, fun x hx hgx => h ⟨x, hx, hgx⟩⟩

theorem mem_fixesOnly_self (inf : X) {g : G} (hg : g ∈ fixesOnly G inf) (x : X) (hx : x ≠ inf) :
    g • x ≠ x := hg.2 x hx

theorem fixesOnly_iff_forall_fixed_eq (inf : X) {g : G} (hg : g ∈ borel G inf) :
    g ∈ fixesOnly G inf ↔ ∀ x : X, g • x = x → x = inf := by
  refine ⟨fun h x hx => ?_, fun h => ⟨hg, fun x hx hgx => hx (h x hgx)⟩⟩
  by_contra hne
  exact (mem_fixesOnly_iff.1 h).2 x hne hx

theorem pairStab_self (inf : X) : pairStab G inf inf = borel G inf := by
  simp [pairStab, borel]

theorem pairStab_comm (inf x : X) : pairStab G inf x = pairStab G x inf := by
  simp [pairStab, inf_comm]

end Basic

end Work.Zassenhaus
