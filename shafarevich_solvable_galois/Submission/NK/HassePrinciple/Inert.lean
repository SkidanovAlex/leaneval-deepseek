/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inert places: the unconditionally proved part of the Hasse principle

This module records what the localisation map does at a place whose decomposition group contains
the subgroup under consideration.  By
`NK.HassePrinciple.loc_injective_of_le_stabSubgroup`, the localisation at such an *inert* place is
injective, and therefore:

* `NK.HassePrinciple.loc_ne_zero_of_le_stabSubgroup` — **every non-zero class of `H²(U, Z/p)`
  has a non-zero local component at every place whose decomposition group contains `U`.**  This is
  an unconditional instance of the conclusion of the Hasse principle (the input structure
  `NK.HassePrinciple.Sha2Input` is not needed);
* `NK.HassePrinciple.sha2Vanishing_of_inert` — **the Hasse principle holds as soon as every
  closed subgroup `U ≅ Gal(κ'/κ)` is contained in the decomposition group of some place.**  The
  mathematical content of the remaining hypothesis is exactly Neukirch's "the prime is
  indecomposed" step, i.e. the statement that `H` lies in a decomposition group; the statement of
  the Hasse principle itself is then immediate.

The interest of the lemma is that it isolates the two halves of the Hasse principle: the
*local* half (a class detected at a place whose decomposition group contains `U` is non-zero) is
proved here unconditionally, while the *arithmetic* half (the existence of such a place, or, more
generally, of enough local information when there is none) is the content of the input field
`the `p`-primary level-wise Hasse principle (now `Sha2Input.level`)`; see `Submission/Work/HassePrinciple/README.md`.
-/

import Submission.NK.HassePrinciple.Defs
import Submission.NK.HassePrinciple.loc_injective_of_le_stabSubgroup
import Submission.NK.HassePrinciple.H2_map_injective_of_coprime_index
import Submission.NK.HassePrinciple.finite_levelGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **A non-zero class has a non-zero local component at an inert place** (unconditional).  If the
decomposition group of the place `A` contains `U`, then a non-zero class of `H²(U, Z/p)` is not
killed by the localisation at `A`. -/
theorem loc_ne_zero_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (h : U ≤ stabSubgroup A.1) {x : H2Profinite p U} (hx : x ≠ 0) :
    H2Profinite.loc p U x A ≠ 0 :=
  fun h0 => hx (loc_injective_of_le_stabSubgroup p A h
    (h0.trans (H2Profinite.loc_zero p U A).symm))

variable {κ κ' : Type u} [NumberField K] [Field κ] [Field κ'] [Algebra κ κ']
  [IsSepClosure κ κ']

/-- **The Hasse principle from the existence of inert places.**  If every closed subgroup
`U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` is contained in the decomposition group of some place of
`K'` over a finite prime of `K`, then the Hasse principle `Sha2Vanishing p K K' κ κ'` holds.

The hypothesis is the group-theoretic shadow of Neukirch's "the prime is indecomposed" step; the
proof is immediate from the injectivity of the localisation at an inert place (the *local* half of
the Hasse principle), which is proved unconditionally. -/
theorem sha2Vanishing_of_inert (p : ℕ)
    (h : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' := by
  intro U hU hκ x hx
  obtain ⟨A, hA⟩ := h U hU hκ
  by_contra hne
  exact hne (loc_injective_of_le_stabSubgroup p A hA ((hx A).trans (H2Profinite.loc_zero p U A).symm))


/-- **(K) at a level with a full local group.**  If the local level group at a place `A` is the
whole level group — i.e. `localInclHom U A L` is bijective, equivalently the decomposition subgroup
of `A` has full image in the level group `U/(U ⊓ Gal(K'/L))` — then the level-wise localisation at
`A` is injective, so a locally trivial class of the level `L` is already zero, and in particular
dies after inflation.  This proves the level-wise Hasse principle — and hence the `p`-primary input
`the `p`-primary level-wise Hasse principle (now `Sha2Input.level`)` — *at such levels* unconditionally.  By Čebotarev's density theorem such a place exists whenever the level group is
abelian (take a prime whose Frobenius class is a generator; see §5.3 of the README), so the
arithmetically hard case of `level_kernel_dies` is the one of *non-abelian* level groups. -/
theorem levelLocTrivial_eq_zero_of_bijective_localInclHom (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (L : FiniteGaloisIntermediateField K K')
    (h : Function.Bijective (localInclHom U A.1 L)) {a : LevelH2 p U L}
    (ha : levelLocTrivial p U L a) : a = 0 :=
  h2Map_injective_of_bijective (p := p) (localInclHom U A.1 L) h
    ((ha A).trans (map_zero _).symm)

/-- The form of the above recording that the level class dies after inflation. -/
theorem level_kernel_dies_of_bijective_localInclHom (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (L : FiniteGaloisIntermediateField K K')
    (h : Function.Bijective (localInclHom U A.1 L)) {a : LevelH2 p U L}
    (ha : levelLocTrivial p U L a) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      (levelMap p (U := U) hLM) a = 0 :=
  ⟨L, le_rfl, by rw [levelLocTrivial_eq_zero_of_bijective_localInclHom p A L h ha, map_zero]⟩


/-- **(K) at a level where the local group has prime-to-`p` index.**

If the local level group at a place `A` is a subgroup of the level group of index prime to `p`
(and `localInclHom` is injective, which always holds), then the level-wise localisation at `A` is
injective by `NK.HassePrinciple.H2_map_injective_of_coprime_index`, so a locally trivial class of
the level `L` is already zero and hence dies after inflation.  This is the generalisation of
`levelLocTrivial_eq_zero_of_bijective_localInclHom` (the case of index `1`) and it proves the input
the `p`-primary input `the `p`-primary level-wise Hasse principle (now `Sha2Input.level`)` at such levels unconditionally:
the arithmetic content of that input is concentrated in the levels where *every* place has local
index divisible by `p`.

(The finiteness of the level group — it embeds into the finite Galois group `Gal(L/K)` by
restriction — is the instance `NK.HassePrinciple.finite_levelGroup'` of
`Submission/Work/HassePrinciple/finite_levelGroup.lean`, imported here so that the prime-to-`p`
index lemma applies.) -/
theorem levelLocTrivial_eq_zero_of_coprime_index (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (L : FiniteGaloisIntermediateField K K')
    (hf : Function.Injective (localInclHom U A.1 L))
    (h : Nat.Coprime (Subgroup.index (MonoidHom.range (localInclHom U A.1 L))) p)
    {a : LevelH2 p U L} (ha : levelLocTrivial p U L a) : a = 0 :=
  H2_map_injective_of_coprime_index (p := p) (localInclHom U A.1 L) hf h
    ((ha A).trans (map_zero _).symm)

/-- The form of the above recording that the level class dies after inflation. -/
theorem level_kernel_dies_of_coprime_index (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (L : FiniteGaloisIntermediateField K K')
    (hf : Function.Injective (localInclHom U A.1 L))
    (h : Nat.Coprime (Subgroup.index (MonoidHom.range (localInclHom U A.1 L))) p)
    {a : LevelH2 p U L} (ha : levelLocTrivial p U L a) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      (levelMap p (U := U) hLM) a = 0 :=
  ⟨L, le_rfl,
    by rw [levelLocTrivial_eq_zero_of_coprime_index p A L hf h ha, map_zero]⟩


/-- **The input (K) holds at every level when `U` is contained in a decomposition group.**  If
`U ≤ stabSubgroup A.1` then `localInclHom U A.1 L` is bijective at every level `L`
(`NK.HassePrinciple.localInclHom_bijective_of_le_stabSubgroup`), so
`NK.HassePrinciple.level_kernel_dies_of_bijective_localInclHom` applies.  This shows that the
first cohomological input of `NK.HassePrinciple.Sha2Input` is not merely an assumption that could
never be verified. -/
theorem level_kernel_dies_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (h : U ≤ stabSubgroup A.1)
    (L : FiniteGaloisIntermediateField K K') {a : LevelH2 p U L}
    (ha : levelLocTrivial p U L a) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      (levelMap p (U := U) hLM) a = 0 :=
  level_kernel_dies_of_bijective_localInclHom p A L
    (localInclHom_bijective_of_le_stabSubgroup A.1 h L) ha

end NK.HassePrinciple
