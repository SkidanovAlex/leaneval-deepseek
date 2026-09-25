/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse principle at the finite levels

This module records the *level-wise* form of the Hasse principle — the form in which the classical
Hasse–Brauer–Noether theorem is consumed by the Neukirch–Uchida development — and derives the
consequences of it that the reduction needs.

## The mathematical content

Let `L/K` be a finite Galois level inside the fixed separable closure, `U ≤ Gal(K'/K)` a subgroup and
`Γ = U/(U ⊓ Gal(K'/L))` the level group.  The **level obstruction**

`NK.HassePrinciple.levelObstruction p U L ⊆ H²(Γ, Z/p)`

is the group of level classes that are locally trivial at *every* place of `K'` over a finite prime
of `K`.  The level-wise Hasse principle is the statement

  `∀ U L a, a ∈ levelObstruction p U L → a = 0`

("no non-zero finite-level class is locally trivial at its own level").  Classically this is the
Hasse–Brauer–Noether theorem for the level extensions `L/(L ∩ K'^U)`, in the `Z/p`-coefficient form;
it is *equivalent*, via Kummer theory and the reciprocity isomorphism for cyclic extensions, to the
Hasse norm theorem — see `Submission/Work/HassePrinciple/README.md`, §4.

## Main results

* `NK.HassePrinciple.level_kernel_dies_of_obstructionTrivial` — the level-wise Sha² computation
  ("a locally trivial level class dies after inflation"), **derived** from the level-wise Hasse
  principle;
* `NK.HassePrinciple.levelForm_of_obstructionTrivial` — the Hasse principle in the level-wise
  form `NK.HassePrinciple.LevelForm` of `Defs.lean`, from the level-wise Hasse principle and the
  exhaustion of the kernel of the localisation by the level obstructions;
* `NK.HassePrinciple.obstruction_trivial_of_coprime_index`,
  `..._of_bijective_localInclHom`, `..._of_le_stabSubgroup` — the level-wise Hasse principle, proved
  **unconditionally**, at every level at which some place has local level group of index prime to
  `p`; in particular at every level at which some place has a full local group, and at every level
  when the subgroup under consideration lies in a decomposition group.
-/

import Submission.NK.HassePrinciple.Obstruction
import Submission.NK.HassePrinciple.Inert
import Submission.NK.HassePrinciple.Norm

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## Consequences of the level-wise Hasse principle -/

/-- **The level-wise Sha² computation, derived from the level-wise Hasse principle.**  A finite-level
class that is locally trivial at its own level dies after inflation to a larger level: indeed it is
zero, so it dies at its own level. -/
theorem level_kernel_dies_of_obstructionTrivial (p : ℕ)
    (h : ∀ (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
      (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0) :
    ∀ (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
      levelLocTrivial p U L a →
        ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
          (levelMap p (U := U) hLM) a = 0 := by
  intro U L a ha
  have hzero : a = 0 := h U L a ((mem_levelObstruction_iff p U L a).mpr ha)
  exact ⟨L, le_rfl, by rw [hzero, map_zero]⟩

/-- **The labelled level-wise Hasse principle plus the exhaustion of the kernel gives
`LevelForm`.**  This is `levelForm_of_obstructionTrivial` for the labelled levels only, i.e. with the
level-wise Hasse principle assumed for the closed subgroups `U ≤ Gal(K'/K)` isomorphic to
`Gal(κ'/κ)` (the hypothesis of `NK.HassePrinciple.sha2Vanishing`). -/
theorem levelForm_of_labelledObstruction (p : ℕ)
    (h : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ (L : FiniteGaloisIntermediateField K K')
        (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0)
    (hC : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Profinite p U,
        (∀ A : OverFinitePrime K K', H2Profinite.loc p U x A = 0) →
          ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
            x = H2Profinite.ofLevel L a ∧ a ∈ levelObstruction p U L) :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  intro U hU hκ L a ha
  have hx : ∀ A : OverFinitePrime K K', H2Profinite.loc p U (H2Profinite.ofLevel L a) A = 0 :=
    (levelLocVanishing_iff (K := K) (K' := K') p (U := U) L a).mp ha
  obtain ⟨L', a', hxa', ha'⟩ := hC U hU hκ _ hx
  rw [hxa']
  calc H2Profinite.ofLevel L' a'
      = H2Profinite.ofLevel L' (0 : LevelH2 p U L') := by rw [h U hU hκ L' a' ha']
    _ = 0 := ofLevel_zero _

/-- **The level-wise Hasse principle plus the exhaustion of the kernel gives `LevelForm`.**

`hC` says that a class whose localisations all vanish is represented at some finite level by a class
of the level obstruction (the exhaustion of the kernel of the localisation by the finite levels);
the level-wise Hasse principle then makes that representative zero.  This is the *alternative*, and
strictly stronger, input route; the chain used by `NK.HassePrinciple.sha2Vanishing` goes through
the colimit form `NK.HassePrinciple.levelForm_of_pgroupLevel` and does not need `hC`. -/
theorem levelForm_of_obstructionTrivial (p : ℕ)
    (h : ∀ (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
      (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0)
    (hC : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Profinite p U,
        (∀ A : OverFinitePrime K K', H2Profinite.loc p U x A = 0) →
          ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
            x = H2Profinite.ofLevel L a ∧ a ∈ levelObstruction p U L) :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  intro U hU hκ L a ha
  have hx : ∀ A : OverFinitePrime K K', H2Profinite.loc p U (H2Profinite.ofLevel L a) A = 0 :=
    (levelLocVanishing_iff (K := K) (K' := K') p (U := U) L a).mp ha
  obtain ⟨L', a', hxa', ha'⟩ := hC U hU hκ _ hx
  rw [hxa']
  calc H2Profinite.ofLevel L' a'
      = H2Profinite.ofLevel L' (0 : LevelH2 p U L') := by rw [h U L' a' ha']
    _ = 0 := ofLevel_zero _

/-! ## Partial discharges of the level-wise Hasse principle -/

section Partial

variable (p : ℕ) {U : Subgroup Gal(K'/K)} (A : OverFinitePrime K K')
  (L : FiniteGaloisIntermediateField K K')

/-- **The level-wise Hasse principle holds at a level with a place of prime-to-`p` local index.**
If the local level group at some place has index prime to `p` in the level group, then the
level-wise localisation at that place is injective
(`NK.HassePrinciple.levelLocTrivial_eq_zero_of_coprime_index`), so every class of the level
obstruction is zero.  This discharges the level-wise Hasse principle at such levels, and in
particular at every level at which some place has a *full* local level group. -/
theorem obstruction_trivial_of_coprime_index
    (hf : Function.Injective (localInclHom U A.1 L))
    (h : Nat.Coprime (Subgroup.index (MonoidHom.range (localInclHom U A.1 L))) p)
    {a : LevelH2 p U L} (ha : a ∈ levelObstruction p U L) : a = 0 :=
  levelLocTrivial_eq_zero_of_coprime_index (K := K) (K' := K') p A L hf h
    ((mem_levelObstruction_iff p U L a).mp ha)

/-- The same, at a level at which some place has a *full* local level group. -/
theorem obstruction_trivial_of_bijective_localInclHom
    (h : Function.Bijective (localInclHom U A.1 L))
    {a : LevelH2 p U L} (ha : a ∈ levelObstruction p U L) : a = 0 :=
  levelLocTrivial_eq_zero_of_bijective_localInclHom (K := K) (K' := K') p A L h
    ((mem_levelObstruction_iff p U L a).mp ha)

/-- The same, at every level, when `U` is contained in a decomposition group. -/
theorem obstruction_trivial_of_le_stabSubgroup (h : U ≤ stabSubgroup A.1)
    {a : LevelH2 p U L} (ha : a ∈ levelObstruction p U L) : a = 0 :=
  obstruction_trivial_of_bijective_localInclHom (K := K) (K' := K') p A L
    (localInclHom_bijective_of_le_stabSubgroup A.1 h L) ha

end Partial

end NK.HassePrinciple
