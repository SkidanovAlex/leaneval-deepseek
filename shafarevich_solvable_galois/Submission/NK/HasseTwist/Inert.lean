/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inert places, and the first *unconditional* instances of the input catalogue

This module records what the twisted localisation does at a place whose decomposition group contains
the subgroup under consideration, and draws the two consequences that make the input catalogue of
`Submission/Work/HasseTwist/Inputs.lean` demonstrably non-vacuous:

* `NK.HasseTwist.loc_ne_zero_of_le_stabSubgroup` — **every non-zero class of `H²(U, μ_p)` has a
  non-zero local component at every place whose decomposition group contains `U`** (unconditional:
  the localisation at such an *inert* place is injective, `NK.HasseTwist.loc_injective_of_le_stabSubgroup`);
* `NK.HasseTwist.obstruction_trivial_of_le_stabSubgroup` — **the labelled level-wise strong form —
  i.e. the input field `Sha2Input.level_obstruction` — holds unconditionally at every level at which
  the subgroup lies in a decomposition group.**  This is a *proof*, not an assumption, of instances
  of the main input;
* `NK.HasseTwist.sha2Vanishing_of_inert` — **the Hasse principle `Sha2Vanishing` holds as soon as
  every labelled closed subgroup lies in the decomposition group of some place**;
* `NK.HasseTwist.sha2Input_of_inert` — consequently the full input catalogue `Sha2Input` is
  *satisfiable*: it is met (with the Hasse norm theorem supplied) whenever the group-theoretic
  hypothesis holds, which is exactly Neukirch's criterion conclusion.

The mathematical content of the remaining hypothesis of `sha2Vanishing_of_inert` is therefore
*whether* a labelled subgroup lies in a decomposition group — Neukirch's "the prime is indecomposed"
step, `NK.LocalDecomposition.IndecomposedPrime` — and not the Hasse principle itself.  See
`Submission/Work/HasseTwist/README.md` §6.
-/

import Submission.NK.HasseTwist.Localisation
import Submission.NK.HasseTwist.loc_injective_of_le_stabSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The level-wise input at an inert level -/

/-- **The level-wise localisation is injective whenever the level group of the decomposition group
is the whole level group.**  This is `NK.HasseTwist.map_injective_of_bijective_of_isIso` applied to
the level-wise localisation, whose coefficient morphism `locCoeff` is an isomorphism
(`NK.HasseTwist.locCoeff_isIso`). -/
lemma locLevel_injective_of_bijective_localInclHom (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (h : Function.Bijective (NK.BrauerHasse.localInclHom U A L)) :
    Function.Injective (locLevel p U A L) :=
  map_injective_of_bijective_of_isIso (NK.BrauerHasse.localInclHom U A L) h
    (locCoeff p U A L) (locCoeff_isIso p U A L) 2

/-- **The labelled level-wise Hasse principle holds at a level with a full local level group.** -/
theorem obstruction_trivial_of_bijective_localInclHom (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (L : FiniteGaloisIntermediateField K K')
    (h : Function.Bijective (NK.BrauerHasse.localInclHom U A.1 L)) {a : LevelH2 p U L}
    (ha : a ∈ levelObstruction p U L) : a = 0 := by
  have hA : (locLevel p U A.1 L) a = 0 := by
    have hmem : a ∈ (⨅ A' : OverFinitePrime K K', (locLevel p U A'.1 L).hom.ker) := ha
    rw [Submodule.mem_iInf] at hmem
    exact hmem A
  exact locLevel_injective_of_bijective_localInclHom p A.1 L h (hA.trans (map_zero _).symm)

/-- **The labelled level-wise Hasse principle holds at every level of a subgroup contained in a
decomposition group.**  This is an *unconditional instance* of the input field
`NK.HasseTwist.Sha2Input.level_obstruction`. -/
theorem obstruction_trivial_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (h : U ≤ stabSubgroup A.1)
    (L : FiniteGaloisIntermediateField K K') {a : LevelH2 p U L}
    (ha : a ∈ levelObstruction p U L) : a = 0 :=
  obstruction_trivial_of_bijective_localInclHom p A L
    (NK.HassePrinciple.localInclHom_bijective_of_le_stabSubgroup (K := K) (K' := K') A.1 h L) ha

/-- The same, in the form of local triviality at the level. -/
theorem levelLocTrivial_eq_zero_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (h : U ≤ stabSubgroup A.1)
    (L : FiniteGaloisIntermediateField K K') {a : LevelH2 p U L}
    (ha : levelLocTrivial p U L a) : a = 0 :=
  obstruction_trivial_of_le_stabSubgroup p A h L ((mem_levelObstruction_iff p U L a).mpr ha)

/-- The level class dies after inflation, at every level of an inert subgroup. -/
theorem level_kernel_dies_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (h : U ≤ stabSubgroup A.1)
    (L : FiniteGaloisIntermediateField K K') {a : LevelH2 p U L}
    (ha : levelLocTrivial p U L a) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      (levelMap p U hLM) a = 0 :=
  ⟨L, le_rfl, by rw [levelLocTrivial_eq_zero_of_le_stabSubgroup p A h L ha, map_zero]⟩

/-! ## The consequences on the colimit -/

/-- **A non-zero class has a non-zero local component at an inert place** (unconditional). -/
theorem loc_ne_zero_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (h : U ≤ stabSubgroup A.1) {x : H2Twist p U} (hx : x ≠ 0) :
    H2Twist.loc p U x A ≠ 0 :=
  fun h0 => hx (loc_injective_of_le_stabSubgroup p A h (h0.trans (H2Twist.loc_zero p U A).symm))

variable {κ κ' : Type u} [NumberField K] [Field κ] [Field κ'] [Algebra κ κ']
  [IsSepClosure κ κ']

/-- **The Hasse principle holds as soon as every labelled closed subgroup lies in the decomposition
group of some place.**  The remaining hypothesis is the group-theoretic shadow of Neukirch's "the
prime is indecomposed" step; the proof is immediate from the injectivity of the localisation at an
inert place, which is proved unconditionally. -/
theorem sha2Vanishing_of_inert (p : ℕ)
    (h : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' := by
  intro U hU hκ x hx
  obtain ⟨A, hA⟩ := h U hU hκ
  by_contra hne
  exact hne (loc_injective_of_le_stabSubgroup p A hA ((hx A).trans (H2Twist.loc_zero p U A).symm))

/-- **A non-vacuity witness for the input catalogue.**  Whenever every labelled closed subgroup lies
in the decomposition group of some place, the input structure `NK.HasseTwist.Sha2Input` is
*inhabited* (with the Hasse norm theorem supplied): all three of its mathematical fields are then
theorems.  In particular `NK.HasseTwist.Sha2Input` is not an empty hypothesis. -/
theorem sha2Input_of_inert (p : ℕ) (hp : p.Prime)
    (hnorm : NK.HassePrinciple.HasseNormTheorem.{u})
    (h : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1) :
    Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p where
  hp := hp
  hasse_norm := hnorm
  level_obstruction := fun U hU hκ L a ha =>
    obstruction_trivial_of_le_stabSubgroup p (Classical.choose (h U hU hκ))
      (Classical.choose_spec (h U hU hκ)) L ha
  kernel_exhausted := fun U hU hκ x hx => by
    have hx0 : x = 0 := sha2Vanishing_of_inert (K := K) (K' := K') (κ := κ) (κ' := κ') p h
      U hU hκ x hx
    exact ⟨⊥, 0, by rw [hx0]; exact (H2Twist.ofLevel_zero (p := p) (U := U) ⊥).symm,
      zero_mem_levelObstruction p U ⊥⟩

end NK.HasseTwist
