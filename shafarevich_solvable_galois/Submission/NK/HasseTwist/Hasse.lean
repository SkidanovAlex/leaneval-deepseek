/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse principle at the finite levels, with `μ_p`-coefficients

This module records the *level-wise* form of the Hasse principle for the cyclotomic twist `μ_p` —
the form in which the classical Hasse–Brauer–Noether theorem is consumed by the Neukirch–Uchida
development — and derives from it the statements that the reduction to the inputs needs.  It is the
twisted counterpart of `Submission/Work/HassePrinciple/LevelHasse.lean`.

Let `L/K` be a finite Galois level inside the fixed separable closure, `U ≤ Gal(K'/K)` a subgroup
and `Γ = U/(U ⊓ Gal(K'/L))` the level group.  The **level obstruction**

`NK.HasseTwist.levelObstruction p U L ⊆ H²(Γ, μ_p(L))`

is the group of level classes that are locally trivial at *every* place of `K'` over a finite prime
of `K`.  The level-wise Hasse principle is the statement

  `∀ U L a, a ∈ levelObstruction p U L → a = 0`

("no non-zero finite-level class is locally trivial at its own level").  Classically this is
Hasse–Brauer–Noether for the relative extension `L/(L ⊓ K'^U)` in the coefficient-correct
(`μ_p`-)form: `Br(L/(L ⊓ K'^U))[p] ↪ ∏_w Br(L_w/(L ⊓ K'^U)_w)[p]` — see
`Submission/Work/HasseTwist/README.md`, §2 and §4, for the exact classical reference and for why
the labelling by `κ` (a `p`-adic field) is what makes the statement true.

## Main results

* `NK.HasseTwist.level_kernel_dies_of_obstructionTrivial` — the level-wise Sha² computation
  ("a locally trivial level class dies after inflation"), **derived** from the level-wise Hasse
  principle;
* `NK.HasseTwist.levelForm_of_labelledObstruction` — the Hasse principle in the level-wise form
  `NK.HasseTwist.LevelForm` of `Defs.lean`, from the labelled level-wise Hasse principle and the
  exhaustion of the kernel of the localisation by the level obstructions;
* `NK.HasseTwist.levelForm_of_obstructionTrivial` — the same for the unlabelled statement (kept
  for completeness: its hypothesis is the κ-free statement, which is *false*, see README §4).
-/

import Submission.NK.HasseTwist.Obstruction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

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
          (levelMap p U hLM) a = 0 := by
  intro U L a ha
  have hzero : a = 0 := h U L a ((mem_levelObstruction_iff p U L a).mpr ha)
  exact ⟨L, le_rfl, by rw [hzero, map_zero]⟩

/-- **The labelled level-wise Hasse principle plus the exhaustion of the kernel gives
`LevelForm`.**  This is `levelForm_of_obstructionTrivial` for the labelled levels only, i.e. with
the level-wise Hasse principle assumed for the closed subgroups `U ≤ Gal(K'/K)` isomorphic to
`Gal(κ'/κ)` (the hypothesis of `NK.HasseTwist.sha2Vanishing`). -/
theorem levelForm_of_labelledObstruction (p : ℕ)
    (h : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ (L : FiniteGaloisIntermediateField K K')
        (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0)
    (hC : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Twist p U,
        (∀ A : OverFinitePrime K K', H2Twist.loc p U x A = 0) →
          ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
            x = H2Twist.ofLevel p U L a ∧ a ∈ levelObstruction p U L) :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  intro U hU hκ L a ha
  have hx : ∀ A : OverFinitePrime K K', H2Twist.loc p U (H2Twist.ofLevel p U L a) A = 0 :=
    (levelLocVanishing_iff (p := p) (U := U) L a).mp ha
  obtain ⟨L', a', hxa', ha'⟩ := hC U hU hκ _ hx
  rw [hxa']
  calc H2Twist.ofLevel p U L' a'
      = H2Twist.ofLevel p U L' (0 : LevelH2 p U L') := by rw [h U hU hκ L' a' ha']
    _ = 0 := H2Twist.ofLevel_zero (p := p) (U := U) L'

/-- **The level-wise Hasse principle plus the exhaustion of the kernel gives `LevelForm`.**

`hC` says that a class whose localisations all vanish is represented at some finite level by a
class of the level obstruction (the exhaustion of the kernel of the localisation by the finite
levels); the level-wise Hasse principle then makes that representative zero.  The hypothesis is the
κ-free (unlabelled) level-wise Hasse principle, which is *false* (README §4); the statement is
recorded because it is the exact form of the reduction, and because its *labelled* version
`levelForm_of_labelledObstruction` is the one used by `NK.HasseTwist.sha2Vanishing`. -/
theorem levelForm_of_obstructionTrivial (p : ℕ)
    (h : ∀ (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
      (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0)
    (hC : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Twist p U,
        (∀ A : OverFinitePrime K K', H2Twist.loc p U x A = 0) →
          ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
            x = H2Twist.ofLevel p U L a ∧ a ∈ levelObstruction p U L) :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  intro U hU hκ L a ha
  have hx : ∀ A : OverFinitePrime K K', H2Twist.loc p U (H2Twist.ofLevel p U L a) A = 0 :=
    (levelLocVanishing_iff (p := p) (U := U) L a).mp ha
  obtain ⟨L', a', hxa', ha'⟩ := hC U hU hκ _ hx
  rw [hxa']
  calc H2Twist.ofLevel p U L' a'
      = H2Twist.ofLevel p U L' (0 : LevelH2 p U L') := by rw [h U L' a' ha']
    _ = 0 := H2Twist.ofLevel_zero (p := p) (U := U) L'

end NK.HasseTwist
