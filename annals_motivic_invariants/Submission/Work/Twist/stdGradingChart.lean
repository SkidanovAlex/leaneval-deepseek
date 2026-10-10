/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Twist
-/
import Mathlib
import Submission.Work.Twist.away_chart_mvPolynomial
import Submission.Work.Twist.away_chart_mvPolynomial_X

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Permuting the coordinates of `ℙⁿ` and the charts `D₊(X_i)`

The standard grading `stdGrading 𝕜 n = MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜` of
`𝕜[X₀,…,Xₙ]` is stable under permuting the variables: for `σ : Equiv.Perm (Fin (n+1))` the algebra
map `MvPolynomial.rename σ` sends homogeneous polynomials of degree `d` to homogeneous polynomials
of degree `d`, so it induces a *graded* ring endomorphism `gradingRename 𝕜 n σ` of `stdGrading 𝕜 n`.

Specialising to the transposition `chartSwap i = Equiv.swap 0 i`, `gradingRename` restricts to a
ring endomorphism of the degree-zero part `↥(stdGrading 𝕜 n 0)` and induces, via
`HomogeneousLocalization.map`, ring homomorphisms

* `chartAwayMap    𝕜 n i : A⁰_{X_i} →+* A⁰_{X_0}`,
* `chartAwayMapInv 𝕜 n i : A⁰_{X_0} →+* A⁰_{X_i}`

between the degree-zero parts of the localisations at `X_i` and at `X₀`.  These are inverse to each
other (the transposition is an involution), and they intertwine the structure maps
`fromZeroRingHom` over the constants.

This file contains the definitions and the elementary facts; the three structural lemmas
`chartAwayMapInv_comp_chartAwayMap`, `chartAwayMap_comp_chartAwayMapInv` and
`chartAwayMap_fromZeroRingHom` are proved in the sibling modules of this directory and are what the
chart-independence of smoothness (`Work.Twist.ringHom_smooth_fromZeroRingHom_X_iff`) rests on.
-/

set_option autoImplicit false

namespace Work.Twist

open MvPolynomial HomogeneousLocalization

noncomputable section

/-! ## The graded ring endomorphism induced by a permutation of the variables -/

/-- The graded ring endomorphism of the standard grading on `𝕜[X₀,…,Xₙ]` induced by a
permutation `σ` of the variables: `MvPolynomial.rename σ`, which preserves homogeneity. -/
def gradingRename (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    stdGrading 𝕜 n →+*ᵍ stdGrading 𝕜 n where
  toRingHom := (MvPolynomial.rename σ).toRingHom
  map_mem := by
    intro i x hx
    exact hx.rename_isHomogeneous

@[simp]
lemma gradingRename_apply (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (p : MvPolynomial (Fin (n + 1)) 𝕜) :
    gradingRename 𝕜 n σ p = MvPolynomial.rename σ p := rfl

lemma gradingRename_X (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) :
    gradingRename 𝕜 n σ (MvPolynomial.X j) = MvPolynomial.X (σ j) := by
  rw [gradingRename_apply, MvPolynomial.rename_X]

lemma gradingRename_comp_self (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ j, σ (σ j) = j) :
    (gradingRename 𝕜 n σ).comp (gradingRename 𝕜 n σ) = GradedRingHom.id (stdGrading 𝕜 n) := by
  refine GradedRingHom.ext fun p => ?_
  show MvPolynomial.rename σ (MvPolynomial.rename σ p) = p
  rw [MvPolynomial.rename_rename]
  have h : σ ∘ σ = id := funext hσ
  rw [h, MvPolynomial.rename_id_apply]

/-! ## The coordinate transposition `X₀ ↔ X_i` -/

/-- The graded automorphism of `stdGrading 𝕜 n` induced by the coordinate transposition
`X₀ ↔ X_i`. -/
abbrev chartRename (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    stdGrading 𝕜 n →+*ᵍ stdGrading 𝕜 n :=
  gradingRename 𝕜 n (chartSwap i)

@[simp]
lemma chartRename_X_self (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    chartRename 𝕜 n i (MvPolynomial.X i) = MvPolynomial.X (0 : Fin (n + 1)) := by
  rw [chartRename, gradingRename_X, chartSwap_self]

@[simp]
lemma chartRename_X_zero (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    chartRename 𝕜 n i (MvPolynomial.X (0 : Fin (n + 1))) = MvPolynomial.X i := by
  rw [chartRename, gradingRename_X, chartSwap_zero]

lemma chartRename_comp_self (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    (chartRename 𝕜 n i).comp (chartRename 𝕜 n i) = GradedRingHom.id (stdGrading 𝕜 n) :=
  gradingRename_comp_self 𝕜 n _ (chartSwap_involutive i)

/-! ## The induced maps between the chart rings `A⁰_{X_i}` and `A⁰_{X_0}` -/

/-- The ring homomorphism `A⁰_{X_i} →+* A⁰_{X_0}` of the chart rings of `ℙⁿ` induced by the
coordinate transposition `X₀ ↔ X_i`. -/
def chartAwayMap (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Away (stdGrading 𝕜 n) (MvPolynomial.X i) →+*
      Away (stdGrading 𝕜 n) (MvPolynomial.X (0 : Fin (n + 1))) :=
  HomogeneousLocalization.map (chartRename 𝕜 n i) (by
    rintro x ⟨k, rfl⟩
    exact ⟨k, by rw [map_pow, chartRename_X_self]⟩)

/-- The ring homomorphism `A⁰_{X_0} →+* A⁰_{X_i}` of the chart rings of `ℙⁿ` induced by the
coordinate transposition `X₀ ↔ X_i`; the inverse of `chartAwayMap`. -/
def chartAwayMapInv (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Away (stdGrading 𝕜 n) (MvPolynomial.X (0 : Fin (n + 1))) →+*
      Away (stdGrading 𝕜 n) (MvPolynomial.X i) :=
  HomogeneousLocalization.map (chartRename 𝕜 n i) (by
    rintro x ⟨k, rfl⟩
    exact ⟨k, by rw [map_pow, chartRename_X_zero]⟩)

end

end Work.Twist
