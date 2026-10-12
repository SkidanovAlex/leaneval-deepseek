import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.CellDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.FoldDefs` — the folding map and the folded mass profile

The **folding** of `ℝ³` onto the `ℓ`-cell `cell ℓ = [-ℓ/2, ℓ/2]³`: `foldMap ℓ u` is the point of
the closed cell congruent to `u` modulo the lattice `ℓℤ³` (componentwise: `uᵢ - ℓ·round(uᵢ/ℓ)`).
It is the geometric object behind the identity
`period W ℓ dx = (foldMap ℓ)_* (W dx)` (the `ℓ`-periodisation of a charge is the folding of the
charge onto one cell), and behind the layer-cake description of the *cell* Coulomb energy of the
periodised charge.

`foldMass ℓ W r` is the mass of the folded charge inside the ball of radius `r` (the *mass profile*
of the pushforward of `W dx`).

Everything here is elementary; the analytic statements about `foldMass` and the Coulomb energy of
the folded charge live in the modules that import this one.
-/

noncomputable section

open MeasureTheory Set
open scoped Real BigOperators

namespace Work.BoseFixR.LatGreen

/-- The **folding** of `ℝ³` onto the `ℓ`-cell: the componentwise map
`u ↦ (uᵢ - ℓ·round(uᵢ/ℓ))ᵢ`, landing in `cell ℓ` and congruent to `u` modulo `ℓℤ³`. -/
noncomputable def foldMap (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => u i - ℓ * (round (u i / ℓ) : ℝ))

@[simp] lemma foldMap_apply (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    foldMap ℓ u i = u i - ℓ * (round (u i / ℓ) : ℝ) := rfl

/-- Each coordinate of the folding is bounded in absolute value by that of `u`. -/
lemma abs_foldMap_apply_le_abs {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    |foldMap ℓ u i| ≤ |u i| := by
  have hm : u i / ℓ * ℓ = u i := by field_simp
  have habs := abs_sub_round (u i / ℓ)
  have h1 : -(1 / 2 : ℝ) ≤ u i / ℓ - (round (u i / ℓ) : ℝ) := (abs_le.mp habs).1
  have h2 : u i / ℓ - (round (u i / ℓ) : ℝ) ≤ 1 / 2 := (abs_le.mp habs).2
  have e1 : -(ℓ / 2) ≤ u i - ℓ * (round (u i / ℓ) : ℝ) := by nlinarith [h1, hm]
  have e2 : u i - ℓ * (round (u i / ℓ) : ℝ) ≤ ℓ / 2 := by nlinarith [h2, hm]
  by_cases h : ℓ / 2 ≤ |u i|
  · rw [foldMap_apply]
    exact le_trans (abs_le.mpr ⟨e1, e2⟩) h
  · have hlt : |u i| < ℓ / 2 := lt_of_not_ge h
    have hlt' : |u i / ℓ| < 1 / 2 := by
      rw [abs_div, abs_of_pos hℓ, div_lt_iff₀ hℓ]
      linarith
    have hr : round (u i / ℓ) = 0 := by
      rw [round_eq_zero_iff]
      exact ⟨by linarith [(abs_lt.mp hlt').1], by linarith [(abs_lt.mp hlt').2]⟩
    rw [foldMap_apply, hr]
    simp

/-- `‖foldMap ℓ u‖ ≤ ‖u‖`: the folding contracts towards the origin. -/
lemma norm_foldMap_le {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) :
    ‖foldMap ℓ u‖ ≤ ‖u‖ := by
  have hsq : ‖foldMap ℓ u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := abs_foldMap_apply_le_abs hℓ u i
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [abs_nonneg (foldMap ℓ u i), abs_nonneg (u i)]
  nlinarith [norm_nonneg (foldMap ℓ u), norm_nonneg u]

/-- The **mass profile of the folded charge** `W dx` at radius `r`: the total mass (weighted by `W`)
over the set of points whose folding lies within distance `r` of the origin. -/
noncomputable def foldMass (ℓ : ℝ) (W : EuclideanSpace ℝ (Fin 3) → ℝ) (r : ℝ) : ℝ :=
  ∫ u : EuclideanSpace ℝ (Fin 3),
    W u * Set.indicator {u : EuclideanSpace ℝ (Fin 3) | ‖foldMap ℓ u‖ ≤ r} (fun _ => (1 : ℝ)) u

end Work.BoseFixR.LatGreen
