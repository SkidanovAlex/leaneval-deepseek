import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `boxP` over the sliding box is a mean: `|boxP_{B(u),i} Φ| ≤ M` for `|Φ| ≤ M`

`Work.SmallBoxTBWord.boxP volA A i Φ x = (1/volA) * ∫ z in A, Φ (x_{i←z})` with the
*true* box volume `volA = Work.SmallBoxSliding.boxMass ℓ d u = |dlBox ℓ d u|`
(`boxMass_eq_measureReal`).  Hence `boxP` is a mean of the updated states over the
box `B(u) = dlBox ℓ d u`, and it inherits any pointwise bound on `Φ`.

The only structural input is that the box `B(u)` lies inside the big box on which
the bound on `Φ` is assumed (`dlBox_subset_acube` / `mem_dlBox_iff`), plus the
finiteness of its volume (`volume_dlBox_lt_top`); the bound on the box integral is
`norm_setIntegral_le_of_norm_le_const`, which needs no measurability of the
integrand.

The degenerate case `boxMass ℓ d u = 0` (an empty box) is handled by
`boxP = 0⁻¹ * _ = 0`, with `0 ≤ M` extracted from the hypothesis `hM` itself
(the point `x_{i←0}` lies in the big box, since `0 ∈ acube ℓ` for `ℓ > 0`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- An elementary but useful fact: the origin lies in the box `acube ℓ` for `ℓ > 0`. -/
lemma zero_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (0 : EuclideanSpace ℝ (Fin 3)) ∈ Submission.BoseGases.acube ℓ := by
  intro m
  simp only [Set.mem_Icc, WithLp.ofLp_zero, Pi.zero_apply, neg_div]
  constructor <;> linarith

/-- Replacing the slot-`i` coordinate of `x` by `z₀` and then by `z` is the same as
replacing it by `z` directly. -/
lemma update_update_eq {N : ℕ} (x : Submission.BoseGases.X N) (i : Fin N)
    (z₀ z : EuclideanSpace ℝ (Fin 3)) :
    Function.update (Function.update x i z₀) i z = Function.update x i z := by
  funext a
  rw [Function.update_apply, Function.update_apply, Function.update_apply]
  by_cases ha : a = i
  · simp only [if_pos ha]
  · simp only [if_neg ha]

/-- **`boxP` is bounded by the bound on `Φ`.**  If `|Φ| ≤ M` on all configurations
whose coordinates lie in the big box `acube ℓ`, then the slot-`i` mean of `Φ` over the
sliding box `B(u) = dlBox ℓ d u` (taken at any configuration `x` with all coordinates
in `acube ℓ`, and after updating the slot `i` to an arbitrary `z₀`) is bounded by `M`. -/
theorem boxP_dlBox_abs_le {N : ℕ} {ℓ d M : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hM : ∀ x : Submission.BoseGases.X N,
      (∀ j : Fin N, x j ∈ Submission.BoseGases.acube ℓ) → |Φ x| ≤ M)
    (i : Fin N) (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X N)
    (z₀ : EuclideanSpace ℝ (Fin 3))
    (hx : ∀ j : Fin N, x j ∈ Submission.BoseGases.acube ℓ) :
    |Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i z₀)| ≤ M := by
  -- `0 ≤ M`, from `hM` at the configuration `x_{i←0}` (whose coordinates all lie in
  -- `acube ℓ`).
  have hM0 : 0 ≤ M := by
    refine le_trans (abs_nonneg (Φ (Function.update x i (0 : EuclideanSpace ℝ (Fin 3)))))
      (hM _ ?_)
    intro j
    rw [Function.update_apply]
    by_cases hj : j = i
    · simp only [if_pos hj]
      exact zero_mem_acube hℓ
    · simp only [if_neg hj]
      exact hx j
  -- The integrand of `boxP` written with `x_{i←z₀}` is the integrand with `x_{i←z}`.
  have hIeq : (∫ z in Submission.BoseGases.dlBox ℓ d u,
        Φ (Function.update (Function.update x i z₀) i z))
      = ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (Function.update x i z) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [update_update_eq x i z₀ z]
  -- The box integral of the (pointwise bounded) integrand is bounded by `M·|B(u)|`.
  have hJ : |∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (Function.update x i z)| ≤
      M * Work.SmallBoxSliding.boxMass ℓ d u := by
    have hfin : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
      Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (f := fun z : EuclideanSpace ℝ (Fin 3) => Φ (Function.update x i z))
      (s := Submission.BoseGases.dlBox ℓ d u) (C := M) hfin ?_
    · rw [Real.norm_eq_abs] at h
      rwa [← Work.SmallBoxSliding.boxMass_eq_measureReal] at h
    · intro z hz
      rw [Real.norm_eq_abs]
      refine hM _ ?_
      intro j
      rw [Function.update_apply]
      by_cases hj : j = i
      · rw [if_pos hj]
        exact (Submission.BoseGases.mem_dlBox_iff ℓ d u z).1 hz |>.1
      · rw [if_neg hj]
        exact hx j
  rw [Work.SmallBoxTBWord.boxP, one_div, hIeq]
  -- `boxMass` is a (nonnegative) volume.
  have hVnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal]
    exact MeasureTheory.measureReal_nonneg
  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · -- degenerate (empty) box: `boxP = 0⁻¹ * _ = 0`
    rw [← hV0, inv_zero, zero_mul, abs_zero]
    exact hM0
  · -- genuine mean: divide the integral bound by the box volume
    rw [abs_mul, abs_of_pos (inv_pos.mpr hVpos)]
    refine le_trans (mul_le_mul_of_nonneg_left hJ (le_of_lt (inv_pos.mpr hVpos))) (le_of_eq ?_)
    rw [mul_comm M (Work.SmallBoxSliding.boxMass ℓ d u), ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hVpos), one_mul]

end Work.BoseFixB1
