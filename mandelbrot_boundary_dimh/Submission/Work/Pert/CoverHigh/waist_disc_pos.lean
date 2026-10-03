import Mathlib
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.Gates

namespace Work.Pert.CoverHigh

open Metric

/-!
# PERT · `Work.Pert.CoverHigh.waist_disc_pos`

The disc of radius `ρ ≥ 0` centred at `(Σ + 2ρ) · i`, where
`Σ = |(1/α).re| + |(1/α).im| + |Ξ| + 4`, lies in the waist
`Qm Ξ α ∩ Qp Ξ α` of the two §4.2 gates.

Write `z = x + i y` and `a = 1/α`.  From `‖z - (Σ+2ρ) i‖ ≤ ρ` we get

* `|x| ≤ ρ`,
* `y ≥ Σ + ρ = |a.re| + |a.im| + |Ξ| + 4 + ρ`,

so in particular `y ≥ |Ξ| + 4 > 0` and `y ≥ |a.im| + ρ + |Ξ| + 4`.  The four membership
inequalities are then the four numerical facts

* `Qm` left: `Ξ - a.re - |y + a.im| < x`, using `|y + a.im| ≥ y + a.im` and
  `R > Ξ - a.re - a.im + 2ρ`,
* `Qm` right: `x < |y| - Ξ`, using `R > 2ρ + Ξ`,
* `Qp` left: `Ξ - |y| < x`, again using `R > 2ρ + Ξ`,
* `Qp` right: `x < a.re - Ξ + |y - a.im|`, using `|y - a.im| ≥ y - a.im` and
  `R > 2ρ + Ξ + a.im - a.re`,

and each of the three inequalities on `R = |a.re| + |a.im| + 2ρ + |Ξ| + 4` is a sum of the
three nonnegative quantities `|a.re| + a.re`, `|a.im| ± a.im`, `|Ξ| - Ξ` and `4`.
-/

theorem waist_disc_pos (Ξ : ℝ) (α : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Metric.closedBall ((((|(1/α).re| + |(1/α).im| + 2 * ρ + |Ξ| + 4 : ℝ)) : ℂ) * Complex.I) ρ
      ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := by
  intro z hz
  set R : ℝ := |(1/α).re| + |(1/α).im| + 2 * ρ + |Ξ| + 4 with hR
  have hnorm : ‖z - ((R : ℂ) * Complex.I)‖ ≤ ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact hz
  -- coordinate bounds for `z`
  have hre : |z.re| ≤ ρ := by
    have h := Complex.abs_re_le_norm (z - ((R : ℂ) * Complex.I))
    have h' : (z - ((R : ℂ) * Complex.I)).re = z.re := by simp
    rw [h'] at h
    exact le_trans h hnorm
  have him : |z.im - R| ≤ ρ := by
    have h := Complex.abs_im_le_norm (z - ((R : ℂ) * Complex.I))
    have h' : (z - ((R : ℂ) * Complex.I)).im = z.im - R := by simp
    rw [h'] at h
    exact le_trans h hnorm
  have hzre_le : z.re ≤ ρ := (abs_le.mp hre).2
  have hzre_ge : -ρ ≤ z.re := (abs_le.mp hre).1
  have hzim_ge : R - ρ ≤ z.im := by linarith [(abs_le.mp him).1]
  -- the three scalar inequalities on `R`
  have hA : 2 * ρ + Ξ < R := by
    rw [hR]
    have h1 : (0:ℝ) ≤ |(1/α).re| := abs_nonneg _
    have h2 : (0:ℝ) ≤ |(1/α).im| := abs_nonneg _
    have h3 : (0:ℝ) ≤ |Ξ| - Ξ := by linarith [le_abs_self Ξ]
    linarith
  have hB : Ξ - (1/α).re - (1/α).im + 2 * ρ < R := by
    rw [hR]
    have h1 : (0:ℝ) ≤ |(1/α).re| + (1/α).re := by linarith [neg_abs_le ((1/α).re)]
    have h2 : (0:ℝ) ≤ |(1/α).im| + (1/α).im := by linarith [neg_abs_le ((1/α).im)]
    have h3 : (0:ℝ) ≤ |Ξ| - Ξ := by linarith [le_abs_self Ξ]
    linarith
  have hC : 2 * ρ + Ξ + (1/α).im - (1/α).re < R := by
    rw [hR]
    have h1 : (0:ℝ) ≤ |(1/α).re| + (1/α).re := by linarith [neg_abs_le ((1/α).re)]
    have h2 : (0:ℝ) ≤ |(1/α).im| - (1/α).im := by linarith [le_abs_self ((1/α).im)]
    have h3 : (0:ℝ) ≤ |Ξ| - Ξ := by linarith [le_abs_self Ξ]
    linarith
  -- `z` is high in the upper half-plane
  have hzim_ge_absΞ : |Ξ| + 4 ≤ z.im := by
    have h1 : |Ξ| + 4 ≤ R - ρ := by
      rw [hR]
      have h2 : (0:ℝ) ≤ |(1/α).re| := abs_nonneg _
      have h3 : (0:ℝ) ≤ |(1/α).im| := abs_nonneg _
      linarith
    linarith
  have hzim_nonneg : 0 ≤ z.im := by linarith [hzim_ge_absΞ, abs_nonneg Ξ]
  -- the four membership inequalities
  have hQm1 : Ξ - (1/α).re - |z.im + (1/α).im| < z.re := by
    have habs : z.im + (1/α).im ≤ |z.im + (1/α).im| := le_abs_self _
    linarith [hB, hzre_ge, hzim_ge, habs]
  have hQm2 : z.re < |z.im| - Ξ := by
    rw [abs_of_nonneg hzim_nonneg]
    linarith [hA, hzre_le, hzim_ge]
  have hQp1 : Ξ - |z.im| < z.re := by
    rw [abs_of_nonneg hzim_nonneg]
    linarith [hA, hzre_ge, hzim_ge]
  have hQp2 : z.re < (1/α).re - Ξ + |z.im - (1/α).im| := by
    have habs : z.im - (1/α).im ≤ |z.im - (1/α).im| := le_abs_self _
    linarith [hC, hzre_le, hzim_ge, habs]
  refine ⟨?_, ?_⟩
  · rw [← Complex.re_add_im z, Qm_mem_iff']
    exact ⟨hQm1, hQm2⟩
  · rw [← Complex.re_add_im z, Qp_mem_iff]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, zero_add, sub_eq_add_neg, neg_zero]
    exact ⟨hQp1, hQp2⟩

end Work.Pert.CoverHigh
