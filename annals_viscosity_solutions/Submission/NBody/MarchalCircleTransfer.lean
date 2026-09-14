import Submission.NBody.MarchalCircleAvg

/-!
# The `φ` function of the circle-average transfer

`circle_avg_inv_norm_le` (`Submission/NBody/MarchalCircleAvg.lean`) bounds the circle average of
`1/‖u + d e_θ‖` by the *planar* value `(1/2π)∫_θ ‖‖u‖•e + d e_θ‖⁻¹ dθ`.  This module introduces the
scalar function which governs that planar value,

  `phiFun x := (1/2π) ∫_θ ((1 + x² + 2x cos θ)^{-1/2} - 1) dθ`,

and proves the linchpin identity

  `(1/2π) ∫_θ ‖b•e + d e_θ‖⁻¹ dθ = (1 + phiFun (d/b))/b`   (`b > 0`),

so that the transfer to be compared with the model lemma
`Commons.Analysis.Integral.average_inv_parabolic_circle_neg` reads

  `(1/2π) ∫_θ ‖b•e + d e_θ‖⁻¹ dθ - 1/b = phiFun (d/b)/b`.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Submission.NBody

/-- The scalar transfer function `φ(x) = (1/2π)∫_θ ((1 + x² + 2x cos θ)^{-1/2} - 1)dθ`. -/
noncomputable def phiFun (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
    (((1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2)) - 1)

/-- The circle average of `φ`: the defining expression is already a θ-integral, but note that the
`1/2π (∫ 1) = 1` term has been moved inside. -/
lemma phiFun_eq (x : ℝ) :
    phiFun x = (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
      (((1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2)) - 1) := rfl

/-- `‖e + x • circVec e f θ‖² = 1 + x² + 2x cos θ` for an orthonormal pair. -/
lemma norm_add_smul_circVec_sq' {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (x : ℝ) (θ : ℝ) :
    ‖e + x • circVec e f θ‖ ^ 2 = 1 + x ^ 2 + 2 * x * Real.cos θ := by
  have h1 : inner ℝ e (x • circVec e f θ) = x * Real.cos θ := by
    rw [inner_smul_right, inner_circVec e e f θ, real_inner_self_eq_norm_sq, he, hef]
    ring
  rw [norm_add_sq_real, h1, norm_smul, norm_circVec he hf hef θ, mul_one, Real.norm_eq_abs,
    sq_abs, he]
  ring

end Submission.NBody

namespace Submission.NBody

/-- **The linchpin identity of the transfer.**  For `b > 0` and `d/b ≠ 1` the planar circle average
of `1/‖b e + d e_θ‖` is `(1 + φ(d/b))/b`. -/
theorem circle_avg_inv_norm_eq_phiFun {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) {b d : ℝ} (hb : 0 < b) (hd : 0 ≤ d) (hne : d / b ≠ 1) :
    (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), (‖(b : ℝ) • e + d • circVec e f θ‖)⁻¹
      = (1 + phiFun (d / b)) / b := by
  set x : ℝ := d / b with hx
  have hx1 : x ≠ 1 := by rw [hx]; exact hne
  have hbx : d = x * b := by rw [hx]; field_simp
  have hbne : b ≠ 0 := ne_of_gt hb
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hbase : ∀ θ : ℝ, 0 < 1 + x ^ 2 + 2 * x * Real.cos θ := by
    intro θ
    have h1 : -x ≤ x * Real.cos θ := by nlinarith [Real.neg_one_le_cos θ, hx0]
    have h3 : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx1)
    nlinarith
  have hpt : ∀ θ : ℝ, (‖(b : ℝ) • e + d • circVec e f θ‖)⁻¹
      = (1 / b) * ((1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2)) := by
    intro θ
    have h1 : (b : ℝ) • e + d • circVec e f θ = b • (e + x • circVec e f θ) := by
      rw [hbx, smul_add, smul_smul]
      rw [mul_comm x b]
    rw [h1, norm_smul, Real.norm_of_nonneg hb.le, mul_inv,
      inv_norm_eq_rpow_neg_half (le_of_lt (hbase θ)) (norm_add_smul_circVec_sq' he hf hef x θ),
      one_div]
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul]
  have hcont : Continuous (fun θ : ℝ => (1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2)) := by
    refine Continuous.rpow_const (by fun_prop) fun θ => Or.inl ?_
    exact ne_of_gt (hbase θ)
  have hcont' : Continuous (fun θ : ℝ => ((1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2)) - 1) :=
    hcont.sub continuous_const
  have h2 : ∫ θ in (0)..(2 * Real.pi), ((1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2))
      = (∫ θ in (0)..(2 * Real.pi),
          (((1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2)) - 1)) + 2 * Real.pi := by
    have hsum := intervalIntegral.integral_add (hcont'.intervalIntegrable _ _)
      (Continuous.intervalIntegrable (continuous_const : Continuous fun _ : ℝ => (1:ℝ))
        (μ := volume) (0:ℝ) (2 * Real.pi))
    rw [intervalIntegral.integral_const] at hsum
    have h3 : (fun θ : ℝ => (((1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2)) - 1) + 1)
        = fun θ : ℝ => ((1 + x ^ 2 + 2 * x * Real.cos θ) ^ (-(1:ℝ)/2)) := by
      ext θ; ring
    rw [h3] at hsum
    rw [hsum]; ring
  rw [h2]
  unfold phiFun
  field_simp
  ring

end Submission.NBody
