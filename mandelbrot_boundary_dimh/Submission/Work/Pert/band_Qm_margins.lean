import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Qm_slice

set_option linter.unusedVariables false

namespace Work.Pert

open MandelDim Complex Set Metric

noncomputable section

/-- `InF1 α` (`|Im α| < Re α`) gives the sharp lower bound `1/(√2 ‖α‖) ≤ Re (1/α)`: the inversion
sends the 45° sector around the positive real axis into itself, so with `Re (1/α) = α.re/‖α‖²` and
`α.re > ‖α‖/√2` we get `Re (1/α) > ‖α‖/(√2 ‖α‖²) = 1/(√2 ‖α‖)`. -/
theorem band_Qm_inv_re_lower {α : ℂ} (hF1 : MandelDim.InF1 α) :
    1 / (Real.sqrt 2 * ‖α‖) ≤ (1 / α).re := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hnorm : 0 < ‖α‖ := norm_pos_iff.mpr hne
  have hn2 : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hIm : α.im ^ 2 < α.re ^ 2 := by
    have h := abs_lt.mp hF1
    nlinarith [h.1, h.2, hre]
  have hlt : ‖α‖ ≤ Real.sqrt 2 * α.re := by
    have h2 : ‖α‖ ^ 2 ≤ (Real.sqrt 2 * α.re) ^ 2 := by
      rw [hn2, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith
    have hb : 0 ≤ Real.sqrt 2 * α.re := by positivity
    have habs := (sq_le_sq.mp h2)
    rwa [abs_of_nonneg (norm_nonneg α), abs_of_nonneg hb] at habs
  have hinv : (1 / α).re = α.re / ‖α‖ ^ 2 := by
    simp only [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hinv, div_le_div_iff₀ (by positivity) (pow_pos hnorm 2)]
  have hstep : ‖α‖ ^ 2 ≤ α.re * (Real.sqrt 2 * ‖α‖) := by
    calc ‖α‖ ^ 2 = ‖α‖ * ‖α‖ := by ring
      _ ≤ (Real.sqrt 2 * α.re) * ‖α‖ := mul_le_mul_of_nonneg_right hlt hnorm.le
      _ = α.re * (Real.sqrt 2 * ‖α‖) := by ring
  linarith

/-- The numerical core of the gate margins: `InF1 α` and `‖α‖ ≤ 1/(32 (M+2+Ξ))` force
`18 M + 2Ξ + 2^10 ≤ Re (1/α)`.  Indeed `Re (1/α) ≥ 1/(√2 ‖α‖) ≥ 16√2 (M+2+Ξ)`, and
`16√2 ≥ 112/5` so it suffices that `18M + 2Ξ + 2^10 ≤ (112/5)(M+2+Ξ)`, which holds for
`M ≥ 2^10`. -/
theorem band_Qm_key_bound {Ξ M : ℝ} {α : ℂ} (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M)
    (hF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) :
    18 * M + 2 * Ξ + 2 ^ 10 ≤ (1 / α).re := by
  have hM1024 : (1024 : ℝ) ≤ M := by
    have h := hM; norm_num at h; exact h
  have hX : 0 < M + 2 + Ξ := by linarith
  have hX32 : 0 < 32 * (M + 2 + Ξ) := by linarith
  have hnorm : 0 < ‖α‖ := by
    have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
    exact norm_pos_iff.mpr (by intro h; rw [h] at hre; simp at hre)
  -- step 1
  have h1 : 1 / (Real.sqrt 2 * ‖α‖) ≤ (1 / α).re := band_Qm_inv_re_lower hF1
  -- step 2
  have hmul : ‖α‖ * (32 * (M + 2 + Ξ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hα hX32.le
    rwa [one_div, inv_mul_cancel₀ hX32.ne'] at h
  have h2 : 16 * Real.sqrt 2 * (M + 2 + Ξ) ≤ 1 / (Real.sqrt 2 * ‖α‖) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2 * ‖α‖)]
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have heq : 16 * Real.sqrt 2 * (M + 2 + Ξ) * (Real.sqrt 2 * ‖α‖)
        = ‖α‖ * (32 * (M + 2 + Ξ)) := by
      calc 16 * Real.sqrt 2 * (M + 2 + Ξ) * (Real.sqrt 2 * ‖α‖)
          = 16 * (Real.sqrt 2 * Real.sqrt 2) * ((M + 2 + Ξ) * ‖α‖) := by ring
        _ = 16 * 2 * ((M + 2 + Ξ) * ‖α‖) := by rw [hs2]
        _ = ‖α‖ * (32 * (M + 2 + Ξ)) := by ring
    rw [heq]
    linarith
  -- step 3
  have h3 : 18 * M + 2 * Ξ + 2 ^ 10 ≤ 16 * Real.sqrt 2 * (M + 2 + Ξ) := by
    have hs2low : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hcoef : (112 : ℝ) / 5 ≤ 16 * Real.sqrt 2 := by linarith
    have hmul2 : (112 : ℝ) / 5 * (M + 2 + Ξ) ≤ 16 * Real.sqrt 2 * (M + 2 + Ξ) :=
      mul_le_mul_of_nonneg_right hcoef hX.le
    have hnum : 18 * M + 2 * Ξ + 2 ^ 10 ≤ (112 : ℝ) / 5 * (M + 2 + Ξ) := by
      have h2p : (2 : ℝ) ^ 10 = 1024 := by norm_num
      rw [h2p]
      linarith
    linarith
  linarith

theorem band_Qm_margins {Ξ M : ℝ} {α : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))) :
    16 * M ≤ (1 / α).re ∧
    ∀ ξ s : ℝ, -(Ξ + 2 ^ 10 + 2 * M) ≤ ξ → ξ ≤ -(Ξ + 2 ^ 10) →
      (ξ + s * Complex.I) ∈ Work.Pert.Qm Ξ α ∧
        2 ^ 10 ≤ |s| - Ξ - ξ ∧
        16 * M ≤ ξ + (1 / α).re - Ξ + |s + (1 / α).im| ∧
        ∀ w : ℂ, ‖w - (ξ + s * Complex.I)‖ < 2 ^ 8 →
          Metric.ball w (2 ^ 8) ⊆ Work.Pert.Qm Ξ α := by
  have hM1024 : (1024 : ℝ) ≤ M := by
    have h := hM; norm_num at h; exact h
  have hkey : 18 * M + 2 * Ξ + 2 ^ 10 ≤ (1 / α).re := band_Qm_key_bound hΞ hM hInF1 hα
  refine ⟨by linarith, ?_⟩
  intro ξ s hξlo hξhi
  have hB2 : 2 ^ 10 ≤ |s| - Ξ - ξ := by
    have := abs_nonneg s
    linarith
  have hB3 : 16 * M ≤ ξ + (1 / α).re - Ξ + |s + (1 / α).im| := by
    have := abs_nonneg (s + (1 / α).im)
    linarith
  have hB1 : (ξ + s * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    rw [Qm_mem_iff']
    constructor
    · linarith
    · linarith
  refine ⟨hB1, hB2, hB3, ?_⟩
  -- the gate contains the ball of radius `2^9` around the band point
  have hMpos : 0 < M := by linarith
  have hrad : ((2 : ℝ) ^ 9) * Real.sqrt 2 ≤ 1024 := by
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h9 : (2 : ℝ) ^ 9 = 512 := by norm_num
    rw [h9]
    nlinarith
  have hball : Metric.ball (ξ + s * Complex.I) ((2 : ℝ) ^ 9) ⊆ Work.Pert.Qm Ξ α := by
    refine ball_subset_Qm_of_margin_slice hB1 (le_trans hrad (le_min ?_ ?_))
    · rw [sliceLo]; linarith
    · rw [sliceHi]; linarith
  intro w hw u hu
  apply hball
  rw [Metric.mem_ball] at hu ⊢
  have htri : dist u (ξ + s * Complex.I) ≤ dist u w + dist w (ξ + s * Complex.I) :=
    dist_triangle _ _ _
  have hdw : dist w (ξ + s * Complex.I) < (2 : ℝ) ^ 8 := by
    rwa [dist_eq_norm]
  have h512 : (2 : ℝ) ^ 8 + (2 : ℝ) ^ 8 = (2 : ℝ) ^ 9 := by norm_num
  linarith

end

end Work.Pert
