/-
# The removable coincidence lies in the swept left rectangle (far side)

CKMRV §5.3 deforms the contour across the line `Re τ = 1` by pushing the *left* detour at the
height `1/τ.im` through the removable coincidence `ST⁻¹τ = -1/(τ-1)`.  On the far side
(`1 < Re τ`) this point lies strictly *left* of the imaginary axis, so it is genuinely swept by
the detour and must be located inside the rectangle `I₂ × [-ξ₂,0]`; this is the hypothesis
`hcoinc` of `Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far`.

The estimate: for `τ` in the ball `B(1 + i s₀, ε)` with `τ.re > 1`,

  `coincℂ τ = -1/(τ - 1)`,  `(coincℂ τ).re = (1 - τ.re)/‖τ-1‖²`,  `(coincℂ τ).im = τ.im/‖τ-1‖²`,

and `τ - 1 = u + i v` with `0 < u < 3 s₀ ε`, `|v - s₀| < 3 s₀ ε`; hence
`‖τ-1‖² = u² + v²` is trapped between `(s₀(1-3ε))²` and `s₀²(1+6ε+18ε²)`, which gives

  `|(coincℂ τ).re| ≤ 3s₀ε/(s₀(1-3ε))² ≤ 16 ε/s₀ ≤ ξ₂`,
  `|(coincℂ τ).im - s₀⁻¹| ≤ 9ε/(s₀(1-3ε)) ≤ 16 ε/s₀ ≤ A₂`.

The numerical slack `16ε ≤ A₂ s₀`, `16ε ≤ ξ₂ s₀` (with `ε ≤ 1/8`) is the one provided by
`Work.LayerCont.ECS.exists_contour_left_data` (`4ε ≤ A₂ s₀`, `4ε ≤ ξ₂ s₀`) after shrinking `ε`
by a factor `4`; the callers below always do so.
-/
import Mathlib
import Submission.Work.LayerCont.FarTail.Defs
import Submission.Work.LayerCont.Coinc.Defs
import Submission.Work.Asymptotics.contourLeftAux

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

open Work.Asymptotics Work.LayerCont.Coinc

/-- **The coincidence `ST⁻¹τ = -1/(τ-1)` lies in the swept left rectangle on the far side.**

For `τ` in the hyperbolic ball `B(1 + i s₀, ε)` with `1 < τ.re` and `s₀ > 1`, the point
`coincℂ τ` lies in the open left rectangle `(-ξ₂, 0) × (s₀⁻¹-A₂, s₀⁻¹+A₂)`, provided the ball is
small compared with `A₂` and `ξ₂` (`16ε ≤ A₂ s₀`, `16ε ≤ ξ₂ s₀`, `ε ≤ 1/8`). -/
theorem coinc_mem_openLeftRect_far {s₀ A₂ ξ₂ ε : ℝ} (hs₀ : 0 < s₀)
    (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hε8 : ε ≤ 1 / 8)
    (hεA : 16 * ε ≤ A₂ * s₀) (hεξ : 16 * ε ≤ ξ₂ * s₀) :
    ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ s₀⁻¹ A₂ ξ₂ := by
  intro τ hτ hτre
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨h1, h2⟩ := Work.Asymptotics.abs_re_im_sub_lt hs₀ hε hε1 hτ
  obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
  obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
  set N : ℝ := ‖(τ : ℂ) - 1‖ ^ 2 with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]; exact Work.LayerCont.Coinc.norm_tau_sub_one_pos τ
  have hN : N = (τ.re - 1) ^ 2 + τ.im ^ 2 := by
    rw [hNdef, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hδpos : 0 < 1 - 3 * ε := by linarith
  have hvlo : s₀ * (1 - 3 * ε) < τ.im := by linarith
  have hspos : 0 < s₀ * (1 - 3 * ε) := mul_pos hs₀ hδpos
  have hNlo : (s₀ * (1 - 3 * ε)) ^ 2 < N := by
    have hsq : (s₀ * (1 - 3 * ε)) ^ 2 < τ.im ^ 2 := sq_lt_sq.mpr (by
      rw [abs_of_nonneg hspos.le, abs_of_pos τ.im_pos]; exact hvlo)
    rw [hN]; nlinarith [hsq, sq_nonneg (τ.re - 1)]
  have hDpos : 0 < s₀ ^ 2 * (1 + 6 * ε + 18 * ε ^ 2) := by positivity
  have hNhi : N < s₀ ^ 2 * (1 + 6 * ε + 18 * ε ^ 2) := by
    have hsq1 : (τ.re - 1) ^ 2 < (3 * s₀ * ε) ^ 2 := sq_lt_sq.mpr (by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * s₀ * ε), abs_lt]
      exact ⟨h1a, h1b⟩)
    have hsq2 : τ.im ^ 2 < (s₀ + 3 * s₀ * ε) ^ 2 := sq_lt_sq.mpr (by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ s₀ + 3 * s₀ * ε), abs_of_pos τ.im_pos]
      linarith)
    rw [hN]; nlinarith [hsq1, hsq2]
  have hre : (Work.LayerCont.Coinc.coincℂ τ).re = (1 - τ.re) / N := by
    rw [Work.LayerCont.Coinc.coincℂ_re_eq, ← hNdef]
  have him : (Work.LayerCont.Coinc.coincℂ τ).im = τ.im / N := by
    rw [Work.LayerCont.Coinc.coincℂ_im_eq, ← hNdef]
  simp only [Work.Asymptotics.openLeftRectℂ, Set.mem_ofPred_eq]
  rw [hre, him]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the real part: `-ξ₂ < (1-τ.re)/N`
    rw [show (1 - τ.re) / N = -((τ.re - 1) / N) by ring]
    have hkey : (τ.re - 1) / N < ξ₂ := by
      rw [div_lt_iff₀ hNpos]
      have hA : 16 * ε * s₀ * (1 - 3 * ε) ^ 2 < ξ₂ * N := by
        have h1' : 16 * ε * s₀ * (1 - 3 * ε) ^ 2 ≤ ξ₂ * (s₀ ^ 2 * (1 - 3 * ε) ^ 2) := by
          have h := mul_le_mul_of_nonneg_right hεξ (by positivity : (0:ℝ) ≤ s₀ * (1 - 3 * ε) ^ 2)
          nlinarith [h]
        have h2' : ξ₂ * (s₀ ^ 2 * (1 - 3 * ε) ^ 2) < ξ₂ * N := by
          have h := mul_lt_mul_of_pos_left hNlo hξ₂
          nlinarith [h]
        linarith
      nlinarith [hA, h1b, hε8, hs₀, hε]
    linarith
  · -- the real part is negative
    rw [div_neg_iff]
    exact Or.inr ⟨by linarith, hNpos⟩
  · -- the imaginary part: the lower bound `s₀⁻¹ - A₂ < τ.im/N`
    have hstep1 : (s₀ * (1 - 3 * ε)) / (s₀ ^ 2 * (1 + 6 * ε + 18 * ε ^ 2)) < τ.im / N := by
      rw [div_lt_div_iff₀ hDpos hNpos]
      have hmul : (s₀ * (1 - 3 * ε)) * N < (s₀ * (1 - 3 * ε)) * (s₀ ^ 2 * (1 + 6 * ε + 18 * ε ^ 2)) :=
        mul_lt_mul_of_pos_left hNhi hspos
      have hmul2 : (s₀ * (1 - 3 * ε)) * (s₀ ^ 2 * (1 + 6 * ε + 18 * ε ^ 2))
          < τ.im * (s₀ ^ 2 * (1 + 6 * ε + 18 * ε ^ 2)) :=
        mul_lt_mul_of_pos_right hvlo hDpos
      linarith
    have hfrac : (s₀ * (1 - 3 * ε)) / (s₀ ^ 2 * (1 + 6 * ε + 18 * ε ^ 2))
        = (1 - 3 * ε) / (s₀ * (1 + 6 * ε + 18 * ε ^ 2)) := by
      field_simp
    have hstep2 : s₀⁻¹ - A₂ < (1 - 3 * ε) / (s₀ * (1 + 6 * ε + 18 * ε ^ 2)) := by
      have hA₂' : 16 * ε / s₀ ≤ A₂ := by
        rw [div_le_iff₀ hs₀]; linarith [hεA]
      have hle : s₀⁻¹ - A₂ ≤ (1 - 16 * ε) / s₀ := by
        rw [show (1 - 16 * ε) / s₀ = s₀⁻¹ - 16 * ε / s₀ by
          rw [sub_div, one_div]]
        linarith
      have hlt : (1 - 16 * ε) / s₀ < (1 - 3 * ε) / (s₀ * (1 + 6 * ε + 18 * ε ^ 2)) := by
        rw [div_lt_div_iff₀ hs₀ (by positivity : (0 : ℝ) < s₀ * (1 + 6 * ε + 18 * ε ^ 2))]
        nlinarith [hε8, hε, hs₀]
      linarith
    rw [hfrac] at hstep1
    linarith
  · -- the imaginary part: the upper bound `τ.im/N < s₀⁻¹ + A₂`
    have hden : τ.im ^ 2 < N := by
      rw [hN]
      have : 0 < τ.re - 1 := by linarith
      nlinarith
    have hstep1 : τ.im / N < 1 / τ.im := by
      rw [div_lt_div_iff₀ hNpos τ.im_pos]
      nlinarith [hden]
    have hstep2a : 1 / τ.im ≤ 1 / (s₀ * (1 - 3 * ε)) :=
      one_div_le_one_div_of_le hspos hvlo.le
    have hstep2b : 1 / (s₀ * (1 - 3 * ε)) < s₀⁻¹ + A₂ := by
      rw [div_lt_iff₀ hspos]
      have hs₀inv : s₀ * s₀⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hs₀)
      have hmul : (1 + 16 * ε) * (1 - 3 * ε) ≤ (1 + A₂ * s₀) * (1 - 3 * ε) := by
        have h : 1 + 16 * ε ≤ 1 + A₂ * s₀ := by linarith
        exact mul_le_mul_of_nonneg_right h hδpos.le
      have hkey : 1 < (1 + 16 * ε) * (1 - 3 * ε) := by nlinarith [hε8, hε]
      nlinarith [hmul, hkey, hs₀inv]
    linarith

end Work.LayerCont.FarTail
