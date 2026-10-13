import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Stability.Cutoff
import Submission.Work.FTS.EllipticEst.Blocks.DzAgmonDefs
import Submission.Work.FTS.EllipticEst.Blocks.AgmonIBP
import Submission.Work.FTS.EllipticEst.TT.logCutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst

open MeasureTheory Set Filter
open scoped Real Topology ContDiff
open Work.FTS.EllipticEst.Blocks

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ### Elementary AM–GM and integral helpers -/

/-- **Weighted Young inequality**: for `r ≥ 0` and `c > 0`, `2 r |a| |b| ≤ c (r a²) + c⁻¹ (r b²)`.
(This is the completing-of-the-square identity `c x² - 2xy + c⁻¹ y² = c (x - c⁻¹ y)² ≥ 0`
with `x = |a|`, `y = |b|`, multiplied by `r`.) -/
theorem young_weighted (r c a b : ℝ) (hr : 0 ≤ r) (hc : 0 < c) :
    2 * r * |a| * |b| ≤ c * (r * a ^ 2) + c⁻¹ * (r * b ^ 2) := by
  have hexp : c * (|a| - c⁻¹ * |b|) ^ 2 = c * a ^ 2 - 2 * |a| * |b| + c⁻¹ * b ^ 2 := by
    rw [sub_sq, mul_pow, sq_abs a, sq_abs b]
    field_simp
  have hsq : 0 ≤ c * (|a| - c⁻¹ * |b|) ^ 2 := mul_nonneg (le_of_lt hc) (sq_nonneg _)
  rw [hexp] at hsq
  have hmul : 0 ≤ r * (c * a ^ 2 - 2 * |a| * |b| + c⁻¹ * b ^ 2) := mul_nonneg hr hsq
  have heq : r * (c * a ^ 2 - 2 * |a| * |b| + c⁻¹ * b ^ 2)
      = c * (r * a ^ 2) + c⁻¹ * (r * b ^ 2) - 2 * r * |a| * |b| := by ring
  linarith [hmul, heq ▸ hmul]

/-- The `1/8`-instance of Young's inequality: `2 r |a| |b| ≤ (1/8) (r a²) + 8 (r b²)`. -/
theorem young_eighth (r a b : ℝ) (hr : 0 ≤ r) :
    2 * r * |a| * |b| ≤ (1 / 8) * (r * a ^ 2) + 8 * (r * b ^ 2) := by
  have h := young_weighted r (1 / 8) a b hr (by norm_num)
  rw [show ((1 : ℝ) / 8)⁻¹ = 8 by norm_num] at h
  linarith [h]

/-- Completing of the square in the form used for the `(zχ')`-pairing:
`(1/4) (r x |y|) ≤ (1/64) (r x²) + r y²` for `r ≥ 0` (from `(x/8 - |y|)² ≥ 0`). -/
theorem young_quarter (r x y : ℝ) (hr : 0 ≤ r) :
    (1 / 4) * (r * x * |y|) ≤ (1 / 64) * (r * x ^ 2) + r * y ^ 2 := by
  have hexp : (x / 8 - |y|) ^ 2 = x ^ 2 / 64 - x * |y| / 4 + |y| ^ 2 := by ring
  have hsq : 0 ≤ (x / 8 - |y|) ^ 2 := sq_nonneg _
  rw [hexp, sq_abs y] at hsq
  have hmul : 0 ≤ r * (x ^ 2 / 64 - x * |y| / 4 + y ^ 2) := mul_nonneg hr hsq
  have heq : r * (x ^ 2 / 64 - x * |y| / 4 + y ^ 2)
      = (1 / 64) * (r * x ^ 2) + r * y ^ 2 - (1 / 4) * (r * x * |y|) := by ring
  linarith [hmul, heq ▸ hmul]

/-- The integral of a four-term linear combination over `(0,∞)`. -/
theorem integral_lin4 {f₁ f₂ f₃ f₄ : ℝ → ℝ} {c₁ c₂ c₃ c₄ : ℝ}
    (h₁ : IntegrableOn f₁ (Set.Ioi (0 : ℝ))) (h₂ : IntegrableOn f₂ (Set.Ioi (0 : ℝ)))
    (h₃ : IntegrableOn f₃ (Set.Ioi (0 : ℝ))) (h₄ : IntegrableOn f₄ (Set.Ioi (0 : ℝ))) :
    (∫ z in Set.Ioi (0 : ℝ), (c₁ * f₁ z + c₂ * f₂ z + c₃ * f₃ z + c₄ * f₄ z))
      = c₁ * (∫ z in Set.Ioi (0 : ℝ), f₁ z) + c₂ * (∫ z in Set.Ioi (0 : ℝ), f₂ z)
        + c₃ * (∫ z in Set.Ioi (0 : ℝ), f₃ z) + c₄ * (∫ z in Set.Ioi (0 : ℝ), f₄ z) := by
  have h12 : IntegrableOn (fun z : ℝ => c₁ * f₁ z + c₂ * f₂ z) (Set.Ioi (0 : ℝ)) :=
    (h₁.const_mul c₁).add (h₂.const_mul c₂)
  have h123 : IntegrableOn (fun z : ℝ => c₁ * f₁ z + c₂ * f₂ z + c₃ * f₃ z) (Set.Ioi (0 : ℝ)) :=
    h12.add (h₃.const_mul c₃)
  rw [integral_add (f := fun z : ℝ => c₁ * f₁ z + c₂ * f₂ z + c₃ * f₃ z)
        (g := fun z : ℝ => c₄ * f₄ z) h123 (h₄.const_mul c₄),
      integral_add (f := fun z : ℝ => c₁ * f₁ z + c₂ * f₂ z) (g := fun z : ℝ => c₃ * f₃ z)
        h12 (h₃.const_mul c₃),
      integral_add (f := fun z : ℝ => c₁ * f₁ z) (g := fun z : ℝ => c₂ * f₂ z)
        (h₁.const_mul c₁) (h₂.const_mul c₂),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-! ### The pointwise core -/

/-- **The pointwise AM–GM core of the cut-off weighted Agmon estimate** (with `ρ = W2`).

For `z > 0`, `0 < α`, `0 ≤ δ`, `h, χ` of class `C^∞` on `(0,∞)`, `0 ≤ χ z ≤ 1`,
`|z χ'(z)| ≤ 1/8` and `|z² χ''(z)| ≤ δ`,

`-(d/dz)(ρ z² (hχ)')(z) · (hχ)(z) ≤ (9/64) ρ (zh')² χ² + (α²/4) ρ (z²h'')² χ²
   + (α⁻² + 8) ρ h² χ² + (5/4 + δ) ρ h²`   (all values at `z`).

Route: `|(d/dz)(ρz²g')| ≤ 2ρz|g'| + ρz²|g''|` with `g = hχ`, `|g'| ≤ |h'|χ + |h||χ'|`,
`|g''| ≤ |h''|χ + 2|h'||χ'| + |h||χ''|`, then the AM–GM pairings
`2ρz|h'||h|χ² ≤ (1/8)ρ(zh')²χ² + 8ρh²χ²`, `2ρz|h|²|χ'|χ ≤ (1/4)ρh²`,
`ρz²|h''||h|χ² ≤ (α²/4)ρ(z²h'')²χ² + α⁻²ρh²χ²`,
`2ρz²|h'||χ'||h|χ ≤ (1/64)ρ(zh')²χ² + ρh²`, `ρz²|h|²|χ''|χ ≤ δρh²`. -/
theorem agmon_pointwise {χ : ℝ → ℝ} {α δ : ℝ} {h : ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) (hα : 0 < α) (hδ0 : 0 ≤ δ)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)))
    (hχcd : ContDiffOn ℝ Work.Stability.smoothOrder χ (Set.Ioi (0 : ℝ)))
    (hχ0 : 0 ≤ χ z) (hχ1 : χ z ≤ 1)
    (hχder1 : |z * deriv χ z| ≤ 1 / 8)
    (hχder2 : |z ^ 2 * deriv (deriv χ) z| ≤ δ) :
    -(deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z * (h z * χ z))
      ≤ (9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
        + (5 / 4 + δ) * (W2 z * h z ^ 2) := by
  have hne : Work.Stability.smoothOrder ≠ 0 := by simp [Work.Stability.smoothOrder]
  have hder : Work.Stability.smoothOrder + 1 ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hρ : 0 ≤ W2 z := W2_nonneg z
  have hA : 0 ≤ W2 z * h z ^ 2 := mul_nonneg hρ (sq_nonneg _)
  -- differentiability of the data at `z`
  have hh_at : DifferentiableAt ℝ h z :=
    (hcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hχ_at : DifferentiableAt ℝ χ z :=
    (hχcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdh_cd : ContDiffOn ℝ Work.Stability.smoothOrder (deriv h) (Set.Ioi (0 : ℝ)) :=
    hcd.deriv_of_isOpen isOpen_Ioi hder
  have hdχ_cd : ContDiffOn ℝ Work.Stability.smoothOrder (deriv χ) (Set.Ioi (0 : ℝ)) :=
    hχcd.deriv_of_isOpen isOpen_Ioi hder
  have hdh_at : DifferentiableAt ℝ (deriv h) z :=
    (hdh_cd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdχ_at : DifferentiableAt ℝ (deriv χ) z :=
    (hdχ_cd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hgcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun y : ℝ => h y * χ y) (Set.Ioi (0 : ℝ)) :=
    hcd.mul hχcd
  have hdg_cd : ContDiffOn ℝ Work.Stability.smoothOrder
      (deriv (fun y : ℝ => h y * χ y)) (Set.Ioi (0 : ℝ)) :=
    hgcd.deriv_of_isOpen isOpen_Ioi hder
  have hdg_at : DifferentiableAt ℝ (deriv (fun y : ℝ => h y * χ y)) z :=
    (hdg_cd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hW2sq_cd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun y : ℝ => W2 y * y ^ 2) (Set.Ioi (0 : ℝ)) :=
    (W2_contDiffOn.of_le le_top).mul (contDiffOn_id.pow 2)
  have hW2sq_at : DifferentiableAt ℝ (fun y : ℝ => W2 y * y ^ 2) z :=
    (hW2sq_cd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  -- first and second derivatives of `g = h χ`
  have hg1 : deriv (fun y : ℝ => h y * χ y) z = deriv h z * χ z + h z * deriv χ z := by
    rw [show (fun y : ℝ => h y * χ y) = h * χ from rfl, deriv_mul hh_at hχ_at]
  have hg2 : deriv (deriv (fun y : ℝ => h y * χ y)) z
      = deriv (deriv h) z * χ z + 2 * deriv h z * deriv χ z + h z * deriv (deriv χ) z := by
    have heq : deriv (h * χ) =ᶠ[𝓝 z] fun y => deriv h y * χ y + h y * deriv χ y := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      rw [deriv_mul]
      · exact (hcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hy)
      · exact (hχcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hy)
    have h1 : (fun y : ℝ => h y * χ y) = h * χ := rfl
    rw [h1, heq.deriv_eq]
    rw [show (fun y : ℝ => deriv h y * χ y + h y * deriv χ y) = deriv h * χ + h * deriv χ from rfl,
      deriv_add (hdh_at.mul hχ_at) (hh_at.mul hdχ_at),
      deriv_mul hdh_at hχ_at, deriv_mul hh_at hdχ_at]
    ring
  -- bounds on `|g'|` and `|g''|`
  have hG1 : |deriv (fun y : ℝ => h y * χ y) z| ≤ |deriv h z| * χ z + |h z| * |deriv χ z| := by
    rw [hg1]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hχ0]
  have hG2 : |deriv (deriv (fun y : ℝ => h y * χ y)) z|
      ≤ |deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z| + |h z| * |deriv (deriv χ) z| := by
    rw [hg2]
    have h1 : |deriv (deriv h) z * χ z + 2 * deriv h z * deriv χ z|
        ≤ |deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hχ0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : |h z * deriv (deriv χ) z| = |h z| * |deriv (deriv χ) z| := abs_mul _ _
    calc |deriv (deriv h) z * χ z + 2 * deriv h z * deriv χ z + h z * deriv (deriv χ) z|
        ≤ |deriv (deriv h) z * χ z + 2 * deriv h z * deriv χ z| + |h z * deriv (deriv χ) z| :=
          abs_add_le _ _
      _ ≤ (|deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z|)
            + |h z| * |deriv (deriv χ) z| := by
          rw [h2]; linarith [h1]
  -- the derivative of `ρ z² g'`
  have hD_id : deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z
      = deriv (fun y : ℝ => W2 y * y ^ 2) z * deriv (fun y : ℝ => h y * χ y) z
        + (W2 z * z ^ 2) * deriv (deriv (fun y : ℝ => h y * χ y)) z := by
    have hsplit : deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z
        = deriv (fun y : ℝ => W2 y * y ^ 2) z * deriv (fun y : ℝ => h y * χ y) z
          + (fun y : ℝ => W2 y * y ^ 2) z * deriv (deriv (fun y : ℝ => h y * χ y)) z := by
      rw [show (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y)
          = (fun y : ℝ => W2 y * y ^ 2) * deriv (fun y : ℝ => h y * χ y) from rfl,
        deriv_mul hW2sq_at hdg_at]
    have hbeta : (fun y : ℝ => W2 y * y ^ 2) z = W2 z * z ^ 2 := rfl
    rw [hsplit, hbeta]
  have hD_abs : |deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z|
      ≤ 2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
        + W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := by
    rw [hD_id]
    have h1 := abs_deriv_W2_mul_sq_le (z := z) hz
    have h2 : |deriv (fun y : ℝ => W2 y * y ^ 2) z * deriv (fun y : ℝ => h y * χ y) z
          + (W2 z * z ^ 2) * deriv (deriv (fun y : ℝ => h y * χ y)) z|
        ≤ |deriv (fun y : ℝ => W2 y * y ^ 2) z| * |deriv (fun y : ℝ => h y * χ y) z|
          + (W2 z * z ^ 2) * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hρ (sq_nonneg z))]
    have h3 : 2 / z * (W2 z * z ^ 2) = 2 * W2 z * z := by
      field_simp
    calc |deriv (fun y : ℝ => W2 y * y ^ 2) z * deriv (fun y : ℝ => h y * χ y) z
            + (W2 z * z ^ 2) * deriv (deriv (fun y : ℝ => h y * χ y)) z|
        ≤ |deriv (fun y : ℝ => W2 y * y ^ 2) z| * |deriv (fun y : ℝ => h y * χ y) z|
            + (W2 z * z ^ 2) * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := h2
      _ ≤ (2 / z * (W2 z * z ^ 2)) * |deriv (fun y : ℝ => h y * χ y) z|
            + (W2 z * z ^ 2) * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := by
          have h4 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (deriv (fun y : ℝ => h y * χ y) z))
          linarith [h4]
      _ = 2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
            + W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := by
          rw [h3]
  -- the five AM–GM pairings
  have hb1 : 2 * W2 z * z * |deriv h z| * |h z| * χ z ^ 2
      ≤ (1 / 8) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + 8 * (W2 z * h z ^ 2 * χ z ^ 2) := by
    have h := young_eighth (W2 z * χ z ^ 2) (z * deriv h z) (h z)
      (mul_nonneg hρ (sq_nonneg _))
    rw [abs_mul, abs_of_pos hz] at h
    linarith [h]
  have hb2 : 2 * W2 z * z * |h z| * |deriv χ z| * |h z| * χ z ≤ (1 / 4) * (W2 z * h z ^ 2) := by
    have habs : |z * deriv χ z| = z * |deriv χ z| := by rw [abs_mul, abs_of_pos hz]
    have hsq : |h z| * |h z| = h z ^ 2 := by rw [← sq_abs (h z)]; ring
    have hstep : 2 * z * |deriv χ z| ≤ 1 / 4 := by linarith [hχder1, habs]
    have hpos : 0 ≤ W2 z * (|h z| * |h z|) * χ z :=
      mul_nonneg (mul_nonneg hρ (mul_nonneg (abs_nonneg _) (abs_nonneg _))) hχ0
    calc 2 * W2 z * z * |h z| * |deriv χ z| * |h z| * χ z
        = (2 * z * |deriv χ z|) * (W2 z * (|h z| * |h z|) * χ z) := by ring
      _ ≤ (1 / 4) * (W2 z * (|h z| * |h z|) * χ z) := mul_le_mul_of_nonneg_right hstep hpos
      _ ≤ (1 / 4) * (W2 z * h z ^ 2) := by
          have hle : W2 z * (|h z| * |h z|) * χ z ≤ W2 z * h z ^ 2 := by
            rw [hsq]
            nlinarith [hA, hχ0, hχ1]
          linarith [hle]
  have hb3 : W2 z * z ^ 2 * |deriv (deriv h) z| * |h z| * χ z ^ 2
      ≤ (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        + (α ^ 2)⁻¹ * (W2 z * h z ^ 2 * χ z ^ 2) := by
    have h := young_weighted (W2 z * χ z ^ 2) (α ^ 2 / 2) (z ^ 2 * deriv (deriv h) z) (h z)
      (mul_nonneg hρ (sq_nonneg _)) (by positivity)
    rw [abs_mul, abs_of_nonneg (sq_nonneg z),
      show ((α ^ 2 / 2))⁻¹ = 2 * (α ^ 2)⁻¹ by field_simp] at h
    linarith [h]
  have hb4 : 2 * W2 z * z ^ 2 * |deriv h z| * |deriv χ z| * |h z| * χ z
      ≤ (1 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2) + W2 z * h z ^ 2 := by
    have he : 2 * W2 z * z ^ 2 * |deriv h z| * |deriv χ z| * |h z| * χ z
        = 2 * |z * deriv χ z| * (W2 z * (z * |deriv h z| * χ z) * |h z|) := by
      rw [abs_mul, abs_of_pos hz]; ring
    rw [he]
    have hstep : 2 * |z * deriv χ z| ≤ 1 / 4 := by linarith [hχder1]
    have hq := young_quarter (W2 z) (z * |deriv h z| * χ z) (h z) hρ
    rw [show (z * |deriv h z| * χ z) ^ 2 = (z * deriv h z) ^ 2 * χ z ^ 2 by
      rw [mul_pow, mul_pow, sq_abs]; ring] at hq
    have hpos : 0 ≤ W2 z * (z * |deriv h z| * χ z) * |h z| :=
      mul_nonneg (mul_nonneg hρ (mul_nonneg (mul_nonneg hz.le (abs_nonneg _)) hχ0))
        (abs_nonneg _)
    have hstep2 : 2 * |z * deriv χ z| * (W2 z * (z * |deriv h z| * χ z) * |h z|)
        ≤ (1 / 4) * (W2 z * (z * |deriv h z| * χ z) * |h z|) :=
      mul_le_mul_of_nonneg_right hstep hpos
    linarith [hstep2, hq]
  have hb5 : W2 z * z ^ 2 * |h z| * |deriv (deriv χ) z| * |h z| * χ z
      ≤ δ * (W2 z * h z ^ 2) := by
    have habs : |z ^ 2 * deriv (deriv χ) z| = z ^ 2 * |deriv (deriv χ) z| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg z)]
    have hsq : |h z| * |h z| = h z ^ 2 := by rw [← sq_abs (h z)]; ring
    have hstep : z ^ 2 * |deriv (deriv χ) z| ≤ δ := by linarith [hχder2, habs]
    have hpos : 0 ≤ W2 z * (|h z| * |h z|) * χ z :=
      mul_nonneg (mul_nonneg hρ (mul_nonneg (abs_nonneg _) (abs_nonneg _))) hχ0
    calc W2 z * z ^ 2 * |h z| * |deriv (deriv χ) z| * |h z| * χ z
        = (z ^ 2 * |deriv (deriv χ) z|) * (W2 z * (|h z| * |h z|) * χ z) := by ring
      _ ≤ δ * (W2 z * (|h z| * |h z|) * χ z) := mul_le_mul_of_nonneg_right hstep hpos
      _ ≤ δ * (W2 z * h z ^ 2) := by
          have hle : W2 z * (|h z| * |h z|) * χ z ≤ W2 z * h z ^ 2 := by
            rw [hsq]
            nlinarith [hA, hχ0, hχ1]
          exact mul_le_mul_of_nonneg_left hle hδ0
  -- assemble
  have hstep1 : -(deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z
        * (h z * χ z))
      ≤ |deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z|
        * (|h z| * χ z) := by
    refine (neg_le_abs _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hχ0]
  have hstep2 : |deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z|
        * (|h z| * χ z)
      ≤ (2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
          + W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z|) * (|h z| * χ z) :=
    mul_le_mul_of_nonneg_right hD_abs (mul_nonneg (abs_nonneg _) hχ0)
  have hstep3 : (2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
          + W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z|) * (|h z| * χ z)
      ≤ (2 * W2 z * z * (|deriv h z| * χ z + |h z| * |deriv χ z|)
          + W2 z * z ^ 2 * (|deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z|
              + |h z| * |deriv (deriv χ) z|)) * (|h z| * χ z) := by
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (abs_nonneg _) hχ0)
    have hA1 : 2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
        ≤ 2 * W2 z * z * (|deriv h z| * χ z + |h z| * |deriv χ z|) :=
      mul_le_mul_of_nonneg_left hG1 (by positivity)
    have hA2 : W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z|
        ≤ W2 z * z ^ 2 * (|deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z|
            + |h z| * |deriv (deriv χ) z|) :=
      mul_le_mul_of_nonneg_left hG2 (by positivity)
    linarith [hA1, hA2]
  have hstep4 : (2 * W2 z * z * (|deriv h z| * χ z + |h z| * |deriv χ z|)
          + W2 z * z ^ 2 * (|deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z|
              + |h z| * |deriv (deriv χ) z|)) * (|h z| * χ z)
      = 2 * W2 z * z * |deriv h z| * |h z| * χ z ^ 2
        + 2 * W2 z * z * |h z| * |deriv χ z| * |h z| * χ z
        + (W2 z * z ^ 2 * |deriv (deriv h) z| * |h z| * χ z ^ 2
          + 2 * W2 z * z ^ 2 * |deriv h z| * |deriv χ z| * |h z| * χ z
          + W2 z * z ^ 2 * |h z| * |deriv (deriv χ) z| * |h z| * χ z) := by
    ring
  linarith [hstep1, hstep2, hstep3, hstep4, hb1, hb2, hb3, hb4, hb5]

/-! ### The arithmetic core -/

/-- **Pure arithmetic core of the cut-off Agmon estimate.**  If `0 < α ≤ 1`, `δ ≤ 1`, all of
`Ag, X, p, q` are nonnegative and
`X ≤ 2 Ag + p/32`,  `Ag ≤ (9/64) X + (α²/4) q + (α⁻² + 12 + δ) p`,
then `α² X ≤ 100 (p + α⁴ q)`.  (Substituting the first inequality into the second gives
`(23/32) Ag ≤ (9/2048 + α⁻² + 12 + δ) p + (α²/4) q`, whence
`α² X ≤ (16/23) α⁴ q + (32/23)(2 + 27α²) p ≤ 39 (p + α⁴ q)`.) -/
theorem agmon_arith {α δ Ag X p q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hδ1 : δ ≤ 1)
    (hAg : 0 ≤ Ag) (hX : 0 ≤ X) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : X ≤ 2 * Ag + p / 32)
    (h2 : Ag ≤ (9 / 64) * X + (α ^ 2 / 4) * q + ((α ^ 2)⁻¹ + 12 + δ) * p) :
    α ^ 2 * X ≤ 100 * (p + α ^ 4 * q) := by
  have hα2pos : 0 < α ^ 2 := pow_pos hα 2
  have hα2le : α ^ 2 ≤ 1 := by nlinarith
  have hα2ne : α ^ 2 ≠ 0 := ne_of_gt hα2pos
  have hα4nn : 0 ≤ α ^ 4 := by positivity
  -- multiply `h2` by `α²`
  have h2α : α ^ 2 * Ag ≤ (9 / 64) * (α ^ 2 * X) + (α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p := by
    have h := mul_le_mul_of_nonneg_left h2 (le_of_lt hα2pos)
    have he : α ^ 2 * ((9 / 64) * X + (α ^ 2 / 4) * q + ((α ^ 2)⁻¹ + 12 + δ) * p)
        = (9 / 64) * (α ^ 2 * X) + (α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p := by
      field_simp
      ring
    rw [he] at h
    exact h
  -- multiply `h1` by `α²`
  have h1α : α ^ 2 * X ≤ 2 * (α ^ 2 * Ag) + (α ^ 2 * p) / 32 := by
    have h := mul_le_mul_of_nonneg_left h1 (le_of_lt hα2pos)
    have he : α ^ 2 * (2 * Ag + p / 32) = 2 * (α ^ 2 * Ag) + (α ^ 2 * p) / 32 := by ring
    rw [he] at h
    exact h
  have hstep : (1 - 2 * (9 / 64)) * (α ^ 2 * X)
      ≤ 2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32 := by
    nlinarith [h1α, h2α]
  have hstep2 : α ^ 2 * X
      ≤ (32 / 23) * (2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32) := by
    have hpos : (0 : ℝ) < 1 - 2 * (9 / 64) := by norm_num
    have h2' : α ^ 2 * X * (1 - 2 * (9 / 64))
        ≤ 2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32 := by
      rw [mul_comm]
      exact hstep
    have h := (le_div_iff₀ hpos).mpr h2'
    have he : (32 / 23 : ℝ) = (1 - 2 * (9 / 64))⁻¹ := by norm_num
    rw [he]
    rw [div_eq_inv_mul] at h
    exact h
  have hb : 2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32
      ≤ (23 / 32) * (100 * (p + α ^ 4 * q)) := by
    nlinarith [hα1, hδ1, hp, hq, hα2le, hα4nn, mul_nonneg hα4nn hq, mul_nonneg (sq_nonneg α) hp,
      mul_nonneg (sq_nonneg α) (mul_nonneg (le_of_lt hα) hp)]
  calc α ^ 2 * X
      ≤ (32 / 23) * (2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32) := hstep2
    _ ≤ (32 / 23) * ((23 / 32) * (100 * (p + α ^ 4 * q))) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 100 * (p + α ^ 4 * q) := by ring

/-! ### The cut-off weighted Agmon estimate -/

/-- **The cut-off form of the weighted Agmon estimate**: for a smooth cut-off `χ` with `0 ≤ χ ≤ 1`,
`|z χ'| ≤ 1/8`, `|z² χ''| ≤ δ ≤ 1` and compact support in `(0,∞)`, and for `C^∞` data `h` on
`(0,∞)` with `∫ ρ h² < ∞` and `∫ ρ (z²h'')² < ∞` (`ρ = W2 z = (w z)^2`),

`α² ∫ ρ (zh')² χ² ≤ 100 (∫ ρ h² + α⁴ ∫ ρ (z²h'')²)`,  for `0 < α ≤ 1`.

This is Piece 2 of `Submission/Work/EllipticEst/NOTES_AgmonCutoff.md`; read that file for the
derivation (integration by parts for the compactly supported `h·χ`, then the pointwise AM–GM
pairings — the `zχ'` terms are paired with `h·χ`, never with a second `zh'`).  All integrals are
honest Bochner integrals over `(0,∞)`. -/
theorem agmon_cutoff_estimate (χ : ℝ → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hχcd : ContDiffOn ℝ Work.Stability.smoothOrder χ (Set.Ioi (0 : ℝ)))
    (hχ0 : ∀ z : ℝ, 0 ≤ χ z) (hχ1 : ∀ z : ℝ, χ z ≤ 1)
    (hχder1 : ∀ z : ℝ, 0 < z → |z * deriv χ z| ≤ 1 / 8)
    (hχder2 : ∀ z : ℝ, 0 < z → |z ^ 2 * deriv (deriv χ) z| ≤ δ)
    (hsupp : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ z : ℝ, z ∉ Set.Icc a b → χ z = 0)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)))
    (hp : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.EllipticEst.Blocks.W2 z * h z ^ 2) (Set.Ioi (0 : ℝ)))
    (hq : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.EllipticEst.Blocks.W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2)
      (Set.Ioi (0 : ℝ))) :
    α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
        Work.FTS.EllipticEst.Blocks.W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
      ≤ 100 * ((∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.Blocks.W2 z * h z ^ 2)
          + α ^ 4 * (∫ z in Set.Ioi (0 : ℝ),
              Work.FTS.EllipticEst.Blocks.W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2)) := by
  obtain ⟨a, b, ha, hab, hsuppχ⟩ := hsupp
  have hne : Work.Stability.smoothOrder ≠ 0 := by simp [Work.Stability.smoothOrder]
  have hder : Work.Stability.smoothOrder + 1 ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => by
    simp only [Set.mem_Ioi]; linarith [hz.1, ha]
  -- the compactly supported function `g = h χ`
  have hgsupp : ∀ z : ℝ, z ∉ Set.Icc a b → (fun y : ℝ => h y * χ y) z = 0 := by
    intro z hz; simp [hsuppχ z hz]
  have hgcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun y : ℝ => h y * χ y) (Set.Ioi (0 : ℝ)) :=
    hcd.mul hχcd
  -- integration by parts
  have hibp : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
      = -∫ z in Set.Ioi (0 : ℝ),
          deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z
            * (h z * χ z) :=
    AgmonIBP (h := fun y : ℝ => h y * χ y) (a := a) (b := b) ha hgsupp hgcd
  -- off the support, `g` is locally zero, so is its derivative
  have hderivg_zero : ∀ z : ℝ, z ∉ Set.Icc a b → deriv (fun y : ℝ => h y * χ y) z = 0 := by
    intro z hz
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    rcases hz' with hlt | hgt
    · have hev : (fun y : ℝ => h y * χ y) =ᶠ[𝓝 z] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
        simp [hsuppχ y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)]
      rw [hev.deriv_eq]; simp
    · have hev : (fun y : ℝ => h y * χ y) =ᶠ[𝓝 z] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
        simp [hsuppχ y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)]
      rw [hev.deriv_eq]; simp
  -- continuity facts on `[a,b]`
  have hcontW2 : ContinuousOn W2 (Set.Icc a b) := W2_contDiffOn.continuousOn.mono hsub
  have hcont_h : ContinuousOn h (Set.Icc a b) := hcd.continuousOn.mono hsub
  have hcont_chi : ContinuousOn χ (Set.Icc a b) := hχcd.continuousOn.mono hsub
  have hcont_dh : ContinuousOn (deriv h) (Set.Icc a b) :=
    (hcd.deriv_of_isOpen isOpen_Ioi hder).continuousOn.mono hsub
  have hcont_ddh : ContinuousOn (deriv (deriv h)) (Set.Icc a b) :=
    ((hcd.deriv_of_isOpen isOpen_Ioi hder).deriv_of_isOpen isOpen_Ioi hder).continuousOn.mono hsub
  have hcont_g : ContinuousOn (fun y : ℝ => h y * χ y) (Set.Icc a b) :=
    hcont_h.mul hcont_chi
  have hcont_dg : ContinuousOn (deriv (fun y : ℝ => h y * χ y)) (Set.Icc a b) :=
    (hgcd.deriv_of_isOpen isOpen_Ioi hder).continuousOn.mono hsub
  have hU_cd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) (Set.Ioi (0 : ℝ)) :=
    ((W2_contDiffOn.of_le le_top).mul (contDiffOn_id.pow 2)).mul
      (hgcd.deriv_of_isOpen isOpen_Ioi hder)
  have hcont_dU : ContinuousOn
      (deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y)) (Set.Icc a b) :=
    ((hU_cd.of_le (by simp [Work.Stability.smoothOrder])).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).mono hsub
  -- integrability of the pieces
  have hInt_Ag : IntegrableOn
      (fun z : ℝ => W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact hcontW2.mul ((continuousOn_id.mul hcont_dg).pow 2)
    · intro z hz
      rw [hderivg_zero z hz]; ring
  have hInt_X : IntegrableOn (fun z : ℝ => W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact (hcontW2.mul ((continuousOn_id.mul hcont_dh).pow 2)).mul (hcont_chi.pow 2)
    · intro z hz
      rw [hsuppχ z hz]; ring
  have hInt_Q : IntegrableOn
      (fun z : ℝ => W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact (hcontW2.mul (((continuousOn_id.pow 2).mul hcont_ddh).pow 2)).mul (hcont_chi.pow 2)
    · intro z hz
      rw [hsuppχ z hz]; ring
  have hInt_P : IntegrableOn (fun z : ℝ => W2 z * h z ^ 2 * χ z ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact (hcontW2.mul (hcont_h.pow 2)).mul (hcont_chi.pow 2)
    · intro z hz
      rw [hsuppχ z hz]; ring
  have hInt_DU : IntegrableOn (fun z : ℝ =>
      deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z * (h z * χ z))
      (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact hcont_dU.mul hcont_g
    · intro z hz
      rw [hsuppχ z hz]; ring
  -- pointwise bound at every `z > 0`
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      -(deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z * (h z * χ z))
        ≤ (9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
          + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
          + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
          + (5 / 4 + δ) * (W2 z * h z ^ 2) :=
    fun z hz => agmon_pointwise hz hα hδ0 hcd hχcd (hχ0 z) (hχ1 z) (hχder1 z hz) (hχder2 z hz)
  -- integrability of the pointwise upper bound
  have hInt_rhs : IntegrableOn (fun z : ℝ =>
      (9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
        + (5 / 4 + δ) * (W2 z * h z ^ 2)) (Set.Ioi (0 : ℝ)) :=
    (((hInt_X.const_mul (9 / 64)).add (hInt_Q.const_mul (α ^ 2 / 4))).add
      (hInt_P.const_mul ((α ^ 2)⁻¹ + 8))).add (hp.const_mul (5 / 4 + δ))
  -- the Agmon integral is bounded by the integral of the pointwise bound
  have hAg_le : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ),
          ((9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
            + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
            + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
            + (5 / 4 + δ) * (W2 z * h z ^ 2)) := by
    rw [hibp, ← integral_neg]
    exact integral_mono_ae hInt_DU.neg hInt_rhs (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hpt z hz)
  -- split the integral of the pointwise bound
  have hsplit : (∫ z in Set.Ioi (0 : ℝ),
        ((9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
          + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
          + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
          + (5 / 4 + δ) * (W2 z * h z ^ 2)))
      = (9 / 64) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + (α ^ 2 / 4) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        + ((α ^ 2)⁻¹ + 8) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 * χ z ^ 2)
        + (5 / 4 + δ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) :=
    integral_lin4 hInt_X hInt_Q hInt_P hp
  -- `X ≤ 2 Ag + p/32`
  have hptX : ∀ z ∈ Set.Ioi (0 : ℝ),
      W2 z * (z * deriv h z) ^ 2 * χ z ^ 2
        ≤ 2 * (W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
          + (1 / 32) * (W2 z * h z ^ 2) := by
    intro z hz
    have hρ : 0 ≤ W2 z := W2_nonneg z
    have hz2 : 2 * (z * deriv χ z) ^ 2 ≤ 1 / 32 := by
      have h1 : (z * deriv χ z) ^ 2 ≤ 1 / 64 := by
        calc (z * deriv χ z) ^ 2 = |z * deriv χ z| ^ 2 := (sq_abs _).symm
          _ ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hχder1 z hz) 2
          _ = 1 / 64 := by norm_num
      linarith
    have hdiff : deriv (fun y : ℝ => h y * χ y) z - deriv h z * χ z = h z * deriv χ z := by
      have hh_at : DifferentiableAt ℝ h z :=
        (hcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hχ_at : DifferentiableAt ℝ χ z :=
        (hχcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
      rw [show (fun y : ℝ => h y * χ y) = h * χ from rfl, deriv_mul hh_at hχ_at]
      ring
    have heq : z * deriv h z * χ z
        = z * deriv (fun y : ℝ => h y * χ y) z - z * h z * deriv χ z := by
      have h2 := congrArg (fun t : ℝ => z * t) hdiff
      rw [mul_sub] at h2
      linarith [h2]
    have hkey : (z * deriv h z * χ z) ^ 2
        ≤ 2 * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2 + 2 * (z * h z * deriv χ z) ^ 2 := by
      have hsq : 0 ≤ (z * deriv (fun y : ℝ => h y * χ y) z + z * h z * deriv χ z) ^ 2 :=
        sq_nonneg _
      rw [heq]
      nlinarith [hsq]
    have h1 : W2 z * (z * deriv h z) ^ 2 * χ z ^ 2
        = W2 z * (z * deriv h z * χ z) ^ 2 := by ring
    rw [h1]
    have h2 : W2 z * (z * deriv h z * χ z) ^ 2
        ≤ W2 z * (2 * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2
            + 2 * (z * h z * deriv χ z) ^ 2) := mul_le_mul_of_nonneg_left hkey hρ
    have h3 : W2 z * (2 * (z * h z * deriv χ z) ^ 2)
        = (2 * (z * deriv χ z) ^ 2) * (W2 z * h z ^ 2) := by ring
    have h4 : 0 ≤ W2 z * h z ^ 2 := mul_nonneg hρ (sq_nonneg _)
    have h5 : (2 * (z * deriv χ z) ^ 2) * (W2 z * h z ^ 2) ≤ (1 / 32) * (W2 z * h z ^ 2) :=
      mul_le_mul_of_nonneg_right hz2 h4
    linarith [h2, h3, h5]
  have hX_le : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
      ≤ 2 * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
        + (1 / 32) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) := by
    have hInt_rhs2 : IntegrableOn (fun z : ℝ =>
        2 * (W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
          + (1 / 32) * (W2 z * h z ^ 2)) (Set.Ioi (0 : ℝ)) :=
      (hInt_Ag.const_mul 2).add (hp.const_mul (1 / 32))
    have hmono := integral_mono_ae hInt_X hInt_rhs2 (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hptX z hz)
    rw [integral_add (f := fun z : ℝ => 2 * (W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2))
        (g := fun z : ℝ => (1 / 32) * (W2 z * h z ^ 2)) (hInt_Ag.const_mul 2) (hp.const_mul (1 / 32)),
      integral_const_mul, integral_const_mul] at hmono
    exact hmono
  -- `P ≤ p`, `Q ≤ q`
  have hP_le : (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 * χ z ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 := by
    refine integral_mono_ae hInt_P hp ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have hc : χ z ^ 2 ≤ 1 := by nlinarith [hχ0 z, hχ1 z]
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg (W2_nonneg z) (sq_nonneg (h z)))
    linarith [this]
  have hQ_le : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 := by
    refine integral_mono_ae hInt_Q hq ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have hc : χ z ^ 2 ≤ 1 := by nlinarith [hχ0 z, hχ1 z]
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg (W2_nonneg z) (sq_nonneg (z ^ 2 * deriv (deriv h) z)))
    linarith [this]
  -- nonnegativity
  have hX_nn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2 :=
    integral_nonneg fun z => mul_nonneg (mul_nonneg (W2_nonneg z) (sq_nonneg _)) (sq_nonneg _)
  have hAg_nn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2 :=
    integral_nonneg fun z => mul_nonneg (W2_nonneg z) (sq_nonneg _)
  have hp_nn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 :=
    integral_nonneg fun z => mul_nonneg (W2_nonneg z) (sq_nonneg _)
  have hq_nn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 :=
    integral_nonneg fun z => mul_nonneg (W2_nonneg z) (sq_nonneg _)
  -- final arithmetic
  have hmain : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
      ≤ (9 / 64) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + (α ^ 2 / 4) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2)
        + ((α ^ 2)⁻¹ + 12 + δ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) := by
    rw [hsplit] at hAg_le
    have hQ' : (α ^ 2 / 4) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        ≤ (α ^ 2 / 4) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2) :=
      mul_le_mul_of_nonneg_left hQ_le (by positivity)
    have hP' : ((α ^ 2)⁻¹ + 8) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 * χ z ^ 2)
        ≤ ((α ^ 2)⁻¹ + 8) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) :=
      mul_le_mul_of_nonneg_left hP_le (by positivity)
    have hb : ((α ^ 2)⁻¹ + 8) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2)
          + (5 / 4 + δ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2)
        ≤ ((α ^ 2)⁻¹ + 12 + δ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) := by
      have h := hp_nn
      nlinarith [hp_nn]
    linarith [hAg_le, hQ', hP', hb]
  have hX_le' : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
      ≤ 2 * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
        + (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) / 32 := by
    have h32 : (1 / 32 : ℝ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2)
        = (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) / 32 := by ring
    rw [h32] at hX_le
    exact hX_le
  exact agmon_arith hα hα1 hδ1 hAg_nn hX_nn hp_nn hq_nn hX_le' hmain

end

end Work.EllipticEst
