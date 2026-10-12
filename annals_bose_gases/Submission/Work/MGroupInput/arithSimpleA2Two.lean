import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.MGroupInput.arithSimpleA2TwoDslot
import Submission.Work.MGroupInput.arithSimpleA2TwoQuad
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

/-- Arithmetic core of the `m`-arm per-state assembly `perState_of_simpleA2Two`.

With `A := 8 π av`, `V := s³`, `u := P/V` the claim is (all in the regime
`0 < s`, `0 < μ`, `0 < av`, `0 ≤ D ≤ 8 π av`, `0 ≤ E₁`, `1 ≤ P`, `20 ≤ μ s³`,
`u ≤ 9 μ`, `u ≥ 8 μ + E₁`):

`(1/9)(u − μ)² A V ≤ ¼(u − μ)² A V − ½μ² A V + ½D(P+1)²/V
   − ½((1+1/20)D + (1/20)av)·(P(P+1)/V) − E₁ av P − 272 π av μ`.

The left side is the `m`-arm target; the right side is exactly what the corpus
chain (`pot_sharp_summary` + `DSquare_cancellation'` + the simple Bogoliubov
payment `SimpleA2Two` + the `CorrWord` bound) delivers.  Difference of the two
sides equals
`(5/36) A V (u−μ)² − 4π av μ² V + ½D(P+1)(1−εP)/V − ½ε av P(P+1)/V − E₁ av P − 272 π av μ`
with `ε = 1/20`; since `P ≥ 8 μ s³ ≥ 160 > 1/ε = 20` and `D ≤ 8π av` the
`D`-slots are bounded below by `4π av (P+1)(1−εP)/V`, and the window
`8μ + E₁ ≤ u ≤ 9μ` bounds `E₁ ≤ μ`, leaving a quadratic in `u` which is
nonnegative (the numerical margin at the hard end `μ s³ = 20`, `u = 8μ`,
`E₁ = 0`, `D = 8π av` is `≈ 78.7 · av · μ² s³ > 0`). -/
theorem arithSimpleA2Two {P : ℕ} {s μ av D E₁ : ℝ} (hs : 0 < s) (hμ : 0 < μ)
    (hav : 0 < av) (hD0 : 0 ≤ D) (hD1 : D ≤ 8 * Real.pi * av) (hE₁ : 0 ≤ E₁)
    (hP : 1 ≤ P) (hμs : 20 ≤ μ * s ^ 3) (hwin : (P : ℝ) / s ^ 3 ≤ 9 * μ)
    (hCn : 8 * μ + E₁ ≤ (P : ℝ) / s ^ 3) :
    (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * Real.pi * av * s ^ 3)
      ≤ (1 / 4) * ((P : ℝ) / s ^ 3 - μ) ^ 2 * (8 * Real.pi * av * s ^ 3)
        - (1 / 2) * μ ^ 2 * (8 * Real.pi * av * s ^ 3)
        + (1 / 2) * D * (((P : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av)
            * ((((P : ℝ) + 1) * (P : ℝ)) * (s ^ 3)⁻¹)
        - E₁ * av * (P : ℝ) - 272 * Real.pi * av * μ := by
  set V : ℝ := s ^ 3 with hVdef
  set x : ℝ := (P : ℝ) with hxdef
  set w : ℝ := μ * V with hwdef
  have hVpos : 0 < V := by rw [hVdef]; positivity
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hw20 : 20 ≤ w := by rw [hwdef]; exact hμs
  -- Rewrite the window hypotheses after multiplying by `V > 0`.
  have h1 : (8 * μ + E₁) * V ≤ x := (le_div_iff₀ hVpos).mp hCn
  have h2 : x ≤ 9 * μ * V := (div_le_iff₀ hVpos).mp hwin
  have hE1Vnn : 0 ≤ E₁ * V := mul_nonneg hE₁ (le_of_lt hVpos)
  have h8w : 8 * w ≤ x := by rw [hwdef]; nlinarith [h1, hE1Vnn]
  have hxup : x ≤ 9 * w := by rw [hwdef]; nlinarith [h2]
  have hx20 : 20 ≤ x := by nlinarith [h8w, hw20]
  have hE1V : E₁ * V ≤ x - 8 * (μ * V) := by nlinarith [h1]
  -- The polynomial core in `x = P` and `w = μ V`.
  have hkey := arithSimpleA2TwoQuad hw20 h8w hxup
  rw [hwdef] at hkey
  -- The `D`-slot bound.
  have hDbound := arithSimpleA2TwoDslot hav hVpos hD0 hD1 hx20
  -- The `E₁`-slot bound.
  have hEslot : E₁ * av * x ≤ ((x - 8 * (μ * V)) * x) * (av * V⁻¹) := by
    have h3 : E₁ * V * x ≤ (x - 8 * (μ * V)) * x := mul_le_mul_of_nonneg_right hE1V hx0
    have hnn : 0 ≤ av * V⁻¹ := by positivity
    have h4 := mul_le_mul_of_nonneg_right h3 hnn
    have h5 : (E₁ * V * x) * (av * V⁻¹) = E₁ * av * x := by field_simp
    linarith [h4, h5]
  have hnn : 0 ≤ av * V⁻¹ := by positivity
  -- Assemble: multiply the target by `V/av = V * av⁻¹` (up to the notation `⁻¹`).
  have hscale : (1 / 9) * (x - μ * V) ^ 2 * (8 * Real.pi) * (av * V⁻¹)
      ≤ ((1 / 4) * (x * V⁻¹ - μ) ^ 2 * (8 * Real.pi * av * V)
          - (1 / 2) * μ ^ 2 * (8 * Real.pi * av * V))
        + ((1 / 2) * D * (x + 1) ^ 2 * V⁻¹
          - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x * V⁻¹))
        + (- E₁ * av * x) + (- 272 * Real.pi * av * μ) := by
    have hk := mul_le_mul_of_nonneg_right hkey hnn
    have hC1 : ((1 / 4) * (x - μ * V) ^ 2 * (8 * Real.pi) - 4 * Real.pi * (μ * V) ^ 2) * (av * V⁻¹)
        = (1 / 4) * (x * V⁻¹ - μ) ^ 2 * (8 * Real.pi * av * V)
          - (1 / 2) * μ ^ 2 * (8 * Real.pi * av * V) := by
      field_simp; ring
    have hT6 : (- 272 * Real.pi * (μ * V)) * (av * V⁻¹) = - 272 * Real.pi * av * μ := by
      field_simp
    nlinarith [hk, hC1, hDbound, hEslot, hT6]
  have hA : (1 / 9) * (μ - x / V) ^ 2 * (8 * Real.pi * av * V)
      = (1 / 9) * (x - μ * V) ^ 2 * (8 * Real.pi) * (av * V⁻¹) := by
    field_simp
    ring
  rw [hA]
  convert hscale using 1; ring

end Work.MGroupInput
