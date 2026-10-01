import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

namespace Work.OffAxis

open Work.ZeroFreeTables

/-- **Upper bound for `Re G72(iσ)` for large imaginary part.**

For `σ ≥ 7/2` we have `Re G72(iσ) ≤ 4/35`.

`G72` is the Laplace transform `w ↦ ∫₀² e^{-wy} g72 y dy` of HB Lemma 7.2's weight
`g72 y = (1/30)(2-y)³(4+6y+y²)`.  On the imaginary axis the closed form
`G72_re_closed_zero` gives

    Re G72(iσ) = 4/σ⁴ + 4/σ⁶ + cos(2σ)·(4(σ²-1)/σ⁶) + sin(2σ)·(-(8/σ⁵)) ,

and since `σ ≥ 7/2 > 1` each trigonometric factor can be bounded by `1` (resp. `-1`)
against a non-negative (resp. non-positive) coefficient:

    Re G72(iσ) ≤ 8/σ⁴ + 8/σ⁵ + 4/σ⁶ ≤ 8/(7/2)⁴ + 8/(7/2)⁵ + 4/(7/2)⁶ = 8320/117649 ≤ 4/35 .

(The sharp truth is much smaller — the value at `σ = 7/2` is about `0.0373` — so the
crude estimate is more than sufficient.) -/
theorem G72ImagReBound : ∀ σ : ℝ, 7 / 2 ≤ σ → (Work.ZeroFreeTables.G72 ((σ : ℂ) * Complex.I)).re ≤ 4 / 35 := by
  intro σ hσ
  have hσpos : 0 < σ := by linarith
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  have h4 : (7/2:ℝ)^4 ≤ σ^4 := pow_le_pow_left₀ (by norm_num) hσ 4
  have h5 : (7/2:ℝ)^5 ≤ σ^5 := pow_le_pow_left₀ (by norm_num) hσ 5
  have h6 : (7/2:ℝ)^6 ≤ σ^6 := pow_le_pow_left₀ (by norm_num) hσ 6
  have hx0 : 0 ≤ 4 * (σ ^ 2 - 1) / σ ^ 6 := by
    apply div_nonneg
    · nlinarith [sq_nonneg σ, hσ]
    · positivity
  have hnum : 4 * (σ ^ 2 - 1) / σ ^ 6 ≤ 4 / σ ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg σ, sq_nonneg (σ^2)]
  have hcos : Real.cos (2 * σ) * (4 * (σ ^ 2 - 1) / σ ^ 6) ≤ 4 / σ ^ 4 :=
    calc Real.cos (2 * σ) * (4 * (σ ^ 2 - 1) / σ ^ 6)
        ≤ 1 * (4 * (σ ^ 2 - 1) / σ ^ 6) := mul_le_mul_of_nonneg_right (Real.cos_le_one _) hx0
      _ = 4 * (σ ^ 2 - 1) / σ ^ 6 := one_mul _
      _ ≤ 4 / σ ^ 4 := hnum
  have hsin : Real.sin (2 * σ) * (-(8 / σ ^ 5)) ≤ 8 / σ ^ 5 := by
    have hc : -(8 / σ ^ 5) ≤ 0 := by
      have hp : (0:ℝ) < 8 / σ ^ 5 := by positivity
      linarith
    simpa using mul_le_mul_of_nonpos_right (Real.neg_one_le_sin (2*σ)) hc
  have hS : 8/σ^4 + 8/σ^5 + 4/σ^6 ≤ 4/35 := by
    have h1 : 8/σ^4 ≤ 8/((7/2:ℝ)^4) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
    have h2 : 8/σ^5 ≤ 8/((7/2:ℝ)^5) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h5
    have h3 : 4/σ^6 ≤ 4/((7/2:ℝ)^6) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h6
    have h4' : 8/((7/2:ℝ)^4) + 8/((7/2:ℝ)^5) + 4/((7/2:ℝ)^6) ≤ 4/35 := by norm_num
    linarith
  rw [Work.ZeroFreeTables.OffAxis.G72_re_closed_zero hσne]
  calc 4 / σ ^ 4 + 4 / σ ^ 6 + Real.cos (2 * σ) * (4 * (σ ^ 2 - 1) / σ ^ 6)
        + Real.sin (2 * σ) * -(8 / σ ^ 5)
      ≤ 4/σ^4 + 4/σ^6 + 4/σ^4 + 8/σ^5 := by linarith [hcos, hsin]
    _ = 8/σ^4 + 8/σ^5 + 4/σ^6 := by ring
    _ ≤ 4/35 := hS

end Work.OffAxis
