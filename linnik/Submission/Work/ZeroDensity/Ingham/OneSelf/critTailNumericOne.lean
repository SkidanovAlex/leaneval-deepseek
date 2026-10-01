import Mathlib
import Submission.Work.ZeroDensity.Ingham.critTailExpPow
import Submission.Work.ZeroDensity.Ingham.critTailTLeExp
import Submission.Work.ZeroDensity.Ingham.critTailPointwiseCore
import Submission.Work.ZeroDensity.Ingham.critTailFinalNumeric

/-!
# Numeric tail estimate for the critical-line integral

For every `C₀ > 0` there is `A₀ ≥ 6` such that for all `A ≥ A₀`, `T ≥ 2`, writing
`H = A log (A T)`,

`C₀ √T (3 + T + H)^4 (1 + H)^6 e^{-(π/2) H} ≤ π/10`.

The three ingredients are:

* `T ≤ e^{H/100}` and `T^4 ≤ e^{H/25}` (from `A log T ≤ H` when `A ≥ 100` and `T ≥ 2`),
* `(1 + H)^{10} ≤ e^{H/4}` (once `H` exceeds a fixed threshold),
* the tail `C₀ (5/2)^4 e^{-(π/2 - 3/10) A}`, which is eventually `≤ π/10`.

Combining them pointwise absorbs every polynomial factor: the left side is at most
`C₀ (5/2)^4 e^{-(π/2 - 3/10) H} ≤ C₀ (5/2)^4 e^{-(π/2 - 3/10) A}` since `H ≥ A`.
-/

namespace Work.ZeroDensity.Ingham.OneSelf

theorem critTailNumericOne (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ A₀ : ℝ, 6 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ T : ℝ, 2 ≤ T →
      C₀ * Real.sqrt T * (3 + T + A * Real.log (A * T)) ^ 4
        * (1 + A * Real.log (A * T)) ^ 6
        * Real.exp (-(Real.pi / 2) * (A * Real.log (A * T))) ≤ Real.pi / 10 := by
  -- the exponential rate `π/2 - 3/10` is positive
  have hc : 0 < Real.pi / 2 - 3 / 10 := by nlinarith [Real.pi_gt_three]
  -- tail control: `C₀ (5/2)^4 e^{-(π/2-3/10) A} ≤ π/10` for large `A`
  obtain ⟨Ae, _hAe6, hAe⟩ := critTailFinalNumeric C₀ (Real.pi / 2 - 3 / 10) hC₀ hc
  -- polynomial-versus-exponential control: `(1+x)^10 ≤ e^{x/4}` for large `x`
  obtain ⟨X₁, hX₁⟩ := critTailExpPow (1 / 4) (by norm_num) 10
  refine ⟨max 6 (max 100 (max Ae (X₁ + 1))), le_max_left _ _, ?_⟩
  intro A hA T hT
  have hA100 : 100 ≤ A :=
    le_trans (le_trans (le_max_left (100 : ℝ) _) (le_max_right (6 : ℝ) _)) hA
  have hAeA : Ae ≤ A :=
    le_trans (le_trans (le_trans (le_max_left Ae (X₁ + 1)) (le_max_right (100 : ℝ) _))
      (le_max_right (6 : ℝ) _)) hA
  have hX1A : X₁ ≤ A :=
    le_trans (le_trans (le_trans (le_trans (le_of_lt (lt_add_one X₁)) (le_max_right Ae (X₁ + 1)))
      (le_max_right (100 : ℝ) _)) (le_max_right (6 : ℝ) _)) hA
  have hApos : 0 < A := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  have hlog1 : 1 ≤ Real.log (A * T) := by
    rw [Real.le_log_iff_exp_le (show (0 : ℝ) < A * T by linarith)]
    nlinarith [Real.exp_one_lt_three]
  -- `A ≤ H` where `H = A log (A T)`
  have hAH : A ≤ A * Real.log (A * T) := by
    have := mul_le_mul_of_nonneg_left hlog1 hApos.le
    simpa using this
  have hHX1 : X₁ ≤ A * Real.log (A * T) := le_trans hX1A hAH
  -- the two `T`-bounds coming from `T ≤ e^{H/A}` and the polynomial-vs-exponential bound
  obtain ⟨hsq, hT4⟩ := critTailTLeExp A T hA100 hT
  have hpow : (1 + A * Real.log (A * T)) ^ 10 ≤ Real.exp ((A * Real.log (A * T)) / 4) := by
    have h := hX₁ (A * Real.log (A * T)) hHX1
    rwa [show (1 / 4 : ℝ) * (A * Real.log (A * T)) = (A * Real.log (A * T)) / 4 by ring] at h
  -- pointwise core: the whole polynomial factor is swallowed by `e^{H/25}` etc.
  have hpt := critTailPointwiseCore A T hA100 hT hsq hT4 hpow
  have hKnn : (0 : ℝ) ≤ C₀ * (5 / 2 : ℝ) ^ 4 := mul_nonneg hC₀.le (by norm_num)
  -- multiply by `C₀ ≥ 0`
  have hstep1 :
      C₀ * Real.sqrt T * (3 + T + A * Real.log (A * T)) ^ 4
        * (1 + A * Real.log (A * T)) ^ 6
        * Real.exp (-(Real.pi / 2) * (A * Real.log (A * T)))
      ≤ C₀ * ((5 / 2 : ℝ) ^ 4
        * Real.exp (-(Real.pi / 2 - 3 / 10) * (A * Real.log (A * T)))) := by
    have h := mul_le_mul_of_nonneg_left hpt hC₀.le
    have heq : C₀ * Real.sqrt T * (3 + T + A * Real.log (A * T)) ^ 4
        * (1 + A * Real.log (A * T)) ^ 6
        * Real.exp (-(Real.pi / 2) * (A * Real.log (A * T)))
        = C₀ * (Real.sqrt T * (3 + T + A * Real.log (A * T)) ^ 4
        * (1 + A * Real.log (A * T)) ^ 6
        * Real.exp (-(Real.pi / 2) * (A * Real.log (A * T)))) := by
      simp only [mul_assoc]
    rw [heq]; exact h
  -- replace `H` by `A` in the exponential (monotone decay, since `H ≥ A`)
  have hexp : Real.exp (-(Real.pi / 2 - 3 / 10) * (A * Real.log (A * T)))
      ≤ Real.exp (-((Real.pi / 2 - 3 / 10) * A)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hc, hAH]
  have hstep2 :
      C₀ * ((5 / 2 : ℝ) ^ 4
        * Real.exp (-(Real.pi / 2 - 3 / 10) * (A * Real.log (A * T))))
      ≤ Real.pi / 10 := by
    have h1 : C₀ * ((5 / 2 : ℝ) ^ 4
        * Real.exp (-(Real.pi / 2 - 3 / 10) * (A * Real.log (A * T))))
        = C₀ * (5 / 2 : ℝ) ^ 4
        * Real.exp (-(Real.pi / 2 - 3 / 10) * (A * Real.log (A * T))) := by ring
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_left hexp hKnn) (hAe A hAeA)
  exact le_trans hstep1 hstep2

end Work.ZeroDensity.Ingham.OneSelf
