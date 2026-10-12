import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Work.BoseFixB1S.cos_pi_pow96_le_exp_neg192
import Submission.Work.BoseFixB1S.oneD_pow96_integral_eq_Icc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.oneD_pow96_integral_le_conv48`

`∫_ℝ (ζ s)^96 ds ≤ 1/7`, where `ζ = Submission.BoseGases.zeta1d` is the 1D cosine
profile `cos (π ·)` on `|·| ≤ 1/2`, zero outside.

The true value is `C(96,48)/2^96 = ∫_{Icc (-1/2) (1/2)} cos^96 (π s) ds ≈ 0.0812`, so
`1/7 ≈ 0.1429` has comfortable margin.  The proof is the crude Gaussian route:

* `oneD_pow96_integral_eq_Icc` (colleague): `∫ ζ^96 = ∫_{Icc (-1/2) (1/2)} cos^96 (π ·)`;
* `cos_pi_pow96_le_exp_neg192` (colleague): on `|s| ≤ 1/2`, `cos (π s)^96 ≤ exp (-192 s²)`
  (`cos x ≤ 1 - 2 x²/π²` from `Real.cos_le_one_sub_mul_cos_sq`, then `log (1 - t) ≤ -t`);
* `∫_{Icc (-1/2) (1/2)} exp (-192 s²) ≤ ∫_ℝ exp (-192 s²) = √(π/192) = 0.1279… ≤ 1/7`
  (`integral_gaussian`, `Real.pi_lt_d20`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false

/-- The Gaussian integral `∫_ℝ exp (-192 s²) = √(π/192)` is `≤ 1/7`
(since `π < 3.1415927 < 192/49`). -/
lemma exp_neg192_sq_integral_le_seventh :
    (∫ s : ℝ, Real.exp (-(192 : ℝ) * s ^ 2)) ≤ 1 / 7 := by
  have h : (∫ s : ℝ, Real.exp (-(192 : ℝ) * s ^ 2)) = √(Real.pi / 192) := by
    simpa using integral_gaussian (192 : ℝ)
  rw [h, Real.sqrt_le_left (by norm_num)]
  nlinarith [Real.pi_lt_d20]

theorem oneD_pow96_integral_le_conv48 :
    (∫ s : ℝ, (Submission.BoseGases.zeta1d s) ^ 96) ≤ 1 / 7 := by
  rw [oneD_pow96_integral_eq_Icc]
  calc ∫ s in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Real.cos (Real.pi * s) ^ 96
      ≤ ∫ s in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Real.exp (-(192 : ℝ) * s ^ 2) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact (by fun_prop : Continuous fun s : ℝ => Real.cos (Real.pi * s) ^ 96).integrableOn_Icc
        · exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(192 : ℝ) * s ^ 2)).integrableOn_Icc
        · exact measurableSet_Icc
        · intro s hs
          exact cos_pi_pow96_le_exp_neg192 s
            (by rw [Set.mem_Icc] at hs; rw [abs_le]; exact ⟨hs.1, hs.2⟩)
    _ ≤ ∫ s : ℝ, Real.exp (-(192 : ℝ) * s ^ 2) :=
        MeasureTheory.setIntegral_le_integral (integrable_exp_neg_mul_sq (by norm_num))
          (Filter.Eventually.of_forall fun s => Real.exp_nonneg _)
    _ ≤ 1 / 7 := exp_neg192_sq_integral_le_seventh

end Work.BoseFixB1S
