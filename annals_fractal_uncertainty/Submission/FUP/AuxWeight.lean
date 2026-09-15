import Submission.FUP.BMReduction
import Submission.FUP.Growth

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# The auxiliary Beurling–Malliavin weight `ω₀` of §5

Cohen's §5 needs one auxiliary weight: the plurisubharmonic extension `u₀` of

  `ω₀(x) = -χ(‖x‖)·‖x‖ / (log(2+‖x‖))²`

(with `χ` a smooth cutoff vanishing for `r ≤ 5` and equal to `1` for `r ≥ 10`), which is `≤ 0` on
`ℝᵈ`, vanishes on `B₂`, has linear-with-logarithm decay at infinity (which is what makes the
Beurling–Malliavin growth functional finite: a genuinely linear weight has *divergent* growth
functional, so `BM_step1` cannot be applied to it) and satisfies the Kohn–Nirenberg regularity
condition up to three derivatives.  It is obtained from the *proved* `Spec.BM_step1_statement`,
applied to `ω₀` itself; the output is then rescaled so that its Lipschitz constant and its growth
constant in the imaginary direction are at most `1` and `1/2` respectively.

This module only sets up `ω₀` and its elementary pointwise properties.  The two analytic inputs
(the `C³` bounds and the bound on the spherical maximal function) are commons lemmas
`Commons.Analysis.Calculus.omega0_iteratedFDeriv_le` and
`Commons.Analysis.Calculus.Gstar_omega0_le`.
-/

namespace Submission.FUP

/-- The auxiliary weight `ω₀(x) = -χ(‖x‖)·‖x‖/(log(2+‖x‖))²` of §5, with
`χ(r) = Real.smoothTransition (r/5 - 1)`. -/
noncomputable def omega0 (x : ℝᵈ) : ℝ :=
  -(Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))

lemma omega0_nonpos (x : ℝᵈ) : omega0 x ≤ 0 := by
  rw [omega0, neg_nonpos]
  exact mul_nonneg (Real.smoothTransition.nonneg _)
    (div_nonneg (norm_nonneg _) (sq_nonneg _))

lemma omega0_eq_zero_of_norm_le_5 {x : ℝᵈ} (hx : ‖x‖ ≤ 5) : omega0 x = 0 := by
  have h : ‖x‖ / 5 - 1 ≤ 0 := by linarith
  rw [omega0, Real.smoothTransition.zero_of_nonpos h, zero_mul, neg_zero]

lemma omega0_eq_zero_of_norm_le_two {x : ℝᵈ} (hx : ‖x‖ ≤ 2) : omega0 x = 0 :=
  omega0_eq_zero_of_norm_le_5 (le_trans hx (by norm_num))

/-- For `‖x‖ ≥ 10` the cutoff is `1`, so `ω₀` is exactly `-‖x‖/(log(2+‖x‖))²`. -/
lemma omega0_eq_of_ten_le_norm {x : ℝᵈ} (hx : 10 ≤ ‖x‖) :
    omega0 x = -(‖x‖ / (Real.log (2 + ‖x‖)) ^ 2) := by
  have h : 1 ≤ ‖x‖ / 5 - 1 := by linarith
  rw [omega0, Real.smoothTransition.one_of_one_le h, one_mul]

end Submission.FUP
