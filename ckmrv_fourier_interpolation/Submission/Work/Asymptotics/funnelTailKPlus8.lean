/-
# The funnel tail expansion of `K₊^{(8)}`

Proof of `Work.Asymptotics.KPlus_funnel_tail_eight`: on the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and the
contour `z = i t`, `t ≥ Im τ + 1`, the kernel `K₊^{(8)}` differs from the cusp model
`Work.Asymptotics.Compact.Gplus 8` by `O((scale τ)^N (1+t)^M exp (-π (t - Im τ)))`.

The proof uses the uniform divisor bound `‖Δ(z)(j τ − j z)‖ ≥ 1/16` (from the explicit
quantitative estimates `E4Fun_sub_one_explicit`, `DeltaFun_funnel_lower_sharp` and
`DeltaFun_imagAxis_atTop`), the decomposition `KPlus_eight_decomposition`, the cancelled form
`Gplus8_eq` of the model and the `O(q)` atom expansions.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Topology

noncomputable section

/-- A crude lower bound for `exp 1`. -/
lemma exp_one_pos' : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1

/-- The numerical comparison `6.75 e^{-2π} ≤ 1/16`. -/
lemma six_le_exp : (6.75 : ℝ) * Real.exp (-(2 * Real.pi)) ≤ 1 / 16 := by
  have h1 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have h4 : (387 : ℝ) ≤ Real.exp 6 := by
    rw [h3]
    have h5 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) ((by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1)) 6
    norm_num at h5 ⊢
    linarith
  have h6 : Real.exp (-6) ≤ 1 / 387 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h4
  have h7 : 6.75 * Real.exp (-(2 * Real.pi)) ≤ 6.75 * (1 / 387) :=
    mul_le_mul_of_nonneg_left (le_trans h2 h6) (by norm_num)
  have h8 : 6.75 * (1 / 387 : ℝ) ≤ 1 / 16 := by norm_num
  linarith

/-- `20000 e^{-2π t} ≤ 1/2` for `t ≥ 3`. -/
lemma exp_decay_small {t : ℝ} (ht : 3 ≤ t) : (20000 : ℝ) * Real.exp (-(2 * Real.pi * t)) ≤ 1 / 2 := by
  have h0 : (6 * Real.pi : ℝ) ≤ 2 * Real.pi * t := by nlinarith [Real.pi_pos, ht]
  have h1 : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(6 * Real.pi)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp 18 = (Real.exp 1) ^ 18 := by
    rw [show (18 : ℝ) = (18 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have h3 : (40000 : ℝ) ≤ Real.exp (6 * Real.pi) := by
    have h4 : Real.exp 18 ≤ Real.exp (6 * Real.pi) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_gt_three]
    have h5 : (40000 : ℝ) ≤ Real.exp 18 := by
      rw [h2]
      have h6 : (2.7 : ℝ) ^ 18 ≤ (Real.exp 1) ^ 18 :=
        pow_le_pow_left₀ (by norm_num) ((by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1)) 18
      norm_num at h6 ⊢
      linarith
    linarith
  have h7 : Real.exp (-(6 * Real.pi)) ≤ 1 / 40000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  have h8 : (20000 : ℝ) * Real.exp (-(2 * Real.pi * t)) ≤ 20000 * (1 / 40000) :=
    mul_le_mul_of_nonneg_left (le_trans h1 h7) (by norm_num)
  have h9 : (20000 : ℝ) * (1 / 40000) ≤ 1 / 2 := by norm_num
  linarith


end

end Work.Asymptotics
