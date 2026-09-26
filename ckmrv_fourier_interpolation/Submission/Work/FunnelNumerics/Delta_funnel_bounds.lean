import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp

namespace Work.FunnelNumerics

open scoped Topology

noncomputable section

/-- **The value of `Δ` on the imaginary axis, in factored form.**
For `t > 0`,
`‖Δ(it)‖ = e^{-2πt} · ∏'ₙ (1 - (e^{-2πt})^{n+1})^24`,
the norm of `Δ(it) = q ∏'ₙ (1 - q^{n+1})^24` with `q = e^{-2πt}`. -/
lemma DeltaFun_imagAxis_norm_eq (t : ℝ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ =
      Real.exp (-(2 * Real.pi * t)) *
        ∏' n : ℕ, (1 - (Real.exp (-(2 * Real.pi * t))) ^ (n + 1)) ^ 24 := by
  have hq0 : 0 ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hq3 : Real.exp (-(2 * Real.pi * t)) ≤ 1 / 3 := by
    have h3 : (3 : ℝ) ≤ Real.exp (2 * Real.pi) := by
      have h1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ); linarith
      have h2 : Real.exp 2 ≤ Real.exp (2 * Real.pi) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      linarith
    have hmono : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(2 * Real.pi)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, ht1])
    have hexp : Real.exp (-(2 * Real.pi)) = 1 / Real.exp (2 * Real.pi) := by
      rw [Real.exp_neg, inv_eq_one_div]
    rw [hexp] at hmono
    exact le_trans hmono (one_div_le_one_div_of_le (by norm_num) h3)
  obtain ⟨hlo, -⟩ := Work.Asymptotics.tprod_one_sub_pow24_mem _ hq0 hq3
  rw [Work.Asymptotics.DeltaFun_imagAxis_eq t ht, norm_mul]
  congr 1
  · rw [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re]
  · simp [abs_of_nonneg (le_trans (by norm_num) hlo)]

/-- **The imaginary-axis upper bound for `Δ`.**  For `1 ≤ t`,
`‖Δ(it)‖ ≤ e^{-2πt}`, the sharp form of the cusp asymptotics: the eta product
`∏'ₙ (1 - q^{n+1})^24 ≤ 1` is absorbed into the leading term `q = e^{-2πt}`. -/
lemma DeltaFun_imagAxis_norm_le (t : ℝ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤ Real.exp (-(2 * Real.pi * t)) := by
  have hq0 : 0 ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hq3 : Real.exp (-(2 * Real.pi * t)) ≤ 1 / 3 := by
    have h3 : (3 : ℝ) ≤ Real.exp (2 * Real.pi) := by
      have h1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ); linarith
      have h2 : Real.exp 2 ≤ Real.exp (2 * Real.pi) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      linarith
    have hmono : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(2 * Real.pi)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, ht1])
    have hexp : Real.exp (-(2 * Real.pi)) = 1 / Real.exp (2 * Real.pi) := by
      rw [Real.exp_neg, inv_eq_one_div]
    rw [hexp] at hmono
    exact le_trans hmono (one_div_le_one_div_of_le (by norm_num) h3)
  obtain ⟨-, hhi⟩ := Work.Asymptotics.tprod_one_sub_pow24_mem _ hq0 hq3
  rw [DeltaFun_imagAxis_norm_eq t ht ht1]
  calc Real.exp (-(2 * Real.pi * t)) *
        ∏' n : ℕ, (1 - (Real.exp (-(2 * Real.pi * t))) ^ (n + 1)) ^ 24
      ≤ Real.exp (-(2 * Real.pi * t)) * 1 :=
        mul_le_mul_of_nonneg_left hhi (Real.exp_pos _).le
    _ = Real.exp (-(2 * Real.pi * t)) := mul_one _

/-- **The two funnel bounds for the modular discriminant.**

* On the funnel `{Im τ ≥ 2}` the (sharp) lower bound `‖Δ(τ)‖ ≥ (1/2)‖q(τ)‖` holds,
  where `q(τ) = e^{2πiτ}`;
* On the imaginary axis, for `t ≥ 1` the sharp upper bound `‖Δ(it)‖ ≤ e^{-2πt}` holds.

These are the two estimates which make the CKMRV funnel tail expansion uniform in `τ`. -/
theorem Delta_funnel_bounds :
    (∀ τ : UpperHalfPlane, 2 ≤ τ.im →
      (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖) ∧
    (∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤ Real.exp (-(2 * Real.pi * t))) := by
  refine ⟨?_, ?_⟩
  · intro τ hτ
    rw [Work.Asymptotics.norm_qParamFun τ]
    exact Work.Asymptotics.DeltaFun_funnel_lower_sharp hτ
  · intro t ht ht1
    exact DeltaFun_imagAxis_norm_le t ht ht1

end

end Work.FunnelNumerics
