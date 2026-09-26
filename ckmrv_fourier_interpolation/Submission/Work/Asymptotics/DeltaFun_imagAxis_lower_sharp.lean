import Mathlib
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.KPlusXiDefs

namespace Work.Asymptotics

/-- For `0 ≤ q ≤ 1/100` the 24-th power of the eta product is at least `1/2`.

Since `∏'ₙ (1 - q^{n+1}) ≥ 1 - Σ'ₙ q^{n+1} = 1 - q/(1-q) ≥ 1 - 2q`, its 24-th power is at
least `(1 - 2q)^24 ≥ 1 - 48q ≥ 1 - 48/100 ≥ 1/2` (Bernoulli). -/
lemma tprod_one_sub_pow24_ge_half {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100) :
    (1 : ℝ) / 2 ≤ ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
  have hq1 : q < 1 := by linarith
  have hsumm : Summable (fun n : ℕ => q ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  have hM : Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) := by
    have h := Real.multipliable_one_add_of_summable (f := fun n : ℕ => -(q ^ (n + 1))) hsumm.neg
    simpa only [sub_eq_add_neg] using h
  have hQ : 1 - 2 * q ≤ ∏' n : ℕ, (1 - q ^ (n + 1)) :=
    tprod_one_sub_pow_ge hq0 (by linarith)
  have hpow : (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24
      = ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 :=
    (hM.tprod_pow 24).symm
  rw [← hpow]
  have hnonneg : 0 ≤ 1 - 2 * q := by linarith
  have hb : (1 : ℝ) - 48 * q ≤ (1 - 2 * q) ^ 24 := by
    have h1 : (1 : ℝ) + (24 : ℝ) * (-(2 * q)) = 1 - 48 * q := by ring
    have h2 : (1 : ℝ) + -(2 * q) = 1 - 2 * q := by ring
    rw [← h1, ← h2]
    exact one_add_mul_le_pow (a := -(2 * q)) (by linarith : (-2 : ℝ) ≤ -(2 * q)) 24
  have h48 : 48 * q ≤ 1 / 2 := by linarith
  linarith [pow_le_pow_left₀ hnonneg hQ 24]

theorem DeltaFun_imagAxis_lower_sharp (t : ℝ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤
      ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
  have hq0 : 0 ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hq100 : Real.exp (-(2 * Real.pi * t)) ≤ 1 / 100 := by
    have h6 : (6 : ℝ) ≤ 2 * Real.pi * t := by nlinarith [Real.pi_gt_three, ht1]
    have h100 : (100 : ℝ) ≤ Real.exp 6 := by
      have h1 : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 6 := by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
      have h2 : (100 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
      linarith
    have hexp : (100 : ℝ) ≤ Real.exp (2 * Real.pi * t) := le_trans h100 (Real.exp_le_exp.mpr h6)
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp
  have hP : (1 : ℝ) / 2 ≤ ∏' n : ℕ, (1 - Real.exp (-(2 * Real.pi * t)) ^ (n + 1)) ^ 24 :=
    tprod_one_sub_pow24_ge_half hq0 hq100
  have hPnn : 0 ≤ ∏' n : ℕ, (1 - Real.exp (-(2 * Real.pi * t)) ^ (n + 1)) ^ 24 :=
    le_trans (by norm_num) hP
  have hnorm : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      = Real.exp (-(2 * Real.pi * t))
        * ∏' n : ℕ, (1 - Real.exp (-(2 * Real.pi * t)) ^ (n + 1)) ^ 24 := by
    rw [DeltaFun_imagAxis_eq t ht, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq0, abs_of_nonneg hPnn]
  rw [hnorm]
  calc (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t))
      = Real.exp (-(2 * Real.pi * t)) * (1 / 2) := by ring
    _ ≤ Real.exp (-(2 * Real.pi * t))
          * ∏' n : ℕ, (1 - Real.exp (-(2 * Real.pi * t)) ^ (n + 1)) ^ 24 :=
        mul_le_mul_of_nonneg_left hP hq0

end Work.Asymptotics
