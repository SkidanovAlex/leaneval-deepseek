import Mathlib

namespace Work.LinnikAreas.Density4

/-- Geometric-series bound for the exponential decay: the partial sum of
`exp(-((n+1)/X))` over `n ∈ [K, M]` is bounded by the full geometric tail
`exp(-((K+1)/X)) / (1 - exp(-(1/X)))`. -/
lemma geom_exp_Icc_bound (X : ℝ) (hX : 0 < X) (K M : ℕ) :
    ∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ) + 1) / X))
      ≤ Real.exp (-(((K:ℝ) + 1) / X)) / (1 - Real.exp (-(1 / X))) := by
  set r := Real.exp (-(1 / X)) with hr
  have hr_nonneg : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have h1Xpos : 0 < 1 / X := one_div_pos.mpr hX
  have hr_lt_one : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have hterm : ∀ n : ℕ, Real.exp (-(((n:ℝ) + 1) / X)) = r ^ (n + 1) := by
    intro n
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hKterm : r ^ (K + 1) = Real.exp (-(((K:ℝ) + 1) / X)) := by
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hIccIco : Finset.Icc K M = Finset.Ico K (M + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  calc ∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ) + 1) / X))
      = ∑ n ∈ Finset.Icc K M, r ^ (n + 1) := by
        apply Finset.sum_congr rfl; intro n _; exact hterm n
    _ = (∑ n ∈ Finset.Icc K M, r ^ n) * r := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro n _; rw [pow_succ]
    _ ≤ (r ^ K / (1 - r)) * r := by
        rw [hIccIco]
        exact mul_le_mul_of_nonneg_right
          (geom_sum_Ico_le_of_lt_one (m := K) (n := M + 1) hr_nonneg hr_lt_one) hr_nonneg
    _ = r ^ (K + 1) / (1 - r) := by
        rw [div_mul_eq_mul_div, ← pow_succ]
    _ = Real.exp (-(((K:ℝ) + 1) / X)) / (1 - Real.exp (-(1 / X))) := by
        rw [hKterm, hr]

end Work.LinnikAreas.Density4
