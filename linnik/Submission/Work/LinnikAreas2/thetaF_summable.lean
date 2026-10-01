import Mathlib

set_option linter.unusedVariables false

namespace Work.LinnikAreas2

/-- For `σ > 0` and `0 < B < A` the series
`∑ n^(σ-1) (e^{-n/A} - e^{-n/B})` converges: the difference of the two
exponentials is nonnegative and dominated by `e^{-n/A}`, while for a natural
`k ≥ σ - 1` one has `n^(σ-1) ≤ n^k` for `n ≥ 1`, and `n^k e^{-n/A}` is summable. -/
theorem thetaF_summable {σ A B : ℝ} (hσ : 0 < σ) (hB : 0 < B) (hBA : B < A) :
    Summable (fun n : ℕ =>
      (n:ℝ)^(σ-1) * (Real.exp (-((n:ℝ)/A)) - Real.exp (-((n:ℝ)/B)))) := by
  have hA : 0 < A := lt_trans hB hBA
  have hAB : A⁻¹ ≤ B⁻¹ := by
    have h := (one_div_lt_one_div_of_lt hB hBA).le
    rwa [one_div, one_div] at h
  obtain ⟨k, hk⟩ := exists_nat_ge (σ - 1)
  have hmaj : Summable (fun n : ℕ => (n:ℝ)^k * Real.exp (-(1/A) * (n:ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul k (r := 1/A) (by positivity)
  have hmaj_shift : Summable
      (fun n : ℕ => (((n+1:ℕ):ℝ))^k * Real.exp (-(((n+1:ℕ):ℝ)/A))) := by
    refine ((summable_nat_add_iff 1).mpr hmaj).congr (fun n => ?_)
    have h : -(((n+1:ℕ):ℝ)/A) = -(1/A) * ((n+1:ℕ):ℝ) := by
      rw [div_eq_mul_inv, one_div]; ring
    rw [h]
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj_shift
  · have hm0 : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := by positivity
    have hd : 0 ≤ Real.exp (-(((n+1:ℕ):ℝ)/A)) - Real.exp (-(((n+1:ℕ):ℝ)/B)) := by
      apply sub_nonneg.mpr
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hAB hm0
    exact mul_nonneg (Real.rpow_nonneg hm0 _) hd
  · have hm1 : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.le_add_left 1 n
    have hm0 : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := le_trans zero_le_one hm1
    have h1 : ((n+1:ℕ):ℝ)^(σ-1) ≤ ((n+1:ℕ):ℝ)^k := by
      have h := Real.rpow_le_rpow_of_exponent_le hm1 hk
      rwa [Real.rpow_natCast] at h
    have h2 : Real.exp (-(((n+1:ℕ):ℝ)/A)) - Real.exp (-(((n+1:ℕ):ℝ)/B))
        ≤ Real.exp (-(((n+1:ℕ):ℝ)/A)) := sub_le_self _ (Real.exp_nonneg _)
    have h2n : 0 ≤ Real.exp (-(((n+1:ℕ):ℝ)/A)) - Real.exp (-(((n+1:ℕ):ℝ)/B)) := by
      apply sub_nonneg.mpr
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hAB hm0
    exact mul_le_mul h1 h2 h2n (pow_nonneg hm0 k)

end Work.LinnikAreas2
