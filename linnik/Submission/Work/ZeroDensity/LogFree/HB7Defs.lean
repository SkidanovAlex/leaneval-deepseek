import Mathlib

namespace Work.ZeroDensity.LogFree

/-- The positive-half weight `exp(-exp(-(n+1)η)) * exp(-u*n)`, i.e. the `j = n ≥ 0` terms of the
weight series of Linnik/Heath-Brown HB7. -/
noncomputable def HB7P (η u : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(Real.exp (-(((n : ℝ) + 1) * η)))) * Real.exp (-(u * (n : ℝ)))

/-- The negative-half weight `exp(-exp(n*η)) * exp(u*(n+1))`, i.e. the `j = -(n+1) < 0` terms of the
weight series, re-indexed by `n : ℕ`. -/
noncomputable def HB7N (η u : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(Real.exp ((n : ℝ) * η))) * Real.exp (u * ((n : ℝ) + 1))

/-- `3n ≤ e^n` for every natural `n ≥ 2`. -/
theorem three_mul_nat_le_exp : ∀ n : ℕ, 2 ≤ n → 3 * (n : ℝ) ≤ Real.exp (n : ℝ) := by
  have h2 : (6 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [h]; nlinarith [Real.exp_one_gt_d9]
  have key : ∀ k : ℕ, 3 * ((k : ℝ) + 2) ≤ Real.exp ((k : ℝ) + 2) := by
    intro k
    induction k with
    | zero => convert h2 using 1 <;> norm_num
    | succ k ih =>
      push_cast
      have h : Real.exp ((k : ℝ) + 1 + 2) = Real.exp ((k : ℝ) + 2) * Real.exp 1 := by
        rw [show ((k : ℝ) + 1 + 2) = ((k : ℝ) + 2) + 1 by ring, Real.exp_add]
      have hmono : Real.exp 2 ≤ Real.exp ((k : ℝ) + 2) := by
        apply Real.exp_le_exp.mpr; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
      rw [h]
      nlinarith [Real.exp_one_gt_d9, ih, h2, hmono]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [this]
  exact key k

/-- Numerical bound `exp(4 - e) < 4`. -/
theorem exp_four_sub_exp_one_lt_four : Real.exp (4 - Real.exp 1) < 4 := by
  have h2 : Real.exp (4 - Real.exp 1) < Real.exp (Real.log 4) := by
    apply Real.exp_lt_exp.mpr
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [this, Real.log_pow]; ring
    rw [hlog4]
    linarith [Real.exp_one_gt_d9, Real.log_two_gt_d9]
  rwa [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h2

/-- `exp(-1) ≤ 1/2`. -/
theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1/2 := by
  rw [Real.exp_neg]
  have h : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1; linarith
  calc (Real.exp 1)⁻¹ = 1 / (Real.exp 1) := by rw [one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h

/-- For `0 ≤ r ≤ 1/2`, the geometric series sums to at most `2`. -/
theorem tsum_pow_le_two {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1/2) :
    (∑' n : ℕ, r ^ n) ≤ 2 := by
  rw [tsum_geometric_of_lt_one h0 (by linarith)]
  calc (1 - r)⁻¹ = 1 / (1 - r) := by rw [one_div]
    _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ = 2 := by norm_num

/-- `(exp(-1))^n = exp(-n)`. -/
theorem exp_neg_nat_eq_pow (n : ℕ) : Real.exp (-(n : ℝ)) = (Real.exp (-1)) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Summability and a `tsum` bound from a geometric majorant `C * r^n` (`0 ≤ r < 1`). -/
theorem summable_and_tsum_le_of_le_const_mul_pow {f : ℕ → ℝ} {r C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, 0 ≤ f n) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n, f n ≤ C * r ^ n) :
    Summable f ∧ (∑' n : ℕ, f n) ≤ C * (1 - r)⁻¹ := by
  have hg : Summable (fun n : ℕ => C * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hfS : Summable f := Summable.of_nonneg_of_le hf h hg
  refine ⟨hfS, ?_⟩
  have hle := hfS.tsum_le_tsum h hg
  rwa [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle

/-- `HB7P` as a single exponential. -/
theorem HB7P_eq_exp (η u : ℝ) (n : ℕ) :
    HB7P η u n = Real.exp (-(Real.exp (-(((n : ℝ) + 1) * η))) - u * (n : ℝ)) := by
  simp only [HB7P]
  rw [← Real.exp_add]
  congr 1

/-- `HB7N` as a single exponential. -/
theorem HB7N_eq_exp (η u : ℝ) (n : ℕ) :
    HB7N η u n = Real.exp (u * ((n : ℝ) + 1) - Real.exp ((n : ℝ) * η)) := by
  simp only [HB7N]
  rw [← Real.exp_add]
  congr 1
  ring

end Work.ZeroDensity.LogFree
