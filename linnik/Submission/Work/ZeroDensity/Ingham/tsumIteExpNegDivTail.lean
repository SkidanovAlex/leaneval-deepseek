import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Tail bound for the exponential series: for `Y > 0`, `M : ℕ` and a nonnegative constant `c`,
`Σ_{n > M} c · e^{-n/Y} ≤ c (Y+1) e^{-M/Y}`. (The series equals
`c · e^{-(M+1)/Y} / (1 - e^{-1/Y})`, and `1 - e^{-1/Y} ≥ 1/(Y+1)` by `e^{x} ≥ 1 + x`.) -/
theorem tsumIteExpNegDivTail (Y : ℝ) (hY : 0 < Y) (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (tsum fun n : ℕ => (if M < n then c * Real.exp (-(n : ℝ) / Y) else 0))
      ≤ c * (Y + 1) * Real.exp (-(M : ℝ) / Y) := by
  have hYne : Y ≠ 0 := ne_of_gt hY
  -- the ratio of the geometric series and its basic properties
  set r : ℝ := Real.exp (-(1 / Y)) with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; exact Real.exp_pos _
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hneg : -(1 / Y) < 0 := by
      have : 0 < 1 / Y := one_div_pos.mpr hY
      linarith
    simpa using Real.exp_lt_exp.mpr hneg
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr_pos.le]; exact hr_lt_one
  have hgeom : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hrnorm
  have hgeo_tsum : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ := tsum_geometric_of_norm_lt_one hrnorm
  -- each exponential term is the corresponding power of `r`
  have hexp_eq : ∀ n : ℕ, Real.exp (-(n : ℝ) / Y) = r ^ n := by
    intro n
    rw [hr_def, ← Real.exp_nat_mul]
    congr 1
    rw [mul_neg, mul_one_div, neg_div]
  let F : ℕ → ℝ := fun n => if M < n then c * Real.exp (-(n : ℝ) / Y) else 0
  change (∑' n : ℕ, F n) ≤ c * (Y + 1) * Real.exp (-(M : ℝ) / Y)
  have hF_nonneg : ∀ n, 0 ≤ F n := by
    intro n; dsimp only [F]
    split_ifs with h
    · exact mul_nonneg hc (Real.exp_pos _).le
    · exact le_rfl
  have hF_le : ∀ n, F n ≤ c * r ^ n := by
    intro n; dsimp only [F]
    split_ifs with h
    · rw [hexp_eq n]
    · exact mul_nonneg hc (pow_nonneg hr_pos.le n)
  have hF_summable : Summable F :=
    Summable.of_nonneg_of_le (f := fun n : ℕ => c * r ^ n) hF_nonneg hF_le (hgeom.mul_left c)
  -- the series is zero on the first `M + 1` terms, so it may be shifted
  have hsplit : (∑' n : ℕ, F n) = ∑' i : ℕ, F (i + (M + 1)) := by
    have h := Summable.sum_add_tsum_nat_add (M + 1) hF_summable
    have h0 : ∑ i ∈ Finset.range (M + 1), F i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiM : i ≤ M := by
        simp only [Finset.mem_range] at hi
        omega
      dsimp only [F]
      rw [if_neg (Nat.not_lt.mpr hiM)]
    rw [h0, zero_add] at h
    exact h.symm
  -- exact evaluation of the shifted geometric series
  have hval : (∑' i : ℕ, F (i + (M + 1))) = c * r ^ (M + 1) * (1 - r)⁻¹ := by
    have hcongr : ∀ i : ℕ, F (i + (M + 1)) = (c * r ^ (M + 1)) * r ^ i := by
      intro i
      have hMi : M < i + (M + 1) := by omega
      dsimp only [F]
      rw [if_pos hMi, hexp_eq (i + (M + 1)), add_comm i (M + 1), pow_add]
      ring
    calc (∑' i : ℕ, F (i + (M + 1)))
        = ∑' i : ℕ, (c * r ^ (M + 1)) * r ^ i := tsum_congr hcongr
      _ = (c * r ^ (M + 1)) * ∑' i : ℕ, r ^ i := hgeom.tsum_mul_left _
      _ = c * r ^ (M + 1) * (1 - r)⁻¹ := by rw [hgeo_tsum]
  -- `e^{1/Y} · r = 1`, whence `r (Y+1) ≤ Y`
  have hexp : Real.exp (1 / Y) * r = 1 := by
    rw [hr_def, ← Real.exp_add]
    rw [add_neg_cancel, Real.exp_zero]
  have hkey : r * (Y + 1) ≤ Y := by
    have h1 : 1 / Y + 1 ≤ Real.exp (1 / Y) := Real.add_one_le_exp _
    have h1' : 1 + 1 / Y ≤ Real.exp (1 / Y) := by linarith
    have hmul : (1 + 1 / Y) * r ≤ Real.exp (1 / Y) * r :=
      mul_le_mul_of_nonneg_right h1' hr_pos.le
    rw [hexp] at hmul
    have h2 : Y * ((1 + 1 / Y) * r) ≤ Y * 1 := mul_le_mul_of_nonneg_left hmul hY.le
    have h3 : Y * ((1 + 1 / Y) * r) = (Y + 1) * r := by
      rw [← mul_assoc, mul_add, mul_one, mul_one_div_cancel hYne]
    rw [h3, mul_one] at h2
    linarith
  have hsub_pos : 0 < 1 - r := by linarith
  have hsub_inv : (1 - r)⁻¹ ≤ Y + 1 := by
    rw [inv_eq_one_div, div_le_iff₀ hsub_pos]
    nlinarith [hkey, hY]
  rw [hsplit, hval, hexp_eq M]
  have hRM_nonneg : 0 ≤ c * r ^ (M + 1) := mul_nonneg hc (pow_nonneg hr_pos.le _)
  have hstep1 : c * r ^ (M + 1) * (1 - r)⁻¹ ≤ c * r ^ (M + 1) * (Y + 1) :=
    mul_le_mul_of_nonneg_left hsub_inv hRM_nonneg
  have hstep2 : c * r ^ (M + 1) * (Y + 1) ≤ c * (Y + 1) * r ^ M := by
    have hrr : r ^ (M + 1) ≤ r ^ M := by
      rw [pow_succ r M]
      calc r ^ M * r ≤ r ^ M * 1 :=
            mul_le_mul_of_nonneg_left hr_lt_one.le (pow_nonneg hr_pos.le M)
        _ = r ^ M := mul_one _
    calc c * r ^ (M + 1) * (Y + 1) = c * (Y + 1) * r ^ (M + 1) := by ring
      _ ≤ c * (Y + 1) * r ^ M := by
            apply mul_le_mul_of_nonneg_left hrr
            exact mul_nonneg hc (by linarith : (0 : ℝ) ≤ Y + 1)
  linarith [hstep1, hstep2]

end Work.ZeroDensity.Ingham
