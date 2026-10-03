import Mathlib

namespace Work.Pert

theorem geom_exp_sum_le {r η : ℝ} (hr : 0 < r) (n : ℕ) :
    ∑ j ∈ Finset.range n, Real.exp (-(2 * Real.pi * (η + r * j))) ≤
      Real.exp (-(2 * Real.pi * η)) * (1 + 1 / (2 * Real.pi * r)) := by
  -- Write `t = 2 π r > 0` and `q = exp (-t) ∈ [0,1)`; the `j`-th summand is
  -- `exp (-(2 π η)) * q ^ j`, so the sum is a truncated geometric series.
  set t : ℝ := 2 * Real.pi * r with ht
  have htpos : 0 < t := by rw [ht]; positivity
  set q : ℝ := Real.exp (-t) with hq
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hqlt1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; linarith
  -- Summand identity.
  have hterm : ∀ j : ℕ,
      Real.exp (-(2 * Real.pi * (η + r * ↑j))) = Real.exp (-(2 * Real.pi * η)) * q ^ j := by
    intro j
    have he : -(2 * Real.pi * (η + r * ↑j)) = -(2 * Real.pi * η) + ↑j * (-t) := by
      rw [ht]; ring
    rw [he, Real.exp_add, hq, Real.exp_nat_mul]
  have hsum1 : ∑ j ∈ Finset.range n, Real.exp (-(2 * Real.pi * (η + r * ↑j)))
      = Real.exp (-(2 * Real.pi * η)) * ∑ j ∈ Finset.range n, q ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  -- The partial geometric sum is at most the full one, `(1 - q)⁻¹`.
  have hgeom : ∑ j ∈ Finset.range n, q ^ j ≤ (1 - q)⁻¹ := by
    have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hqlt1
    have hs : Summable (fun j : ℕ => q ^ j) := summable_geometric_of_norm_lt_one hnorm
    have h := hs.sum_le_tsum (Finset.range n) (fun i _ => pow_nonneg hq0 i)
    rwa [tsum_geometric_of_norm_lt_one hnorm] at h
  -- `1/(1 - e^{-t}) ≤ 1 + 1/t`, from `1 + t ≤ e^t`.
  have hbound : (1 - q)⁻¹ ≤ 1 + 1 / t := by
    have h1mq : 0 < 1 - q := by linarith
    have hmul : (t + 1) * q ≤ 1 := by
      have h2 : (t + 1) * (Real.exp t)⁻¹ ≤ Real.exp t * (Real.exp t)⁻¹ :=
        mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (by positivity)
      rw [mul_inv_cancel₀ (ne_of_gt (Real.exp_pos t))] at h2
      rwa [hq, Real.exp_neg]
    have hkey : t ≤ (t + 1) * (1 - q) := by nlinarith [hmul]
    rw [inv_le_iff_one_le_mul₀ h1mq]
    have htwo : 1 + 1 / t = (t + 1) / t := by rw [add_div, div_self (ne_of_gt htpos)]
    rw [htwo, div_mul_eq_mul_div, le_div_iff₀ htpos]
    linarith
  calc ∑ j ∈ Finset.range n, Real.exp (-(2 * Real.pi * (η + r * ↑j)))
      = Real.exp (-(2 * Real.pi * η)) * ∑ j ∈ Finset.range n, q ^ j := hsum1
    _ ≤ Real.exp (-(2 * Real.pi * η)) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom (Real.exp_nonneg _)
    _ ≤ Real.exp (-(2 * Real.pi * η)) * (1 + 1 / t) :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)

end Work.Pert
