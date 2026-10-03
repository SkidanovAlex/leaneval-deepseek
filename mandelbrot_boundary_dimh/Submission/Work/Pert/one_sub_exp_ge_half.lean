import Mathlib

namespace Work.Pert

/-- For `‖x‖ ≤ 1` the quantity `1 - e^x` is bounded below by `‖x‖/2`; the extremal point is
`x = -1`, where the ratio is `1 - e^{-1} ≈ 0.632 > 1/2`. -/
theorem one_sub_exp_ge_half (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖x‖ / 2 ≤ ‖1 - Complex.exp x‖ := by
  -- Split `x = 2u`, `1 - e^x = (1 - e^u)(1 + e^u)`, and bound the two factors separately.
  set u : ℂ := x / 2 with hu_def
  have hu_le : ‖u‖ ≤ 1 / 2 := by
    rw [hu_def, Complex.norm_div, Complex.norm_ofNat]
    linarith
  have hu_le1 : ‖u‖ ≤ 1 := by linarith
  have hnormu : ‖x‖ / 2 = ‖u‖ := by
    rw [hu_def, Complex.norm_div, Complex.norm_ofNat]
  -- `e^{-1/2} ≥ 3/5`
  have hexp_half : (3 : ℝ) / 5 ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have he1 : Real.exp (1 : ℝ) < 25 / 9 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hpos : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
    have hinv : (9 : ℝ) / 25 ≤ Real.exp (-(1 : ℝ)) := by
      rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ hpos]
      linarith
    have hsq : (Real.exp (-(1 / 2 : ℝ))) ^ 2 = Real.exp (-(1 : ℝ)) := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    have htarget : ((3 : ℝ) / 5) ^ 2 ≤ (Real.exp (-(1 / 2 : ℝ))) ^ 2 := by
      rw [hsq]; norm_num
      linarith
    have hb : 0 ≤ Real.exp (-(1 / 2 : ℝ)) := (Real.exp_pos _).le
    have hle : (3 / 5 : ℝ) * (3 / 5) ≤ Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) := by
      simpa only [pow_two] using htarget
    exact (mul_self_le_mul_self_iff (by norm_num : (0 : ℝ) ≤ 3 / 5) hb).mpr hle
  -- `cos (1/2) ≥ 7/8`
  have hcos_half : (7 : ℝ) / 8 ≤ Real.cos (1 / 2) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := (1 / 2 : ℝ))
    linarith
  -- First factor: `‖1 - e^u‖ ≥ (25/36) ‖u‖`.
  have hA : ‖u‖ * (25 / 36) ≤ ‖1 - Complex.exp u‖ := by
    have he : ‖Complex.exp u - 1 - u - u ^ 2 / 2‖ ≤ ‖u‖ ^ 3 * (2 / 9) := by
      have h := Complex.exp_bound hu_le1 (n := 3) (by norm_num)
      have hsum : (∑ m ∈ Finset.range 3, u ^ m / (m.factorial : ℂ)) = 1 + u + u ^ 2 / 2 := by
        simp [Finset.sum_range_succ, Nat.factorial]
      rw [hsum] at h
      have h1 : Complex.exp u - 1 - u - u ^ 2 / 2 = Complex.exp u - (1 + u + u ^ 2 / 2) := by
        ring
      rw [h1]
      refine h.trans_eq ?_
      norm_num
    have h1 : ‖u‖ - ‖u‖ ^ 2 / 2 ≤ ‖u + u ^ 2 / 2‖ := by
      have h := norm_sub_le (u + u ^ 2 / 2) (u ^ 2 / 2)
      simp only [add_sub_cancel_right, norm_div, norm_pow, Complex.norm_ofNat] at h
      linarith
    have h2 : ‖u‖ ^ 2 ≤ ‖u‖ / 2 := by nlinarith [norm_nonneg u, hu_le]
    have h3 : ‖u‖ ^ 3 * (2 / 9) ≤ ‖u‖ / 18 := by nlinarith [norm_nonneg u, hu_le]
    have htri : ‖u + u ^ 2 / 2‖ - ‖Complex.exp u - 1 - u - u ^ 2 / 2‖
        ≤ ‖(u + u ^ 2 / 2) + (Complex.exp u - 1 - u - u ^ 2 / 2)‖ := by
      have h := norm_add_le ((u + u ^ 2 / 2) + (Complex.exp u - 1 - u - u ^ 2 / 2))
        (-(Complex.exp u - 1 - u - u ^ 2 / 2))
      simp only [add_neg_cancel_right, norm_neg] at h
      linarith
    have hkey : (u + u ^ 2 / 2) + (Complex.exp u - 1 - u - u ^ 2 / 2) = Complex.exp u - 1 := by
      ring
    calc ‖u‖ * (25 / 36) = ‖u‖ - ‖u‖ / 4 - ‖u‖ / 18 := by ring
      _ ≤ ‖u‖ - ‖u‖ ^ 2 / 2 - ‖u‖ ^ 3 * (2 / 9) := by linarith
      _ ≤ ‖u + u ^ 2 / 2‖ - ‖Complex.exp u - 1 - u - u ^ 2 / 2‖ := by linarith
      _ ≤ ‖(u + u ^ 2 / 2) + (Complex.exp u - 1 - u - u ^ 2 / 2)‖ := htri
      _ = ‖Complex.exp u - 1‖ := by rw [hkey]
      _ = ‖1 - Complex.exp u‖ := by rw [← norm_neg, neg_sub]
  -- Second factor: `‖1 + e^u‖ ≥ 3/2`, via its real part `1 + e^{Re u} cos (Im u)`.
  have hB : (3 : ℝ) / 2 ≤ ‖1 + Complex.exp u‖ := by
    have hre : (1 + Complex.exp u).re = 1 + Real.exp u.re * Real.cos u.im := by
      simp [Complex.exp_re]
    have hre_ge : (3 : ℝ) / 2 ≤ (1 + Complex.exp u).re := by
      rw [hre]
      have hre_lower : -(1 / 2 : ℝ) ≤ u.re := by
        have h := Complex.abs_re_le_norm u
        have : |u.re| ≤ 1 / 2 := by linarith
        linarith [neg_abs_le u.re]
      have him_upper : |u.im| ≤ 1 / 2 := by
        have h := Complex.abs_im_le_norm u
        linarith
      have hexp_ge : (3 : ℝ) / 5 ≤ Real.exp u.re :=
        le_trans hexp_half (Real.exp_le_exp.mpr (by linarith))
      have hcos_ge : (7 : ℝ) / 8 ≤ Real.cos u.im := by
        have h1 : Real.cos (1 / 2) ≤ Real.cos |u.im| := by
          refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) ?_ him_upper
          linarith [Real.pi_gt_three]
        have h2 : Real.cos |u.im| = Real.cos u.im := by
          rcases abs_choice u.im with h | h
          · rw [h]
          · rw [h, Real.cos_neg]
        exact le_trans hcos_half (h2 ▸ h1)
      have hpe : (3 / 5 : ℝ) * (7 / 8) ≤ Real.exp u.re * Real.cos u.im :=
        mul_le_mul hexp_ge hcos_ge (by linarith) (Real.exp_pos u.re).le
      nlinarith [hpe]
    calc (3 : ℝ) / 2 ≤ (1 + Complex.exp u).re := hre_ge
      _ ≤ ‖1 + Complex.exp u‖ := Complex.re_le_norm _
  have hprod : ‖u‖ ≤ ‖1 - Complex.exp u‖ * ‖1 + Complex.exp u‖ := by
    have hmul := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 3 / 2) (norm_nonneg _)
    have heq : ‖u‖ * (25 / 36) * (3 / 2) = ‖u‖ * (25 / 24) := by ring
    have hge : ‖u‖ ≤ ‖u‖ * (25 / 24) := by nlinarith [norm_nonneg u]
    linarith [hmul, heq.ge, hge]
  have hfac : 1 - Complex.exp x = (1 - Complex.exp u) * (1 + Complex.exp u) := by
    rw [show x = u + u from by rw [hu_def]; ring, Complex.exp_add]
    ring
  calc ‖x‖ / 2 = ‖u‖ := hnormu
    _ ≤ ‖1 - Complex.exp u‖ * ‖1 + Complex.exp u‖ := hprod
    _ = ‖1 - Complex.exp x‖ := by rw [hfac, norm_mul]

end Work.Pert
