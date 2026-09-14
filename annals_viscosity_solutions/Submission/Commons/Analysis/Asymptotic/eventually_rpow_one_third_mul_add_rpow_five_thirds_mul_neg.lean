import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace Commons.Analysis.Asymptotic

theorem eventually_rpow_one_third_mul_add_rpow_five_thirds_mul_neg {A : ℕ → ℝ} {lam : ℕ → ℝ}
    {a W : ℝ} (hA : Filter.Tendsto A Filter.atTop (nhds a)) (ha : a < 0)
    (hlam : Filter.Tendsto lam Filter.atTop (nhds 0)) (hpos : ∀ n, 0 < lam n) :
    ∀ᶠ n in Filter.atTop,
      lam n ^ ((1:ℝ)/3) * A n + lam n ^ ((5:ℝ)/3) * W < 0 := by
  -- eventually `A n < a/2` (with `a/2 < 0`)
  have hA2 : ∀ᶠ n in Filter.atTop, A n < a / 2 :=
    hA.eventually (eventually_lt_nhds (by linarith))
  -- `lam n ^ (4/3) * W → 0`
  have hlam43 : Filter.Tendsto (fun n : ℕ => lam n ^ ((4:ℝ)/3)) Filter.atTop (nhds 0) :=
    hlam.rpow_const_nhds_zero (by norm_num)
  have hWlim : Filter.Tendsto (fun n : ℕ => lam n ^ ((4:ℝ)/3) * W) Filter.atTop (nhds 0) := by
    simpa using hlam43.mul_const W
  -- eventually `lam n ^ (4/3) * W < -a/2`
  have hW : ∀ᶠ n in Filter.atTop, lam n ^ ((4:ℝ)/3) * W < -(a / 2) :=
    hWlim.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hA2, hW] with n hAn hWn
  have hsum : A n + lam n ^ ((4:ℝ)/3) * W < 0 := by
    have := add_lt_add hAn hWn
    linarith
  have hpos13 : 0 < lam n ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos (hpos n) _
  have hmul : lam n ^ ((1:ℝ)/3) * (A n + lam n ^ ((4:ℝ)/3) * W) < 0 :=
    mul_neg_of_pos_of_neg hpos13 hsum
  have heq : lam n ^ ((1:ℝ)/3) * (A n + lam n ^ ((4:ℝ)/3) * W)
      = lam n ^ ((1:ℝ)/3) * A n + lam n ^ ((5:ℝ)/3) * W := by
    have h1 : lam n ^ ((1:ℝ)/3) * lam n ^ ((4:ℝ)/3) = lam n ^ ((5:ℝ)/3) := by
      rw [← Real.rpow_add (hpos n)]
      norm_num
    rw [mul_add, ← mul_assoc, h1]
  rwa [heq] at hmul

end Commons.Analysis.Asymptotic