import Mathlib

namespace Work.FIChain

theorem RhoWin2Holder34 (x : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 4 * |f m|)
      ≤ (∑ m ∈ Finset.Icc 1 x, |f m|) ^ ((1 : ℝ) / 3)
        * (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 6 * |f m|) ^ ((2 : ℝ) / 3) := by
  -- The exponent identity `(d^4)^(3/2) = d^6` for `d ≥ 0`.
  have hpow : ∀ m : ℕ, ((m.divisors.card : ℝ) ^ 4) ^ ((3 : ℝ) / 2) = (m.divisors.card : ℝ) ^ 6 := by
    intro m
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _) 4 ((3 : ℝ) / 2)]
    norm_num
  -- Weighted Hölder (Lyapunov interpolation) with weight `|f|`, function `d^4` and exponent `3/2`.
  have h := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.Icc 1 x) (p := (3 : ℝ) / 2) (by norm_num)
      (fun m => |f m|) (fun m => (m.divisors.card : ℝ) ^ 4)
      (fun m => abs_nonneg _) (fun m => by positivity)
  rw [show (1 : ℝ) - ((3 : ℝ) / 2)⁻¹ = 1 / 3 by norm_num,
    show ((3 : ℝ) / 2)⁻¹ = 2 / 3 by norm_num] at h
  -- Rewrite `|f m| * (d^4)^(3/2)` as `d^6 * |f m|`.
  have hsum : (∑ m ∈ Finset.Icc 1 x, |f m| * ((m.divisors.card : ℝ) ^ 4) ^ ((3 : ℝ) / 2))
      = ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 6 * |f m| := by
    apply Finset.sum_congr rfl
    intro m _
    rw [hpow m, mul_comm]
  rw [hsum] at h
  calc (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 4 * |f m|)
      = ∑ m ∈ Finset.Icc 1 x, |f m| * ((m.divisors.card : ℝ)) ^ 4 := by
        apply Finset.sum_congr rfl
        intro m _
        ring
    _ ≤ _ := h

end Work.FIChain
