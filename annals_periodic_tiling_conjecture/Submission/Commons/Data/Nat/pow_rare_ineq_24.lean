import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Data.Nat

/-- Exponential dominates the linear term: `3 * 2^14 * t < 2^t` for `t ≥ 24`. -/
private lemma two_pow_gt_linear_24 : ∀ t : ℕ, 24 ≤ t → 3 * 2 ^ 14 * t < 2 ^ t := by
  have hstep : ∀ n : ℕ, 24 ≤ n → 3 * 2 ^ 14 * n < 2 ^ n → 3 * 2 ^ 14 * (n + 1) < 2 ^ (n + 1) := by
    intro n hn hlt
    have hinc : 3 * 2 ^ 14 ≤ 2 ^ n := by
      have h16 : 16 ≤ n := by omega
      have h1 : 3 * 2 ^ 14 ≤ 2 ^ 16 := by norm_num
      exact le_trans h1 (Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) h16)
    have hadd : 3 * 2 ^ 14 * n + 3 * 2 ^ 14 < 2 ^ n + 2 ^ n := by
      exact Nat.add_lt_add_of_lt_of_le hlt hinc
    have hcalc : 3 * 2 ^ 14 * (n + 1) = 3 * 2 ^ 14 * n + 3 * 2 ^ 14 := by ring
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [pow_succ]
      ring
    rw [hcalc, hpow]
    exact hadd
  intro t ht
  refine Nat.le_induction ?base ?succ t ht
  · norm_num
  · intro n hn ih
    exact hstep n hn ih

lemma pow_rare_ineq_24 : ∀ t : ℕ, 24 ≤ t →
    3 * t * 128 * 2 ^ (3 * t + 5) < (2 ^ (2 * t) - 7) * (2 ^ (2 * t) - 7) := by
  intro t ht
  have hlin : 3 * 2 ^ 14 * t < 2 ^ t := two_pow_gt_linear_24 t ht
  have h7le : 7 ≤ 2 ^ (2 * t) := by
    calc
      7 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) (by omega)
  -- Cast both sides of the goal into ℝ, where the arithmetic is straightforward.
  have hL : (((3 * t * 128 * 2 ^ (3 * t + 5) : ℕ) : ℝ) =
      3 * (t : ℝ) * 128 * (2 : ℝ) ^ (3 * t + 5)) := by
    norm_num [Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  have hRhs : ((((2 ^ (2 * t) - 7) * (2 ^ (2 * t) - 7) : ℕ) : ℝ) =
      ((2 : ℝ) ^ (2 * t) - 7) ^ 2) := by
    have hsub : ((2 ^ (2 * t) - 7 : ℕ) : ℝ) = (2 : ℝ) ^ (2 * t) - 7 := by
      rw [Nat.cast_sub h7le]
      norm_num
    rw [Nat.cast_mul, hsub]
    ring
  have hmain : 3 * (t : ℝ) * 128 * (2 : ℝ) ^ (3 * t + 5) < ((2 : ℝ) ^ (2 * t) - 7) ^ 2 := by
    let x : ℝ := (2 : ℝ) ^ t
    have hX2 : (2 : ℝ) ^ (2 * t) = x ^ 2 := by
      calc
        (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ (t * 2) := by congr 1; ring
        _ = ((2 : ℝ) ^ t) ^ 2 := by rw [pow_mul]
        _ = x ^ 2 := rfl
    have hX5 : (2 : ℝ) ^ (3 * t + 5) = 32 * x ^ 3 := by
      rw [pow_add]
      have h : (2 : ℝ) ^ (3 * t) = ((2 : ℝ) ^ t) ^ 3 := by
        calc
          (2 : ℝ) ^ (3 * t) = (2 : ℝ) ^ (t * 3) := by congr 1; ring
          _ = ((2 : ℝ) ^ t) ^ 3 := by rw [pow_mul]
      rw [h]
      norm_num
      ring
    rw [hX5, hX2]
    change 3 * (t : ℝ) * 128 * (32 * x ^ 3) < (x ^ 2 - 7) ^ 2
    have hlinR : 3 * (2 : ℝ) ^ 14 * (t : ℝ) < x := by
      dsimp [x]
      exact_mod_cast hlin
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hx3 : 0 < x ^ 3 := pow_pos hxpos 3
    have hx2 : 14 ≤ x ^ 2 := by
      have h16 : (16 : ℝ) ≤ x := by
        dsimp [x]
        calc
          (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
          _ ≤ (2 : ℝ) ^ t := by
            apply pow_le_pow_right₀
            · norm_num
            · omega
      have hge : (16 : ℝ) * 16 ≤ x ^ 2 := by
        nlinarith [h16]
      nlinarith
    -- x^2 ≥ 14 gives (x^2 - 7)^2 ≥ x^4 / 4, while the linear bound
    -- 3 * 2^14 * t < x gives 3*t*4096*x^3 < x^4 / 4 = (3*t*128*(32*x^3)) * 4 < x^4.
    nlinarith [hlinR, hx2, hx3]
  -- Convert the real inequality back to the natural-number statement.
  have hR : (((3 * t * 128 * 2 ^ (3 * t + 5) : ℕ) : ℝ) <
      (((2 ^ (2 * t) - 7) * (2 ^ (2 * t) - 7) : ℕ) : ℝ)) := by
    rw [hL, hRhs]
    exact hmain
  exact (Nat.cast_lt (α := ℝ)).mp hR

end Commons.Data.Nat