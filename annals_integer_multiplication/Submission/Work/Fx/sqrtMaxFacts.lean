import Mathlib
import Submission.Work.Fx.scaleCommon

namespace Work.Fx

/-- The two arithmetic facts about `b = max (2^p) (⌊√a⌋+1)` (with `a = X*X + Y*Y` as a natural)
needed by the scaling word: `2^p ≤ b` and `b² > X² + Y²`.  (`⌊√a⌋+1 > √a` because
`Nat.sqrt a ≤ √a`; the `2^p` branch also gives `> √a` since there `2^p ≥ ⌊√a⌋+1`.) -/
theorem sqrtMaxFacts (p : ℕ) (X Y : ℤ) :
    let a : ℕ := (X * X + Y * Y).toNat
    let b : ℤ := max ((2 : ℤ) ^ p) ((Nat.sqrt a : ℤ) + 1)
    (2 : ℤ) ^ p ≤ b ∧ ((b : ℝ)) ^ 2 > (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 := by
  let a : ℕ := (X * X + Y * Y).toNat
  let b : ℤ := max ((2 : ℤ) ^ p) ((Nat.sqrt a : ℤ) + 1)
  change (2 : ℤ) ^ p ≤ b ∧ ((b : ℝ)) ^ 2 > (X : ℝ) ^ 2 + (Y : ℝ) ^ 2
  -- `b` dominates the lower bound `⌊√a⌋ + 1`, which is nonnegative.
  have hb_ge : ((Nat.sqrt a : ℤ) + 1 : ℝ) ≤ (b : ℝ) := by
    have h : ((Nat.sqrt a : ℤ) + 1) ≤ b := le_max_right _ _
    exact_mod_cast h
  have hs_nonneg : (0 : ℝ) ≤ ((Nat.sqrt a : ℤ) + 1 : ℝ) := by
    have h : (0:ℤ) ≤ (Nat.sqrt a : ℤ) + 1 := by
      have := Int.natCast_nonneg (Nat.sqrt a); linarith
    exact_mod_cast h
  have hb_ge_sq : (((Nat.sqrt a : ℤ) + 1 : ℝ)) ^ 2 ≤ (b : ℝ) ^ 2 :=
    pow_le_pow_left₀ hs_nonneg hb_ge 2
  constructor
  · exact le_max_left _ _
  · by_cases hpos : (0:ℤ) ≤ X * X + Y * Y
    · -- `X² + Y² = a < (⌊√a⌋+1)² ≤ b²`.
      have haZ : (a : ℤ) = X * X + Y * Y := Int.toNat_of_nonneg hpos
      have haR : (a : ℝ) = (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 := by
        have h : (a : ℝ) = ((X * X + Y * Y : ℤ) : ℝ) := by exact_mod_cast haZ
        rw [h]; push_cast; ring
      have hlt : (a:ℝ) < (((Nat.sqrt a : ℤ) + 1 : ℝ)) ^ 2 := by
        have h0 : a < (Nat.sqrt a + 1) ^ 2 := by
          simpa [pow_two] using Nat.lt_succ_sqrt a
        have h1 : (a:ℝ) < ((Nat.sqrt a + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h0
        simpa using h1
      calc (X:ℝ)^2 + (Y:ℝ)^2 = (a:ℝ) := haR.symm
        _ < (((Nat.sqrt a : ℤ) + 1 : ℝ))^2 := hlt
        _ ≤ (b:ℝ)^2 := hb_ge_sq
    · -- Here `X*X + Y*Y ≤ 0`, so `X = Y = 0`, `a = 0` and `b ≥ 1 > 0`.
      have hle : X * X + Y * Y ≤ 0 := le_of_lt (not_le.mp hpos)
      have ha0 : a = 0 := Int.toNat_of_nonpos hle
      have hX : X = 0 := by
        have hsum : X*X + Y*Y = 0 := le_antisymm hle (add_nonneg (mul_self_nonneg X) (mul_self_nonneg Y))
        have h1 : X*X ≤ 0 := by have h2 := mul_self_nonneg Y; linarith
        exact mul_self_eq_zero.mp (le_antisymm h1 (mul_self_nonneg X))
      have hY : Y = 0 := by
        have hsum : X*X + Y*Y = 0 := le_antisymm hle (add_nonneg (mul_self_nonneg X) (mul_self_nonneg Y))
        have h1 : Y*Y ≤ 0 := by have h2 := mul_self_nonneg X; linarith
        exact mul_self_eq_zero.mp (le_antisymm h1 (mul_self_nonneg Y))
      have hsq : ((Nat.sqrt a : ℤ) + 1 : ℝ) = 1 := by
        rw [ha0]; norm_num
      have hb1 : (1:ℝ) ≤ (b:ℝ) := by
        calc (1:ℝ) = ((Nat.sqrt a : ℤ) + 1 : ℝ) := hsq.symm
          _ ≤ (b:ℝ) := hb_ge
      have htarget : (X:ℝ)^2 + (Y:ℝ)^2 = 0 := by rw [hX, hY]; norm_num
      have h1 : (1:ℝ) ≤ (b:ℝ)^2 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hb1 2
        simpa using this
      rw [htarget]; linarith

end Work.Fx
