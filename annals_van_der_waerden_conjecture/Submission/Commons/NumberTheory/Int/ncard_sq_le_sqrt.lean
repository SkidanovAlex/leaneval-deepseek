import Mathlib

namespace Commons.NumberTheory.Int

/-- The number of integers whose square is at most `T` is at most `2 √T + 1`. -/
theorem ncard_sq_le_sqrt (T : ℕ) :
    (({x : ℤ | x ^ 2 ≤ (T : ℤ)} : Set ℤ)).ncard ≤ 2 * Nat.sqrt T + 1 := by
  set s : ℕ := Nat.sqrt T with hs
  have hmem : ∀ x : ℤ, x ∈ ({x : ℤ | x ^ 2 ≤ (T : ℤ)} : Set ℤ) ↔
      x ∈ (Finset.Icc (-(s : ℤ)) (s : ℤ) : Set ℤ) := by
    intro x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Icc, ← abs_le]
    constructor
    · intro hx
      by_contra hcon
      push_neg at hcon
      have h1 : (s : ℤ) + 1 ≤ |x| := by omega
      have h2 : ((s : ℤ) + 1) ^ 2 ≤ |x| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      rw [sq_abs] at h2
      have h3 : ((s : ℤ) + 1) ^ 2 ≤ (T : ℤ) := le_trans h2 hx
      have h4 : (((s + 1) ^ 2 : ℕ) : ℤ) ≤ (T : ℤ) := by
        have hcast : (((s + 1) ^ 2 : ℕ) : ℤ) = ((s : ℤ) + 1) ^ 2 := by push_cast; ring
        rw [hcast]; exact h3
      have h5 : (s + 1) ^ 2 ≤ T := Int.ofNat_le.mp h4
      have h6 : T < (s + 1) ^ 2 := by
        rw [hs]; simpa using Nat.lt_succ_sqrt' T
      omega
    · intro hab
      have h2 : (|x| : ℤ) ^ 2 ≤ ((s : ℤ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg x) hab 2
      have hs2 : ((s : ℤ)) ^ 2 = ((s ^ 2 : ℕ) : ℤ) := by push_cast; ring
      have hsT : (s ^ 2 : ℕ) ≤ T := by
        rw [hs]; exact Nat.sqrt_le' T
      rw [← sq_abs]
      calc (|x| : ℤ) ^ 2 ≤ ((s : ℤ)) ^ 2 := h2
        _ = ((s ^ 2 : ℕ) : ℤ) := hs2
        _ ≤ (T : ℤ) := by exact_mod_cast hsT
  have hS : ({x : ℤ | x ^ 2 ≤ (T : ℤ)} : Set ℤ) =
      (Finset.Icc (-(s : ℤ)) (s : ℤ) : Set ℤ) := Set.ext hmem
  rw [hS, Set.ncard_coe_finset, Int.card_Icc]
  have hc : (s : ℤ) + 1 - (-(s : ℤ)) = ((2 * s + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hc, Int.toNat_natCast]

end Commons.NumberTheory.Int
