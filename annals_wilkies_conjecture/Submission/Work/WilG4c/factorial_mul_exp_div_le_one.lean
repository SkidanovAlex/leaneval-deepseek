import Mathlib

namespace Work.WilG4c

/-- Arithmetic of the rescaling: if `(1 + exp S) * (r + 1) ≤ lam` and `1 ≤ m ≤ r` then
`m! * exp S / lam ^ m ≤ 1`. -/
theorem factorial_mul_exp_div_le_one {m r : ℕ} (S lam : ℝ) (hS : 0 ≤ S)
    (hlam : (1 + Real.exp S) * (r + 1) ≤ lam) (hm : 1 ≤ m) (hmr : m ≤ r) :
    (m.factorial : ℝ) * Real.exp S / lam ^ m ≤ 1 := by
  have hEpos : 0 < Real.exp S := Real.exp_pos S
  have h1E : 0 < 1 + Real.exp S := by linarith
  -- `lam` is bounded below by `(1 + exp S) * (m + 1)`
  have hmr1 : m + 1 ≤ r + 1 := Nat.succ_le_succ hmr
  have hcast : ((m : ℝ) + 1) ≤ ((r : ℝ) + 1) := by exact_mod_cast hmr1
  have hL2 : (1 + Real.exp S) * ((m : ℝ) + 1) ≤ lam :=
    le_trans (mul_le_mul_of_nonneg_left hcast (le_of_lt h1E)) hlam
  -- hence `lam ^ m` dominates `(1 + exp S) ^ m * (m + 1) ^ m`
  have hpow : ((1 + Real.exp S) * ((m : ℝ) + 1)) ^ m ≤ lam ^ m :=
    pow_le_pow_left₀ (by positivity) hL2 m
  -- `m! ≤ (m + 1) ^ m`
  have hfacNat : m.factorial ≤ (m + 1) ^ m :=
    le_trans (Nat.factorial_le_pow m) (Nat.pow_le_pow_left (Nat.le_succ m) m)
  have hfac : (m.factorial : ℝ) ≤ ((m : ℝ) + 1) ^ m := by exact_mod_cast hfacNat
  -- `exp S ≤ (1 + exp S) ^ m`
  have hexp : Real.exp S ≤ (1 + Real.exp S) ^ m := by
    have hle : (1 + Real.exp S) ^ 1 ≤ (1 + Real.exp S) ^ m :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + Real.exp S) hm
    have h1 : Real.exp S ≤ (1 + Real.exp S) ^ 1 := by rw [pow_one]; linarith
    exact le_trans h1 hle
  have hJ : (m.factorial : ℝ) * Real.exp S ≤ lam ^ m := by
    calc (m.factorial : ℝ) * Real.exp S
        ≤ ((m : ℝ) + 1) ^ m * (1 + Real.exp S) ^ m := by
          apply mul_le_mul hfac hexp (le_of_lt hEpos)
          positivity
      _ = ((1 + Real.exp S) * ((m : ℝ) + 1)) ^ m := by rw [mul_pow]; ring
      _ ≤ lam ^ m := hpow
  have hLpos : 0 < lam :=
    lt_of_lt_of_le (mul_pos h1E (by exact_mod_cast Nat.succ_pos r)) hlam
  rw [div_le_one (pow_pos hLpos m)]
  exact hJ

end Work.WilG4c
