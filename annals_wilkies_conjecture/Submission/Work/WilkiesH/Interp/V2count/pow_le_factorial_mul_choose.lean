import Mathlib

namespace Work.WilkiesH.Interp.V2count

theorem pow_le_factorial_mul_choose (n d : ℕ) :
    (d + 1) ^ n ≤ n.factorial * (n + d).choose n := by
  -- The key Mathlib estimate: `(m + 1 - k)^k ≤ m.descFactorial k`.
  -- Applying it with `m = n + d` and `k = n` gives `(d + 1)^n ≤ (n + d).descFactorial n`,
  -- and `descFactorial` equals `k! * choose` (definition of the binomial coefficient).
  have h := Nat.pow_sub_le_descFactorial (n + d) n
  have hnd : n + d + 1 - n = d + 1 := by omega
  rw [hnd] at h
  rwa [Nat.descFactorial_eq_factorial_mul_choose] at h

end Work.WilkiesH.Interp.V2count
