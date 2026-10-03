import Mathlib

namespace Work.FatouCH.Cont

theorem GeomGrowthChain {u : ℕ → ℝ} {C A : ℝ} {N : ℕ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    (h0 : u 0 ≤ A) (hstep : ∀ i < N, u (i + 1) ≤ C * u i) :
    ∀ i ≤ N, u i ≤ A * C ^ i := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro i hi
  induction i with
  | zero => simpa using h0
  | succ k ih =>
    have hkN : k < N := Nat.lt_of_succ_le hi
    have hk : u k ≤ A * C ^ k := ih (Nat.le_of_lt hkN)
    calc u (k + 1) ≤ C * u k := hstep k hkN
      _ ≤ C * (A * C ^ k) := mul_le_mul_of_nonneg_left hk hC0
      _ = A * C ^ (k + 1) := by rw [pow_succ]; ring

end Work.FatouCH.Cont
