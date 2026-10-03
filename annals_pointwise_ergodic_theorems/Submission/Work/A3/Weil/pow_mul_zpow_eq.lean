import Mathlib

namespace Work.A3.Weil

/-- Bookkeeping identity used in the Weil/complete-sum estimates: with `d = k + 1` the
factor `N^{2^k} · (q⁻¹ + N⁻¹ + q·N^{-d})` (which arises from expanding a product of a
main term and a `q`-normalised error term) rewrites as
`N^{2^k - 1} + N^{2^k - 1 - k}·q + N^{2^k}/q`.

Note `hq : 1 ≤ q` and `hk : 1 ≤ k` are not needed for the identity itself; they are kept
because the statement is used under those hypotheses downstream. -/
theorem pow_mul_zpow_eq {k d : ℕ} (hkd : k + 1 = d) (hk : 1 ≤ k) {N q : ℕ} (hN : 1 ≤ N)
    (hq : 1 ≤ q) :
    (N : ℝ) ^ (2 ^ k) * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ)))
      = (N : ℝ) ^ (2 ^ k - 1) + (N : ℝ) ^ (2 ^ k - 1 - k) * (q : ℝ) + (N : ℝ) ^ (2 ^ k) / (q : ℝ) := by
  subst hkd
  have hNne : (N:ℝ) ≠ 0 := by
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one this)
  have hge : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))
  have h1 : (N:ℝ)^(2^k) * (q:ℝ)⁻¹ = (N:ℝ)^(2^k) / (q:ℝ) := (div_eq_mul_inv _ _).symm
  have h2 : (N:ℝ)^(2^k) * (N:ℝ)⁻¹ = (N:ℝ)^(2^k - 1) := by
    simpa using (pow_sub₀ (N:ℝ) hNne (Nat.one_le_two_pow (n := k))).symm
  have h3 : (N:ℝ)^(2^k) * ((q:ℝ) * (N:ℝ)^(-(((k+1:ℕ) : ℤ)))) = (N:ℝ)^(2^k - 1 - k) * (q:ℝ) := by
    have hpowneg : (N:ℝ)^(-(((k+1:ℕ):ℤ))) = ((N:ℝ)^(k+1))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have hsub : 2 ^ k - (k + 1) = 2 ^ k - 1 - k := by
      rw [Nat.sub_sub, Nat.add_comm 1 k]
    calc (N:ℝ)^(2^k) * ((q:ℝ) * (N:ℝ)^(-(((k+1:ℕ):ℤ))))
        = (q:ℝ) * ((N:ℝ)^(2^k) * ((N:ℝ)^(k+1))⁻¹) := by rw [hpowneg]; ring
      _ = (q:ℝ) * (N:ℝ)^(2^k - (k+1)) := by
            rw [pow_sub₀ (N:ℝ) hNne hge]
      _ = (q:ℝ) * (N:ℝ)^(2^k - 1 - k) := by rw [hsub]
      _ = (N:ℝ)^(2^k - 1 - k) * (q:ℝ) := by ring
  calc
    (N:ℝ)^(2^k) * ((q:ℝ)⁻¹ + (N:ℝ)⁻¹ + (q:ℝ) * (N:ℝ)^(-(((k+1:ℕ) : ℤ))))
        = (N:ℝ)^(2^k) * (q:ℝ)⁻¹ + (N:ℝ)^(2^k) * (N:ℝ)⁻¹
            + (N:ℝ)^(2^k) * ((q:ℝ) * (N:ℝ)^(-(((k+1:ℕ) : ℤ)))) := by ring
    _ = (N:ℝ)^(2^k) / (q:ℝ) + (N:ℝ)^(2^k - 1)
            + (N:ℝ)^(2^k - 1 - k) * (q:ℝ) := by rw [h1, h2, h3]
    _ = (N:ℝ)^(2^k - 1) + (N:ℝ)^(2^k - 1 - k) * (q:ℝ) + (N:ℝ)^(2^k) / (q:ℝ) := by ring

end Work.A3.Weil
