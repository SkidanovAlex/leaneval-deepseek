import Mathlib

namespace Work.WilC4

theorem mul_pow_toNat_eq_iff {M : Type} [Field M] {x t : M} (hx : x ≠ 0) (p : ℤ) (n : ℕ) :
    t ^ n * x ^ (-p).toNat = x ^ p.toNat ↔ t ^ n = x ^ p := by
  have h : x ^ p = x ^ p.toNat / x ^ (-p).toNat := by
    calc x ^ p = x ^ ((p.toNat : ℤ) - ((-p).toNat : ℤ)) := by rw [Int.toNat_sub_toNat_neg]
      _ = x ^ (p.toNat : ℤ) / x ^ ((-p).toNat : ℤ) := zpow_sub₀ hx _ _
      _ = x ^ p.toNat / x ^ (-p).toNat := by rw [zpow_natCast, zpow_natCast]
  rw [h, eq_div_iff (pow_ne_zero _ hx)]

end Work.WilC4
