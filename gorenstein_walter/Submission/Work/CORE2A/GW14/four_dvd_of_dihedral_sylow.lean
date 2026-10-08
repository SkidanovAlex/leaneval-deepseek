import Mathlib

namespace Work.CORE2A.GW14

theorem four_dvd_of_dihedral_sylow {G : Type} [Group G] [Finite G] (S : Subgroup G)
    (hpg : IsPGroup 2 S) (n : ℕ) (hiso : Nonempty (S ≃* DihedralGroup n))
    (h8 : 8 ≤ Nat.card S) : 4 ∣ n ∧ 3 ≤ n := by
  -- Extract the isomorphism and compute the order of `S` as `2 * n`.
  obtain ⟨e⟩ := hiso
  have hcard : Nat.card S = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  -- `S` is a finite 2-group, so its order is a power of `2`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hpg : ∃ k, Nat.card S = 2 ^ k)
  have hkn : 2 * n = 2 ^ k := by rw [← hcard, hk]
  -- Since `8 ≤ Nat.card S = 2^k`, we have `k ≥ 3`.
  have hk3 : 3 ≤ k := by
    have hle : 2 ^ 3 ≤ 2 ^ k := by rw [← hkn, ← hcard]; norm_num; exact h8
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  constructor
  · -- `8 ∣ 2 * n`, hence `4 ∣ n`.
    have h8dvd : 8 ∣ 2 * n := by
      rw [hkn]
      have h := pow_dvd_pow (2 : ℕ) hk3
      rwa [show (2 : ℕ) ^ 3 = 8 from by norm_num] at h
    rw [show (8 : ℕ) = 2 * 4 from by norm_num] at h8dvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 2)).mp h8dvd
  · -- `2 * n ≥ 8` gives `n ≥ 4 ≥ 3`.
    omega

end Work.CORE2A.GW14
