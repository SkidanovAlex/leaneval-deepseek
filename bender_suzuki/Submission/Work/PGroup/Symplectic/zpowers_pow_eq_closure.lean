import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup.Symplectic

theorem zpowers_pow_eq_closure {G : Type*} [Group G] {a : G} {p m i : ℕ} (hp : p.Prime)
    (ho : orderOf a = p ^ m) (hi : i ≤ m) :
    Subgroup.zpowers (a ^ p ^ (m - i)) =
      Subgroup.closure {x : G | x ∈ Subgroup.zpowers a ∧ x ^ p ^ i = 1} := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hne : (p : ℤ) ^ i ≠ 0 := pow_ne_zero i hpz
  have hpinj : (p : ℤ) ^ (m - i) * (p : ℤ) ^ i = (p : ℤ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    apply Subgroup.subset_closure
    constructor
    · rw [Subgroup.mem_zpowers_iff]
      exact ⟨(p ^ (m - i) : ℕ), zpow_natCast a (p ^ (m - i))⟩
    · rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hi, ← ho]
      exact pow_orderOf_eq_one a
  · rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx.1
    have hkpi : (a ^ k) ^ (p ^ i) = 1 := by rw [hk]; exact hx.2
    have hzp : a ^ (k * ((p ^ i : ℕ) : ℤ)) = 1 := by
      rw [zpow_mul, zpow_natCast]
      exact hkpi
    have hdvd : (p : ℤ) ^ m ∣ k * (p : ℤ) ^ i := by
      have h := orderOf_dvd_iff_zpow_eq_one.mpr hzp
      rw [ho] at h
      simpa [Nat.cast_pow] using h
    have hmain : (p : ℤ) ^ (m - i) ∣ k := by
      have h1 : (p : ℤ) ^ (m - i) * (p : ℤ) ^ i ∣ k * (p : ℤ) ^ i := by
        rw [hpinj]; exact hdvd
      exact (Int.mul_dvd_mul_iff_right hne).mp h1
    obtain ⟨q, hq⟩ := hmain
    refine Subgroup.mem_zpowers_iff.mpr ⟨q, ?_⟩
    rw [← hk, hq, zpow_mul, ← zpow_natCast a (p ^ (m - i)), Nat.cast_pow]

end Work.PGroup.Symplectic
