import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.GL32

theorem inf_zpowers_eq_bot_of_coprime {G : Type*} [Group G] (a b : G) {m n : ℕ}
    (ha : a ^ m = 1) (hb : b ^ n = 1) (h : Nat.Coprime m n) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  -- Every element of the intersection is a power of both `a` and `b`, so its
  -- order divides both `m` and `n`, hence divides `gcd m n = 1`, hence it is `1`.
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxa, hxb⟩ := hx
  -- write `x = a ^ i` for some integer `i`
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxa
  rw [← hi] at hxb ⊢
  -- and `a ^ i = b ^ j` for some integer `j`
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxb
  have hm : orderOf (a ^ i) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast (a ^ i) m, ← zpow_mul a i (m : ℤ), zpow_mul' a i (m : ℤ),
        zpow_natCast a m, ha, one_zpow])
  have hn : orderOf (a ^ i) ∣ n :=
    orderOf_dvd_of_pow_eq_one (by
      rw [← hj, ← zpow_natCast (b ^ j) n, ← zpow_mul b j (n : ℤ), zpow_mul' b j (n : ℤ),
        zpow_natCast b n, hb, one_zpow])
  exact orderOf_eq_one_iff.mp
    (Nat.dvd_one.mp (by rw [← h.gcd_eq_one]; exact Nat.dvd_gcd hm hn))

end Work.Hering.GL32
