import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

theorem exists_pow_order_prime {G : Type} [Group G] {x : G} {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hx : x ≠ 1) (hdvd : orderOf x ∣ p ^ m) :
    ∃ x₀ : G, x₀ ∈ Subgroup.zpowers x ∧ orderOf x₀ = p ∧ x₀ ^ p = 1 ∧ x₀ ≠ 1 := by
  have _hm : 1 ≤ m := hm
  -- The order of `x` divides `p ^ m`, hence it is a power of the prime `p`.
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  -- Since `x ≠ 1` the order is not `1 = p ^ 0`, so `k ≠ 0`.
  have hk_ne : k ≠ 0 := by
    intro h
    apply hx
    rw [← orderOf_eq_one_iff, hk, h, pow_zero]
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne
  -- `orderOf x = p ^ (j + 1) = p ^ j * p`
  have hord : orderOf x = p ^ j * p := by
    rw [hk, hj, pow_succ]
  -- The desired element `x₀` is the `(p ^ j)`-th power of `x`.
  have hx0_pow : (x ^ (p ^ j)) ^ p = 1 := by
    rw [← pow_mul, ← hord, pow_orderOf_eq_one]
  have hx0_ne : x ^ (p ^ j) ≠ 1 := by
    intro hcontra
    have hd : orderOf x ∣ p ^ j := orderOf_dvd_iff_pow_eq_one.mpr hcontra
    rw [hord] at hd
    have hle : p ^ j * p ≤ p ^ j := Nat.le_of_dvd (pow_pos hp.pos j) hd
    have hlt : p ^ j < p ^ j * p := by
      simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt (pow_pos hp.pos j)
    exact absurd hlt (not_lt.mpr hle)
  have hx0_ord : orderOf (x ^ (p ^ j)) = p := by
    have hd : orderOf (x ^ (p ^ j)) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx0_pow
    rcases hp.eq_one_or_self_of_dvd (orderOf (x ^ (p ^ j))) hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx0_ne
    · exact h
  exact ⟨x ^ (p ^ j), Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) (p ^ j),
    hx0_ord, hx0_pow, hx0_ne⟩

end Work.ThmF.ChV3.Prove
