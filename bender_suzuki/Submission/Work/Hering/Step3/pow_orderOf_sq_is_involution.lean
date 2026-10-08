import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step3

theorem pow_orderOf_sq_is_involution {G : Type*} [Group G] [Finite G] {P : Subgroup G} {x : G}
    (hxP : x ∉ P) (hx2 : x ^ 2 ∈ P) (hP : Odd (Nat.card P)) :
    orderOf (x ^ orderOf (x ^ 2)) = 2 ∧ (x ^ orderOf (x ^ 2))⁻¹ * x ∈ P := by
  -- Write `n` for the order of `x ^ 2`.
  set n := orderOf (x ^ 2) with hn
  -- `n` divides the order of `P`, because `x ^ 2 ∈ P`.
  have hdvd : n ∣ Nat.card P := by
    have h := orderOf_dvd_natCard (⟨x ^ 2, hx2⟩ : P)
    simpa only [Subgroup.orderOf_mk] using h
  -- Hence `n` is odd, since `P` has odd order.
  have hn_odd : Odd n := by
    obtain ⟨c, hc⟩ := hdvd
    have : Odd (n * c) := by rw [← hc]; exact hP
    exact (Nat.odd_mul.mp this).1
  -- Write `n = 2 * k + 1` and set `z = (x ^ 2) ^ k ∈ P`.
  obtain ⟨k, hk⟩ := hn_odd
  set z := (x ^ 2) ^ k with hz
  have hzP : z ∈ P := P.pow_mem hx2 k
  -- Then `x ^ n = x * z`.
  have hy : x ^ n = x * z := by
    rw [hk, hz, pow_succ', pow_mul]
  -- `(x ^ n) ^ 2 = (x ^ 2) ^ n = 1`.
  have hy2 : (x ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm n 2, pow_mul, hn, pow_orderOf_eq_one]
  -- `x ^ n ≠ 1`, since otherwise `x = z⁻¹ ∈ P`, contradicting `x ∉ P`.
  have hy_ne : x ^ n ≠ 1 := by
    intro h
    rw [hy] at h
    have hx : x = z⁻¹ := eq_inv_of_mul_eq_one_left h
    exact hxP (by rw [hx]; exact P.inv_mem hzP)
  -- `(x ^ n)⁻¹ * x = z⁻¹ ∈ P`.
  have hmem : (x ^ n)⁻¹ * x ∈ P := by
    have heq : (x ^ n)⁻¹ * x = z⁻¹ := by
      rw [hy, hz, mul_inv_rev]
      simp
    rw [heq]
    exact P.inv_mem hzP
  -- `(x ^ n) ^ 2 = 1` and `x ^ n ≠ 1` give `orderOf (x ^ n) = 2`.
  have hord : orderOf (x ^ n) = 2 := by
    have hdvd2 : orderOf (x ^ n) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
    have hne1 : orderOf (x ^ n) ≠ 1 := by
      intro h
      rw [orderOf_eq_one_iff] at h
      exact hy_ne h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact absurd h hne1
    · exact h
  exact ⟨hord, hmem⟩

end Work.Hering.Step3
