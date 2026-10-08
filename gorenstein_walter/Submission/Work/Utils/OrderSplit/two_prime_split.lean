import Mathlib

namespace Work.Utils.OrderSplit

/-- Every positive natural number factors as `2 ^ k` times an odd number. -/
lemma exists_two_pow_mul_odd : ∀ n : ℕ, n ≠ 0 → ∃ k m : ℕ, n = 2 ^ k * m ∧ Odd m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd n with hev | hod
    · obtain ⟨j, hj⟩ := hev
      have hjlt : j < n := by omega
      have hj0 : j ≠ 0 := by omega
      obtain ⟨k, m, hkm, hom⟩ := ih j hjlt hj0
      exact ⟨k + 1, m, by rw [hj, hkm, pow_succ]; ring, hom⟩
    · exact ⟨0, n, by simp, hod⟩

theorem two_prime_split {G : Type} [Group G] [Finite G] (x : G) :
    ∃ x2 x2' : G, x = x2 * x2' ∧ x2 ∈ Subgroup.zpowers x ∧ x2' ∈ Subgroup.zpowers x ∧
      (∃ k : ℕ, orderOf x2 = 2 ^ k) ∧ Odd (orderOf x2') := by
  have hpos : 0 < orderOf x := orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)
  obtain ⟨k, m, hkm, hmodd⟩ :=
    exists_two_pow_mul_odd (orderOf x) (Nat.pos_iff_ne_zero.mp hpos)
  -- `2 ^ k` is the 2-part of the order of `x`, and `m` is the odd part.
  have hcop : Nat.Coprime (2 ^ k) m := (Nat.coprime_two_left.mpr hmodd).pow_left k
  have hgcd : m.gcd (2 ^ k) = 1 := by
    rw [Nat.gcd_comm]
    exact hcop.gcd_eq_one
  -- Bézout: `1 = m * A + 2 ^ k * B` in `ℤ`.
  obtain ⟨A, B, hbez⟩ : ∃ A B : ℤ, (1 : ℤ) = (m : ℤ) * A + (((2 ^ k : ℕ)) : ℤ) * B := by
    refine ⟨m.gcdA (2 ^ k), m.gcdB (2 ^ k), ?_⟩
    have h := Nat.gcd_eq_gcd_ab m (2 ^ k)
    rw [hgcd] at h
    simpa using h
  have h2 : orderOf (x ^ m) ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul,
      show m * 2 ^ k = orderOf x by rw [Nat.mul_comm, ← hkm], pow_orderOf_eq_one]
  have h4 : orderOf (x ^ (2 ^ k)) ∣ m := by
    rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← hkm, pow_orderOf_eq_one]
  refine ⟨(x ^ m) ^ A, (x ^ (2 ^ k)) ^ B, ?_, ?_, ?_, ?_, ?_⟩
  · -- `x = (x ^ m) ^ A * (x ^ (2 ^ k)) ^ B`
    conv_lhs => rw [← zpow_one x]
    rw [hbez, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  · rw [Subgroup.mem_zpowers_iff]
    exact ⟨(m : ℤ) * A, by rw [zpow_mul, zpow_natCast]⟩
  · rw [Subgroup.mem_zpowers_iff]
    exact ⟨(((2 ^ k : ℕ)) : ℤ) * B, by rw [zpow_mul, zpow_natCast]⟩
  · -- the order of `(x ^ m) ^ A` divides `2 ^ k`, hence is a power of two
    have h3 : orderOf ((x ^ m) ^ A) ∣ 2 ^ k := by
      rw [← orderOf_pow_natAbs (x ^ m) A]
      exact dvd_trans (orderOf_pow_dvd (x := x ^ m) A.natAbs) h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    exact ⟨j, hj⟩
  · -- the order of `(x ^ (2 ^ k)) ^ B` divides the odd number `m`
    have h5 : orderOf ((x ^ (2 ^ k)) ^ B) ∣ m := by
      rw [← orderOf_pow_natAbs (x ^ (2 ^ k)) B]
      exact dvd_trans (orderOf_pow_dvd (x := x ^ (2 ^ k)) B.natAbs) h4
    exact Odd.of_dvd_nat hmodd h5

end Work.Utils.OrderSplit
