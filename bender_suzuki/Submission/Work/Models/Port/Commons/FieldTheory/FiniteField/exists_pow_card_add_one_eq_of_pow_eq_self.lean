import Mathlib.Algebra.Order.Ring.Star
import Mathlib.FieldTheory.Finite.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.FieldTheory.FiniteField

/-- For `n ≥ 1`, the integers `2 ^ n + 1` and `2 ^ n - 1` are coprime. -/
theorem nat_coprime_two_pow_add_one_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n + 1) (2 ^ n - 1) := by
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd hp (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hcop2 : Nat.Coprime 2 (2 ^ n - 1) := Nat.coprime_two_left.mpr hodd
  have h := (Nat.coprime_add_self_left (m := 2) (n := 2 ^ n - 1)).mpr hcop2
  rwa [show 2 + (2 ^ n - 1) = 2 ^ n + 1 from by omega] at h

theorem exists_pow_card_add_one_eq_of_pow_eq_self {n : ℕ} (hn : 1 ≤ n)
    {y : GaloisField 2 (2 * n)} (hy : y ^ (2 ^ n) = y) :
    ∃ b : GaloisField 2 (2 * n), b ^ (2 ^ n + 1) = y := by
  have hcop : Nat.Coprime (2 ^ n + 1) (2 ^ n - 1) := nat_coprime_two_pow_add_one_sub_one hn
  by_cases hy0 : y = 0
  · refine ⟨0, ?_⟩
    rw [hy0, zero_pow (by positivity : 2 ^ n + 1 ≠ 0)]
  · let u : (GaloisField 2 (2 * n))ˣ := Units.mk0 y hy0
    have hu : (u : GaloisField 2 (2 * n)) = y := Units.val_mk0 hy0
    have hpu : u ^ (2 ^ n) = u := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hu, hy]
    have h1 : u ^ (2 ^ n - 1) = 1 := by
      have key : u ^ (2 ^ n - 1) * u = 1 * u := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow), hpu, one_mul]
      exact mul_right_cancel key
    have hdvd : orderOf u ∣ 2 ^ n - 1 := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hcopu : Nat.Coprime (orderOf u) (2 ^ n + 1) := (hcop.coprime_dvd_right hdvd).symm
    have hgcd : (Nat.card (Subgroup.zpowers u)).gcd (2 ^ n + 1) = 1 := by
      rw [Nat.card_zpowers]
      exact hcopu
    let a : Subgroup.zpowers u := ⟨u, Subgroup.mem_zpowers u⟩
    let t : ℕ := (((2 ^ n + 1 : ℕ) : ZMod (Nat.card (Subgroup.zpowers u)))⁻¹).val
    have hkey : (a ^ t) ^ (2 ^ n + 1) = a := pow_zmod_val_inv_pow hgcd a
    have hw : (((a ^ t : Subgroup.zpowers u) : (GaloisField 2 (2 * n))ˣ)) ^ (2 ^ n + 1) = u := by
      have := congrArg (fun z : Subgroup.zpowers u => (z : (GaloisField 2 (2 * n))ˣ)) hkey
      simpa using this
    refine ⟨(((a ^ t : Subgroup.zpowers u) : (GaloisField 2 (2 * n))ˣ) : GaloisField 2 (2 * n)), ?_⟩
    rw [← Units.val_pow_eq_pow_val, hw, hu]

end Commons.FieldTheory.FiniteField