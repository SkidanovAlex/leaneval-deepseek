import Mathlib
import Submission.Work.Hering.AppVIII.frobPowOfFourth
import Submission.Work.Higman.Family

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Elementary field facts about `GF(2ⁿ)` used in Appendix VIII

* `x ^ (2 ^ n) = x`: the Frobenius power `n` is the identity on `GF(2ⁿ)`;
* `x ^ (2 ^ (k + n)) = x ^ (2 ^ k)`: the dependence of `x ↦ x ^ (2 ^ k)` on `k` is `n`-periodic;
* `x ↦ x ^ (2 ^ k)` is a bijection of `GF(2ⁿ)`;
* `√x = x ^ (2 ^ (n-1))`;
* `x ↦ x ^ (2 ^ s + 1)` is a bijection of `GF(2 ^ (2s+1))` (the map `x ↦ x·θ(x)` with
  `θ = x ↦ x ^ (2^s)`).
-/

set_option autoImplicit false

namespace Work.Hering.AppVIII

open Work.Higman

theorem pow_two_pow_card (n : ℕ) (hn : 0 < n) (x : GaloisField 2 n) : x ^ (2 ^ n) = x := by
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (Nat.pos_iff_ne_zero.mp hn)
  rw [← hcard]
  exact FiniteField.pow_card x

theorem pow_two_pow_add_card (n k : ℕ) (hn : 0 < n) (x : GaloisField 2 n) :
    x ^ (2 ^ (k + n)) = x ^ (2 ^ k) := by
  rw [pow_add, pow_mul]
  exact pow_two_pow_card n hn (x ^ 2 ^ k)

theorem bijective_pow_two_pow (n k : ℕ) :
    Function.Bijective (fun x : GaloisField 2 n => x ^ (2 ^ k)) := by
  have hfun : (fun x : GaloisField 2 n => x ^ (2 ^ k)) =
      ⇑((frobeniusEquiv (GaloisField 2 n) 2) ^ k) := by
    funext x
    exact (frobeniusEquiv_pow_apply n k x).symm
  rw [hfun]
  exact ((frobeniusEquiv (GaloisField 2 n) 2) ^ k).bijective

theorem sqrtF_eq_pow (n : ℕ) (hn : 0 < n) (x : GaloisField 2 n) :
    sqrtF (GaloisField 2 n) x = x ^ (2 ^ (n - 1)) := by
  show (frobeniusEquiv (GaloisField 2 n) 2).symm x = x ^ (2 ^ (n - 1))
  have horder : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n := by
    have h := Work.Higman.orderOf_frobeniusEquiv_pow n 1 hn
    simpa using h
  have hnpow : (frobeniusEquiv (GaloisField 2 n) 2) ^ n = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [horder])
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have h1 : (frobeniusEquiv (GaloisField 2 n) 2) ^ (n - 1) * (frobeniusEquiv (GaloisField 2 n) 2)
      = 1 := by
    rw [← pow_succ, hn1]
    exact hnpow
  have h2 : (frobeniusEquiv (GaloisField 2 n) 2)⁻¹ * (frobeniusEquiv (GaloisField 2 n) 2) = 1 :=
    inv_mul_cancel _
  have hpow : (frobeniusEquiv (GaloisField 2 n) 2) ^ (n - 1) =
      (frobeniusEquiv (GaloisField 2 n) 2)⁻¹ :=
    mul_right_cancel (h1.trans h2.symm)
  change ((frobeniusEquiv (GaloisField 2 n) 2)⁻¹) x = x ^ (2 ^ (n - 1))
  rw [← hpow]
  exact frobeniusEquiv_pow_apply n (n - 1) x

/-- `x ↦ x ^ (2 ^ s + 1) = x·θ(x)` is a bijection of `GF(2 ^ (2s+1))`: for `y ≠ 0` the
preimage is `(y ^ (2 ^ (s+1) - 2))⁻¹`, because `(2 ^ s + 1) * (2 ^ (s+1) - 2) = 2 ^ (2s+1) - 2`. -/
theorem surjective_pow_two_pow_add_one (s : ℕ) :
    Function.Surjective (fun x : GaloisField 2 (2 * s + 1) => x ^ (2 ^ s + 1)) := by
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp⟩
  · refine ⟨(y ^ (2 ^ (s + 1) - 2))⁻¹, ?_⟩
    have hN : y ^ (2 ^ (2 * s + 1) - 1) = 1 := by
      haveI : Fintype (GaloisField 2 (2 * s + 1)) := Fintype.ofFinite _
      have hcard : Fintype.card (GaloisField 2 (2 * s + 1)) = 2 ^ (2 * s + 1) := by
        rw [← Nat.card_eq_fintype_card]
        exact GaloisField.card 2 (2 * s + 1) (by omega)
      have := FiniteField.pow_card_sub_one_eq_one y hy
      rw [hcard] at this
      simpa using this
    have harith : (2 ^ s + 1) * (2 ^ (s + 1) - 2) = 2 ^ (2 * s + 1) - 2 := by
      have hle1 : 2 ≤ 2 ^ (s + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hle2 : 2 ≤ 2 ^ (2 * s + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      zify [hle1, hle2]
      ring
    have h3 : 2 ^ (2 * s + 1) - 2 + 1 = 2 ^ (2 * s + 1) - 1 := by
      have hle2 : 2 ≤ 2 ^ (2 * s + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have key : y ^ (2 ^ (2 * s + 1) - 2) * y = 1 := by
      rw [← pow_succ, h3, hN]
    have hfin : (y ^ (2 ^ (2 * s + 1) - 2))⁻¹ = y := inv_eq_of_mul_eq_one_right key
    have hpow : ((y ^ (2 ^ (s + 1) - 2))⁻¹) ^ (2 ^ s + 1) = (y ^ (2 ^ (2 * s + 1) - 2))⁻¹ := by
      have hmul : (2 ^ (s + 1) - 2) * (2 ^ s + 1) = 2 ^ (2 * s + 1) - 2 :=
        (Nat.mul_comm _ _).trans harith
      rw [← inv_pow, ← pow_mul, inv_pow, hmul]
    show ((y ^ (2 ^ (s + 1) - 2))⁻¹) ^ (2 ^ s + 1) = y
    rw [hpow, hfin]

end Work.Hering.AppVIII
