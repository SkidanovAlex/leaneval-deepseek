import Mathlib
import Submission.Work.DSTR.M110.frobeniusRingAut

namespace Work.DSTR.M110

theorem frobeniusInvolutionEq (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0)
    (σ : GaloisField p k ≃+* GaloisField p k)
    (hσ2 : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ 1) :
    ∃ m : ℕ, k = 2 * m ∧ ∀ x : GaloisField p k, σ x = x ^ (p ^ m) := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  -- Every ring automorphism of `GF(p^k)` is a Frobenius power `x ↦ x ^ (p ^ i)`.
  obtain ⟨i, hi_lt, hi_apply, hi_order⟩ := frobeniusRingAut p k hk1 σ
  -- `σ` is an involution which is not the identity, so it has order `2` in `RingAut`.
  have hσsq : σ ^ 2 = 1 := by
    rw [pow_two]
    ext x
    exact hσ2 x
  have horder : orderOf σ = 2 := orderOf_eq_prime hσsq hσ1
  -- Hence `k / gcd i k = 2`, and setting `d = gcd i k` we get `k = 2 * d`.
  set d := Nat.gcd i k with hd_def
  have hd : k / d = 2 := by rw [← hi_order]; exact horder
  have hdvdk : d ∣ k := Nat.gcd_dvd_right i k
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right i (Nat.pos_of_ne_zero hk)
  have hk2 : k = 2 * d := by
    have h := (Nat.mul_div_cancel' hdvdk).symm
    rw [h, hd]; ring
  -- Write `i = d * j`; since `i < k = 2 * d` and `d > 0` we get `j < 2`, so `j ∈ {0,1}`.
  obtain ⟨j, hj⟩ : ∃ j, i = d * j := Nat.gcd_dvd_left i k
  have hilt2 : j < 2 := by
    have h1 : i < d * 2 := by omega
    have h2 : d * j < d * 2 := by rw [← hj]; exact h1
    exact (Nat.mul_lt_mul_left hdpos).mp h2
  have hid : i = d := by
    have hj01 : j = 0 ∨ j = 1 := by omega
    rcases hj01 with h | h
    · -- `j = 0` would force `i = 0`, i.e. `σ = 1`, contradicting `hσ1`.
      exfalso
      apply hσ1
      have hi0 : i = 0 := by rw [hj, h]; ring
      ext x
      rw [hi_apply x, hi0]
      simp
    · rw [hj, h]; ring
  exact ⟨d, hk2, fun x => by rw [hi_apply x, hid]⟩

end Work.DSTR.M110
