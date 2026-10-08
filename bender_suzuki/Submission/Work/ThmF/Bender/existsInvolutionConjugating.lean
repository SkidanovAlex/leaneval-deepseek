import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Bender

/-!
# Two involutions with an odd-order product are conjugate

If `s` and `t` are involutions (`orderOf s = orderOf t = 2`) and the product `s * t` has odd
order `m`, then `s` and `t` are conjugate, and moreover the conjugating element can be chosen
to be an involution.

## The construction

Put `a = s * t` and `m = orderOf a` (odd).  Since `a⁻¹ = t s` and `s² = t² = 1` one has

`(*)`  `s * a * s = a⁻¹`

i.e. `a` is inverted by `s`.  Let `k = (m+1)/2`, so `2k = m+1` and hence, using `a^m = 1`,

`a ^ k * a ^ k = a`  and  `(a ^ k)⁻¹ * (a ^ k)⁻¹ = a⁻¹`.

The element `u = s * a ^ k` is the required involution:

* `u * u = (s aᵏ s) aᵏ = (aᵏ)⁻¹ aᵏ = 1`, because `s aᵏ s = (s a s)ᵏ = (a⁻¹)ᵏ = (aᵏ)⁻¹` (conjugation
  by `s` sends `a ^ j` to `(a ^ j)⁻¹` by `(*)`);
* `u ≠ 1` because otherwise `s = (aᵏ)⁻¹ ∈ ⟨a⟩` would have odd order, contradicting `orderOf s = 2`;
* `u * s * u⁻¹ = (s aᵏ s) (aᵏ)⁻¹ s = (aᵏ)⁻¹ (aᵏ)⁻¹ s = a⁻¹ s = t`.

-/

open LeanEval.GroupTheory.Defs in theorem existsInvolutionConjugating {G : Type*} [Group G] {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2) (hodd : Odd (orderOf (s * t))) : ∃ u : G, orderOf u = 2 ∧ u * s * u⁻¹ = t := by
  -- `s` and `t` are involutions.
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s; rw [hs] at h; simpa [pow_two] using h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht] at h; simpa [pow_two] using h
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  -- `a = s * t`, whose order `m` is odd.
  set a : G := s * t with ha
  have hodd_a : Odd (orderOf a) := by rw [ha]; exact hodd
  obtain ⟨n, hn⟩ := hodd_a
  -- `k = (m + 1) / 2`, written as `n + 1` with `m = 2 n + 1`.
  let k : ℕ := n + 1
  have h2k : 2 * k = orderOf a + 1 := by dsimp [k]; omega
  have ham : a ^ orderOf a = 1 := pow_orderOf_eq_one a
  -- `(*)`: `s` inverts `a`.
  have hsa : s * a * s = a⁻¹ := by
    rw [ha, mul_inv_rev, hs_inv, ht_inv]
    rw [← mul_assoc s s t, hs2, one_mul]
  -- Conjugation by `s` (an involution) sends `a ^ m` to `(a ^ m)⁻¹`.
  have hconj : ∀ m : ℕ, s * a ^ m * s = (s * a * s) ^ m := by
    intro m
    have h := map_pow (MulAut.conj s) a m
    rw [MulAut.conj_apply] at h
    simpa [hs_inv] using h
  have hconj_k : s * a ^ k * s = (a ^ k)⁻¹ := by
    rw [hconj k, hsa, inv_pow]
  -- `u = s * a ^ k` is an involution.
  have hu2 : (s * a ^ k) * (s * a ^ k) = 1 := by
    calc (s * a ^ k) * (s * a ^ k)
        = (s * a ^ k * s) * a ^ k := by simp only [mul_assoc]
      _ = (a ^ k)⁻¹ * a ^ k := by rw [hconj_k]
      _ = 1 := inv_mul_cancel _
  have hu_ne : s * a ^ k ≠ 1 := by
    intro h1
    have hs_eq : s = (a ^ k)⁻¹ := (inv_eq_of_mul_eq_one_left h1).symm
    have ho : orderOf s = orderOf (a ^ k) := by rw [hs_eq, orderOf_inv]
    have hdvd : orderOf (a ^ k) ∣ orderOf a := orderOf_pow_dvd k
    have h2dvd : 2 ∣ orderOf a := by
      rw [← ho, hs] at hdvd
      exact hdvd
    exact Nat.not_even_iff_odd.mpr ⟨n, hn⟩ (even_iff_two_dvd.mpr h2dvd)
  have horderu : orderOf (s * a ^ k) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hu2
    · exact hu_ne
  -- `a ^ k * a ^ k = a`, hence `(a ^ k)⁻¹ * (a ^ k)⁻¹ = a⁻¹`.
  have hkk : a ^ k * a ^ k = a := by
    rw [← pow_add]
    have hk2 : k + k = orderOf a + 1 := by omega
    rw [hk2, pow_succ, ham, one_mul]
  have hu_inv : (s * a ^ k)⁻¹ = (a ^ k)⁻¹ * s := by
    rw [mul_inv_rev, hs_inv]
  have hfinal : (s * a ^ k) * s * (s * a ^ k)⁻¹ = a⁻¹ * s := by
    rw [hu_inv, hconj_k]
    rw [← mul_assoc, ← mul_inv_rev, hkk]
  have htarget : a⁻¹ * s = t := by
    rw [ha, mul_inv_rev, hs_inv, ht_inv, mul_assoc, hs2, mul_one]
  exact ⟨s * a ^ k, horderu, hfinal.trans htarget⟩

end Work.ThmF.Bender
