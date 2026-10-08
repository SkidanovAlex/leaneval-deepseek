import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `st` has odd order for `s` an involution of `H` and `t` an involution outside `H`

Peterfalvi I, Ch. I §1: if `H` is strongly embedded in the finite group `G` and `t ∉ H` is an
involution, then `H` contains no involution commuting with `t`; more sharply, for every
involution `s ∈ H` the product `s * t` has odd order.

Argument.  Assume `m = orderOf (s * t)` is even and put `z = (s * t)^(m / 2)`.  Since
`s (s t) s⁻¹ = (s t)⁻¹` and `t (s t) t⁻¹ = (s t)⁻¹`, the element `z` is an involution commuting
with both `s` and `t`.  Hence `s ∈ H ∩ z H z⁻¹`, so `z H z⁻¹ = H` (an involution of `H` lies in
a unique conjugate of `H`, `Work.ThmF.conj_eq_self_of_involution_mem`) and `z ∈ H`; then
`z ∈ H ∩ t H t⁻¹`, which forces `t ∈ H`, a contradiction.
-/

namespace Work.ThmF.Bender

open LeanEval.GroupTheory.Defs Submission.Blueprint in theorem twoInvolutionsOdd {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H) {s t : G} (hs : s ∈ H) (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) (htH : t ∉ H) : Odd (orderOf (s * t)) := by
  rw [← Nat.not_even_iff_odd]
  intro hEven
  set a : G := s * t with ha
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hEven
  -- `s` and `t` are involutions.
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h
    simpa [pow_two] using h
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  -- Conjugation by `s` (resp. `t`) inverts `a = s * t`.
  have hsa : s * a * s⁻¹ = a⁻¹ := by
    rw [ha, mul_inv_rev, hs_inv, ht_inv]
    calc s * (s * t) * s = (s * s) * (t * s) := by group
      _ = t * s := by rw [hss, one_mul]
  have hta : t * a * t⁻¹ = a⁻¹ := by
    rw [ha, mul_inv_rev, hs_inv, ht_inv]
    calc t * (s * t) * t = (t * s) * (t * t) := by group
      _ = t * s := by rw [htt, mul_one]
  -- `z = a ^ k` is an involution.
  have hz2 : a ^ k * a ^ k = 1 := by
    rw [← pow_add]
    have h : k + k = orderOf a := by rw [← two_mul]; exact hk.symm
    rw [h, pow_orderOf_eq_one]
  have hm_ne : orderOf a ≠ 0 := by
    intro h0
    have hdvd := orderOf_dvd_natCard a
    rw [h0, zero_dvd_iff] at hdvd
    have := Nat.card_pos (α := G)
    omega
  have hz_ne : a ^ k ≠ 1 := by
    intro hk1
    have hdvd : orderOf a ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hk1
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; exact absurd hk hm_ne
      · exact h
    have hle := Nat.le_of_dvd hk_pos hdvd
    have hlt : k < orderOf a := by rw [hk]; omega
    omega
  have hzord : orderOf (a ^ k) = 2 := by
    apply orderOf_eq_prime
    · rwa [pow_two]
    · exact hz_ne
  -- `z` commutes with `s` and with `t`.
  have key_s : s * a ^ k * s⁻¹ = a ^ k := by
    have h1 : s * a ^ k * s⁻¹ = (s * a * s⁻¹) ^ k := by
      have := map_pow (MulAut.conj s).toMonoidHom a k
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
    rw [h1, hsa, inv_pow]
    exact inv_eq_of_mul_eq_one_right hz2
  have hz_s : a ^ k * s = s * a ^ k := by
    calc a ^ k * s = s * a ^ k * s⁻¹ * s := by rw [key_s]
      _ = s * a ^ k := by group
  have key_t : t * a ^ k * t⁻¹ = a ^ k := by
    have h1 : t * a ^ k * t⁻¹ = (t * a * t⁻¹) ^ k := by
      have := map_pow (MulAut.conj t).toMonoidHom a k
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
    rw [h1, hta, inv_pow]
    exact inv_eq_of_mul_eq_one_right hz2
  have hz_t : a ^ k * t = t * a ^ k := by
    calc a ^ k * t = t * a ^ k * t⁻¹ * t := by rw [key_t]
      _ = t * a ^ k := by group
  -- An involution of `H` lies in no conjugate of `H` except itself.
  have hs_conj : s ∈ Submission.Blueprint.conj (a ^ k) H := by
    rw [Work.Models.mem_conj_iff]
    have h : (a ^ k)⁻¹ * s * (a ^ k) = s := by rw [mul_assoc, ← hz_s]; group
    rw [h]; exact hs
  have hconj1 : Submission.Blueprint.conj (a ^ k) H = H :=
    Work.ThmF.conj_eq_self_of_involution_mem hH hs hs2 hs_conj
  have hzH : a ^ k ∈ H := (Work.ThmF.conj_eq_iff_mem hH (a ^ k)).mp hconj1
  -- Applying the same statement to the commuting involution `z` and `t` gives `t ∈ H`.
  have hz_conj : a ^ k ∈ Submission.Blueprint.conj t H := by
    rw [Work.Models.mem_conj_iff]
    have h : t⁻¹ * a ^ k * t = a ^ k := by rw [mul_assoc, hz_t]; group
    rw [h]; exact hzH
  have hconj2 : Submission.Blueprint.conj t H = H :=
    Work.ThmF.conj_eq_self_of_involution_mem hH hzH hzord hz_conj
  exact htH ((Work.ThmF.conj_eq_iff_mem hH t).mp hconj2)

end Work.ThmF.Bender
