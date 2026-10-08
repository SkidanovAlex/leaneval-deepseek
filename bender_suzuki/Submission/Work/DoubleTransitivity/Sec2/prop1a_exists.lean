import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Alg.exists_involution_conjugating

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.DoubleTransitivity.Sec2

open Submission.Blueprint

/-- **Peterfalvi I §2 Prop. 1(a), oddness half.**  If two involutions `s` and `t` of a finite
group `G` fix no common point of `Ω = G ⧸ H` for a Bender subgroup `H`, then `s * t` has odd
order.

Indeed, if `orderOf (s * t) = 2k` then `z = (s * t)^k` is an involution of `G`; since
`(s * t)^k` is fixed by conjugation with `s` (which inverts `s * t`) and with `t`, the element
`z` commutes with `s` and with `t`.  Let `ω` be the unique fixed point of `z` on `Ω`
(Peterfalvi I §1 (10)(a), `Sec1.unique_fixed`); commuting with `z` it is carried by `s` to
another fixed point of `z`, hence is itself fixed by `s`, and likewise by `t`.  Thus `s` and `t`
share the fixed point `ω`, contradiction. -/
private theorem odd_orderOf_mul_of_no_common_fixed {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsBender H) {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hst : ¬ ∃ ω : Omega H, s • ω = ω ∧ t • ω = ω) :
    Odd (orderOf (s * t)) := by
  classical
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨k, hk⟩ := hodd
  set r : G := s * t with hr
  have hn : orderOf r = k + k := by rw [hr]; exact hk
  have hkpos : 0 < k := by
    have := orderOf_pos r
    rw [hn] at this
    omega
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- Conjugation by `s` (resp. `t`) inverts the rotation `r = s * t`.
  have hsr : s * r * s⁻¹ = r⁻¹ := by
    rw [hr]
    calc s * (s * t) * s⁻¹ = t * s⁻¹ := by rw [← mul_assoc, hs2, one_mul]
      _ = t * s := by rw [hsinv]
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, hsinv, htinv]
  have htr : t * r * t⁻¹ = r⁻¹ := by
    rw [hr]
    calc t * (s * t) * t⁻¹ = t * s := by rw [htinv, ← mul_assoc, mul_assoc, ht2, mul_one]
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, hsinv, htinv]
  -- `z = r ^ k` is an involution.
  have hzk_mul : r ^ k * r ^ k = 1 := by
    rw [← pow_add, ← hn, pow_orderOf_eq_one]
  have hzk_inv : (r ^ k)⁻¹ = r ^ k := inv_eq_of_mul_eq_one_right hzk_mul
  have hz2 : (r ^ k) ^ 2 = 1 := by rw [pow_two]; exact hzk_mul
  have hz1 : r ^ k ≠ 1 := by
    intro h
    have hdvd : orderOf r ∣ k := by
      rw [orderOf_dvd_iff_pow_eq_one]; exact h
    rw [hn] at hdvd
    have hle := Nat.le_of_dvd hkpos hdvd
    omega
  have hzord : orderOf (r ^ k) = 2 := orderOf_eq_prime hz2 hz1
  -- `z` commutes with `s` and with `t`.
  have hsz : s * r ^ k * s⁻¹ = r ^ k := by
    rw [← conj_pow, hsr, inv_pow, hzk_inv]
  have htz : t * r ^ k * t⁻¹ = r ^ k := by
    rw [← conj_pow, htr, inv_pow, hzk_inv]
  have hszc : s * r ^ k = r ^ k * s := by
    have h := congrArg (· * s) hsz
    simpa [mul_assoc] using h
  have htzc : t * r ^ k = r ^ k * t := by
    have h := congrArg (· * t) htz
    simpa [mul_assoc] using h
  obtain ⟨ω_z, hωz, huniq⟩ := Sec1.unique_fixed hH hzord
  have hsfix : s • ω_z = ω_z := by
    apply huniq
    rw [← mul_smul, ← hszc, mul_smul, hωz]
  have htfix : t • ω_z = ω_z := by
    apply huniq
    rw [← mul_smul, ← htzc, mul_smul, hωz]
  exact hst ⟨ω_z, hsfix, htfix⟩

/-- **Peterfalvi I §2 Prop. 1(a).**  Let `H` be a Bender subgroup of the finite group `G`, and let
`s`, `t` be involutions of `G` that fix no common point of `Ω = G ⧸ H` (i.e. that lie in no
common conjugate of `H`).  Then the "reflection" `u = s (s t)^j` of the dihedral group generated
by `s` and `t` conjugates `s` to `t`: it is an involution in `⟨s, t⟩` with `u⁻¹ s u = t`, and
(again because `s` and `t` share no fixed point) `u` and `s` fix no common point of `Ω`. -/
theorem prop1a_exists {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsBender H)
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hst : ¬ ∃ ω : Omega H, s • ω = ω ∧ t • ω = ω) :
    ∃ u : G, orderOf u = 2 ∧ u⁻¹ * s * u = t ∧ u ∈ Subgroup.closure ({s, t} : Set G) ∧
      ¬ ∃ ω : Omega H, u • ω = ω ∧ s • ω = ω := by
  obtain ⟨u, hu2, hconj, hu_mem⟩ :=
    Alg.exists_involution_conjugating hs ht (odd_orderOf_mul_of_no_common_fixed hH hs ht hst)
  refine ⟨u, hu2, hconj, hu_mem, ?_⟩
  rintro ⟨ω, huω, hsω⟩
  have huω' : u⁻¹ • ω = ω := by
    have h := congrArg (fun x => u⁻¹ • x) huω
    rw [inv_smul_smul] at h
    exact h.symm
  have htfix : t • ω = ω := by
    rw [← hconj]
    simp only [mul_smul, huω, hsω, huω']
  exact hst ⟨ω, hsω, htfix⟩

end Work.DoubleTransitivity.Sec2
