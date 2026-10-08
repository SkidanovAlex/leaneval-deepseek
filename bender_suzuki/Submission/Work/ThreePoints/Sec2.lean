/-
# `Work.ThreePoints.Sec2` — Peterfalvi I Ch. I §2: involutions and two-point stabilisers

* Prop. 1 (a): if two involutions `s`, `t` have no common fixed point in `Ω = G ⧸ H`, then `s * t`
  has odd order, and `s` and `t` are conjugate by an involution of `⟨s, t⟩`;
* Prop. 1 (b): the involutions of `G` form a single conjugacy class, and `Inv(H)` is a single
  `H`-class;
* Prop. 1 (c), Prop. 2, Lemma 1, Lemma 2.
-/
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-! ## Elementary order-two API -/

/-- An element of order `2` is an involution. -/
theorem mul_self_eq_one_of_orderOf_eq_two {x : G} (h : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← h]
  exact pow_orderOf_eq_one x

/-- Conversely. -/
theorem orderOf_eq_two_of {x : G} (h1 : x ≠ 1) (h2 : x * x = 1) : orderOf x = 2 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
  rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf x) hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

/-- **Peterfalvi I Ch. I §2 Prop. 1 (a), first assertion.**  Two involutions `s`, `t` without a
common fixed point in `Ω = G ⧸ H` have a product of odd order. -/
theorem odd_orderOf_mul [Finite G] {H : Subgroup G} (h : IsStronglyEmbedded H) {s t : G}
    (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hsep : ∀ ω : G ⧸ H, s • ω = ω → t • ω ≠ ω) : Odd (orderOf (s * t)) := by
  classical
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hs2 : s * s = 1 := mul_self_eq_one_of_orderOf_eq_two hs
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  set x : G := s * t with hx
  have hxpos : 0 < orderOf x := by
    by_contra hcon
    have h0 : orderOf x = 0 := Nat.eq_zero_of_not_pos hcon
    have hd := orderOf_dvd_natCard x
    rw [h0] at hd
    exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd hd)
  obtain ⟨k, hk⟩ := heven
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, add_zero] at hk
      exact absurd (hk ▸ hxpos) (Nat.lt_irrefl 0)
    · exact hkpos
  set u : G := x ^ k with hu
  have hxk_mul : x ^ k * x ^ k = 1 := by
    rw [← pow_add, show k + k = orderOf x from hk.symm, pow_orderOf_eq_one]
  have hu_mul : u * u = 1 := by simpa [hu] using hxk_mul
  have hu_ne : u ≠ 1 := by
    intro h1
    have h1' : x ^ k = 1 := by rw [← hu]; exact h1
    have hdvd : orderOf x ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1'
    rw [hk] at hdvd
    have hle : k + k ≤ k := Nat.le_of_dvd hkpos hdvd
    omega
  have hu2 : orderOf u = 2 := orderOf_eq_two_of hu_ne hu_mul
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hsx : MulAut.conj s x = x⁻¹ := by
    have hA : s * (s * t) * s⁻¹ = t * s := by rw [← mul_assoc, hs2, one_mul, hsinv]
    have hB : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, htinv, hsinv]
    rw [mulAut_conj_apply, hx, hA, hB]
  have htx : MulAut.conj t x = x⁻¹ := by
    have hA : t * (s * t) * t⁻¹ = t * s := by group
    have hB : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, htinv, hsinv]
    rw [mulAut_conj_apply, hx, hA, hB]
  have hsu : MulAut.conj s u = u := by
    rw [hu, map_pow, hsx, inv_pow, inv_eq_of_mul_eq_one_right hxk_mul]
  have htu : MulAut.conj t u = u := by
    rw [hu, map_pow, htx, inv_pow, inv_eq_of_mul_eq_one_right hxk_mul]
  have hcomm_su : s * u = u * s := by
    rw [mulAut_conj_apply] at hsu
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [hsu]
  have hcomm_tu : t * u = u * t := by
    rw [mulAut_conj_apply] at htu
    calc t * u = (t * u * t⁻¹) * t := by group
      _ = u * t := by rw [htu]
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp (ncard_fixedPts_zpowers h hu2)
  have hωmem : ω ∈ fixedPts H (Subgroup.zpowers u) := by rw [hω]; exact rfl
  have hωu : u • ω = ω := (mem_fixedPts.mp hωmem) u (Subgroup.mem_zpowers u)
  have hsω : s • ω = ω := by
    have hmem : s • ω ∈ fixedPts H (Subgroup.zpowers u) := by
      rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      rw [smul_smul, ← hcomm_su, mul_smul, hωu]
    rw [hω] at hmem
    simpa using hmem
  have htω : t • ω = ω := by
    have hmem : t • ω ∈ fixedPts H (Subgroup.zpowers u) := by
      rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      rw [smul_smul, ← hcomm_tu, mul_smul, hωu]
    rw [hω] at hmem
    simpa using hmem
  exact hsep ω hsω htω

end Work.ThreePoints
