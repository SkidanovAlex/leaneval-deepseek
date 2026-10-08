import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

set_option linter.unusedVariables false

open scoped Pointwise

open LeanEval.GroupTheory.Defs Submission.Blueprint

/-- `K = J(D,t) = Kset H t` is closed under inverses. -/
private theorem Kset_inv_mem_aux {G : Type*} [Group G] {H : Subgroup G} {t : G} {x : G}
    (hx : x ∈ Kset H t) : x⁻¹ ∈ Kset H t := by
  obtain ⟨hxD, hxinv⟩ := mem_Kset_iff.mp hx
  refine mem_Kset_iff.mpr ⟨(twoPoint H t).inv_mem hxD, ?_⟩
  rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group, hxinv]

/-- Integer powers of an element of `K` lie in `K`. -/
private theorem zpow_mem_Kset_aux {G : Type*} [Group G] {H : Subgroup G} {t : G} {x : G}
    (hx : x ∈ Kset H t) (n : ℤ) : x ^ n ∈ Kset H t := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
  · rw [hm, zpow_natCast]; exact pow_mem_Kset hx m
  · rw [hm, zpow_neg, zpow_natCast]; exact Kset_inv_mem_aux (pow_mem_Kset hx m)

/- Peterfalvi II, Ch. V §1, Proposition 2 (p. 240): `K = J(D,t)` is a cyclic normal subgroup of
`D = H ∩ Hᵗ`.

The hypothesis `hAppX` collects the consequences of Appendix X applied to `D/W`: there is a
subgroup `A` with `W ≤ A ≤ D`, `⟨K⟩ W = A`, `A = ⟨k⟩ W` for some `k ∈ K`, `D' ≤ A`, and `K`
invariant under `D`.

The argument is elementary once these are available.  Since `K ⊆ ⟨K⟩ ⊆ A = ⟨k⟩ W` and every
element of `W` commutes with `k` (`W ≤ C_D(K)`) and with `t` (`W ≤ V = C_D(t)`), every `x ∈ K`
can be written `x = kⁿ·w` with `n ∈ ℤ`, `w ∈ W`.  Applying `t x t⁻¹ = x⁻¹` gives
`k⁻ⁿ w = w⁻¹ k⁻ⁿ`, hence `w = w⁻¹`; as `w ∈ D` has odd order, `w = 1`.  Thus `K ⊆ ⟨k⟩`, while
`⟨k⟩ ⊆ K` because `K` is closed under integral powers; so `K = ⟨k⟩`, which is cyclic, and
`K = ⟨K⟩` is `D`-invariant by hypothesis. -/
open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem prop2v2 {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b) (hAppX : ∃ A : Subgroup G, W H t ≤ A ∧ A ≤ twoPoint H t ∧ Ksub H t ⊔ W H t = A ∧ (∃ k : G, k ∈ Kset H t ∧ A = Subgroup.closure ({k} : Set G) ⊔ W H t) ∧ (∀ x ∈ twoPoint H t, ∀ y ∈ twoPoint H t, x * y * x⁻¹ * y⁻¹ ∈ A) ∧ (∀ d ∈ twoPoint H t, ∀ x ∈ Kset H t, d * x * d⁻¹ ∈ Kset H t)) : IsCyclic ↥(Ksub H t) ∧ (Ksub H t : Set G) = Kset H t ∧ ((Ksub H t).subgroupOf (twoPoint H t)).Normal := by
  obtain ⟨A, _hWA, _hAD, hsup, ⟨k, hkK, hAeq⟩, _hcom, hnorm⟩ := hAppX
  -- `Ksub ≤ A`.
  have hKsubA : Ksub H t ≤ A := hsup ▸ le_sup_left
  -- Every `w ∈ W` commutes with `k`.
  have hkW : ∀ w ∈ W H t, w * k = k * w := by
    intro w hw
    have hwc : w ∈ Subgroup.centralizer (Kset H t : Set G) := (Subgroup.mem_inf.mp hw).2
    exact (Subgroup.mem_centralizer_iff.mp hwc k hkK).symm
  -- `⟨k⟩` normalises `W`.
  have hkN : Subgroup.zpowers k ≤ Subgroup.normalizer (W H t : Set G) := by
    have hkC : k ∈ Subgroup.centralizer (W H t : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hkW w hw
    exact (Subgroup.zpowers_le (H := Subgroup.centralizer (W H t : Set G))).mpr hkC |>.trans
      (Subgroup.centralizer_le_normalizer (W H t : Set G))
  -- Step 1: `K ⊆ ⟨k⟩`.
  have hKset_sub : Kset H t ⊆ (Subgroup.zpowers k : Set G) := by
    intro x hx
    have hxA : x ∈ A := hKsubA (Kset_le_Ksub H t hx)
    rw [hAeq, ← Subgroup.zpowers_eq_closure k] at hxA
    have hmem : x ∈ ((Subgroup.zpowers k : Set G) * (W H t : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers k) (W H t) hkN]
      exact hxA
    rw [Set.mem_mul] at hmem
    obtain ⟨u, hu, w, hw, huw⟩ := hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu
    -- `w` commutes with `t`
    have hwcent : w ∈ Subgroup.centralizer ({t} : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hw).1).2
    have hwt : t * w = w * t := (Subgroup.mem_centralizer_iff.mp hwcent) t (by simp)
    have htw : t * w * t⁻¹ = w := by rw [hwt, mul_assoc, mul_inv_cancel, mul_one]
    -- conjugation by `t` of `k ^ n`
    have htkn : t * k ^ n * t⁻¹ = k ^ (-n) := by
      have h1 : t * k ^ n * t⁻¹ = (MulAut.conj t) (k ^ n) :=
        (MulAut.conj_apply t (k ^ n)).symm
      rw [h1, map_zpow (MulAut.conj t) k n]
      have h2 : (MulAut.conj t) k = k⁻¹ := by
        rw [MulAut.conj_apply, (mem_Kset_iff.mp hkK).2]
      rw [h2, inv_zpow, ← zpow_neg]
    -- write `x` and `x⁻¹`
    have hxe : x = k ^ n * w := by rw [← huw, ← hn]
    have hxinv : t * x * t⁻¹ = x⁻¹ := (mem_Kset_iff.mp hx).2
    have hval1 : t * x * t⁻¹ = k ^ (-n) * w := by
      rw [hxe]
      calc t * (k ^ n * w) * t⁻¹ = (t * k ^ n * t⁻¹) * (t * w * t⁻¹) := by group
        _ = k ^ (-n) * w := by rw [htkn, htw]
    have hval2 : x⁻¹ = w⁻¹ * k ^ (-n) := by
      rw [hxe, mul_inv_rev, show (k ^ n)⁻¹ = k ^ (-n) from (zpow_neg k n).symm]
    have heq : k ^ (-n) * w = w⁻¹ * k ^ (-n) := by
      rw [← hval1, hxinv, hval2]
    -- `w` commutes with `k ^ (-n)`, hence `w = w⁻¹`
    have hcomm : Commute w k := hkW w hw
    have hcomm1 : Commute w (k ^ (-n)) := hcomm.zpow_right (-n)
    have hcomm2 : Commute w⁻¹ (k ^ (-n)) := hcomm1.inv_left
    have hw_eq : w = w⁻¹ := by
      have h2 : k ^ (-n) * w = k ^ (-n) * w⁻¹ := by rw [heq, hcomm2.eq]
      exact mul_left_cancel h2
    have hw2 : w * w = 1 := (eq_inv_iff_mul_eq_one).mp hw_eq
    have hwD : w ∈ twoPoint H t := centD_le_twoPoint t (Subgroup.mem_inf.mp hw).1
    have hodd : Odd (Nat.card ↥(twoPoint H t)) := split_odd_card_twoPoint h
    have hdvd : orderOf w ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hw2
    have hoddw : Odd (orderOf w) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hwD)
    have hw1 : w = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · exfalso
        rw [h1] at hoddw
        exact Nat.not_odd_iff_even.mpr even_two hoddw
    rw [hxe, hw1, mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  -- Step 2: `⟨k⟩ ⊆ K`.
  have hzp_sub : (Subgroup.zpowers k : Set G) ⊆ Kset H t := by
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn]
    exact zpow_mem_Kset_aux hkK n
  -- Conclusion.
  have hKset_eq : (Kset H t : Set G) = (Subgroup.zpowers k : Set G) :=
    Set.Subset.antisymm hKset_sub hzp_sub
  have hKsub_eq : Ksub H t = Subgroup.zpowers k := by
    show Subgroup.closure (Kset H t) = Subgroup.zpowers k
    rw [hKset_eq, Subgroup.closure_eq]
  have hKsub_set : (Ksub H t : Set G) = Kset H t := by
    rw [hKsub_eq]; exact hKset_eq.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hKsub_eq]; exact inferInstance
  · rw [hKsub_eq]; exact hKset_eq.symm
  · exact (Subgroup.normal_subgroupOf_iff (Ksub_le_twoPoint (H := H) t)).mpr
      (fun a b ha hb => by
        have haK : a ∈ Kset H t := by
          have h1 : a ∈ (Ksub H t : Set G) := ha
          rw [hKsub_set] at h1
          exact h1
        have hb' : b * a * b⁻¹ ∈ Kset H t := hnorm b hb a haK
        have h2 : b * a * b⁻¹ ∈ (Ksub H t : Set G) := by
          rw [hKsub_set]; exact hb'
        exact h2)

end Work.ThmF.ChV12
