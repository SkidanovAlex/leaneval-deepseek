import Mathlib
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O^{2'}` API

`Submission.Blueprint.oddResidual G = sInf {N : Subgroup G | N.Normal ∧ Odd N.index}` is the
smallest normal subgroup of odd index (Peterfalvi's `O^{2'}(G)`).  This module records the
elementary API used throughout `Work.ThreePoints.P3Sub`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-- The intersection of two normal subgroups of odd index has odd index. -/
theorem odd_index_inf {H K : Subgroup G} (hH : H.Normal) (hK : K.Normal)
    (hHi : Odd H.index) (hKi : Odd K.index) : Odd (H ⊓ K).index := by
  haveI := hH
  haveI := hK
  -- `[G : H ⊓ K] = [G : H] · [H : H ⊓ K]`
  have h1 : (H ⊓ K).index = H.index * (H ⊓ K).relIndex H := by
    have h := Subgroup.relIndex_mul_index (show H ⊓ K ≤ H from inf_le_left)
    rw [mul_comm] at h
    exact h.symm
  -- `[H : H ⊓ K] = [H ⊔ K : K]` (second isomorphism theorem)
  have h2 : (H ⊓ K).relIndex H = K.relIndex (H ⊔ K) := by
    rw [Subgroup.relIndex_sup_right H K]
    show ((H ⊓ K).subgroupOf H).index = (K.subgroupOf H).index
    congr 1
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨x.2, h⟩
  -- `[H ⊔ K : K]` divides `[G : K]`
  have h4 : (H ⊓ K).relIndex H ∣ K.index := by
    rw [h2]
    have h := Subgroup.relIndex_mul_index (show K ≤ H ⊔ K from le_sup_right)
    exact ⟨(H ⊔ K).index, h.symm⟩
  rw [h1]
  exact hHi.mul (hKi.of_dvd_nat h4)

/-- Membership in `sInf` a set of subgroups. -/
theorem mem_sInf_set {S : Set (Subgroup G)} {x : G} :
    x ∈ sInf S ↔ ∀ N ∈ S, x ∈ N := Subgroup.mem_sInf

theorem oddResidual_basic {G : Type} [Group G] [Finite G] :
    (Submission.Blueprint.oddResidual G).Normal ∧
      Odd (Submission.Blueprint.oddResidual G).index ∧
      (∀ N : Subgroup G, N.Normal → Odd N.index → Submission.Blueprint.oddResidual G ≤ N) ∧
      (∀ x : G, x * x = 1 → x ∈ Submission.Blueprint.oddResidual G) := by
  classical
  set S : Set (Subgroup G) := {N | N.Normal ∧ Odd N.index} with hSdef
  have htop : (⊤ : Subgroup G) ∈ S :=
    ⟨Subgroup.normal_top, by rw [Subgroup.index_top]; exact odd_one⟩
  have hfin : S.Finite := Set.toFinite S
  -- a finite subfamily has an infimum in `S`
  have key : ∀ U : Finset (Subgroup G), (∀ N ∈ U, N ∈ S) →
      (U.inf id).Normal ∧ Odd (U.inf id).index := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
        intro _
        rw [Finset.inf_empty]
        exact ⟨Subgroup.normal_top, by rw [Subgroup.index_top]; exact odd_one⟩
    | insert a U ha ih =>
        intro hU
        have haS : a ∈ S := hU a (Finset.mem_insert_self a U)
        have hUS : ∀ N ∈ U, N ∈ S := fun N hN => hU N (Finset.mem_insert_of_mem hN)
        obtain ⟨hnorm, hodd⟩ := ih hUS
        rw [Finset.inf_insert]
        haveI : a.Normal := haS.1
        haveI : (U.inf id).Normal := hnorm
        show (a ⊓ U.inf id).Normal ∧ Odd (a ⊓ U.inf id).index
        exact ⟨inferInstance, odd_index_inf haS.1 hnorm haS.2 hodd⟩
  -- `S` is the range of `T`, so `sInf S = T.inf id`
  have hEq : sInf S = hfin.toFinset.inf id := by
    refine le_antisymm ?_ ?_
    · rw [Finset.inf_eq_iInf]
      refine le_iInf fun N => le_iInf fun hN => sInf_le ?_
      exact hfin.mem_toFinset.mp hN
    · refine le_sInf fun N hN => ?_
      exact Finset.inf_le (f := id) (hfin.mem_toFinset.mpr hN)
  have hmem : sInf S ∈ S := by
    rw [hEq]
    exact key hfin.toFinset (fun N hN => hfin.mem_toFinset.mp hN)
  rw [oddResidual]
  refine ⟨hmem.1, hmem.2, ?_, ?_⟩
  · intro N hN hNi
    exact sInf_le (show N ∈ S from ⟨hN, hNi⟩)
  · intro x hx
    haveI : (sInf S).Normal := hmem.1
    have hpow : x ^ (sInf S).index ∈ sInf S := Subgroup.pow_index_mem _ x
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
    obtain ⟨k, hk⟩ := hmem.2
    have hxid : x ^ (sInf S).index = x := by
      rw [hk, pow_add, pow_mul, hx2, one_pow, one_mul, pow_one]
    rw [← hxid]
    exact hpow

end Work.ThreePoints
