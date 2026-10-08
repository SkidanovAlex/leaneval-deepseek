import Mathlib
import Submission.Work.RED.Basic

namespace Work.RED

open Subgroup

open scoped commutatorElement

set_option linter.style.haveILetI false

theorem MNF_commute_of_minimalNormalIn (G : Type*) [Group G] [Finite G] (N K K' : Subgroup G)
    (hN : Work.RED.GW2.IsMinimalNormal N) (hK : Work.RED.GW2.IsMinimalNormalIn N K)
    (hK' : Work.RED.GW2.IsMinimalNormalIn N K') (hne : K ≠ K') :
    K ⊓ K' = ⊥ ∧ ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
  have _ := hN
  have hKnormal : (K.subgroupOf N).Normal := hK.normal
  have hK'normal : (K'.subgroupOf N).Normal := hK'.normal
  have hKle : K ≤ N := hK.le
  have hK'le : K' ≤ N := hK'.le
  -- `K ⊓ K'` is a normal subgroup of `↥N`.
  have hinf_normal : ((K ⊓ K').subgroupOf N).Normal := by
    have h : (K ⊓ K').subgroupOf N = (K.subgroupOf N) ⊓ (K'.subgroupOf N) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h]
    haveI : (K.subgroupOf N).Normal := hKnormal
    haveI : (K'.subgroupOf N).Normal := hK'normal
    exact Subgroup.normal_inf_normal _ _
  -- If `K ⊓ K' = K` then `K ≤ K'`, and minimality of `K'` forces `K = K'`.
  have hne_inf : K ⊓ K' ≠ K := by
    intro hEq
    have hle : K ≤ K' := by rw [← hEq]; exact inf_le_right
    exact hne (hK'.minimal K hle hKnormal hK.ne_bot)
  have hbot : K ⊓ K' = ⊥ := by
    by_contra h
    exact hne_inf (hK.minimal (K ⊓ K') inf_le_left hinf_normal h)
  refine ⟨hbot, ?_⟩
  -- Both `K` and `K'` normalize each other, hence `⁅K, K'⁆ ≤ K ⊓ K' = ⊥`.
  have hNormK : N ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := N) hKle).mp hKnormal
  have hNormK' : N ≤ Subgroup.normalizer (K' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K') (K := N) hK'le).mp hK'normal
  have h1 : ⁅K, K'⁆ ≤ K :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := K') (K := K)).mp (hK'le.trans hNormK)
  have h2 : ⁅K, K'⁆ ≤ K' :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := K) (K := K')).mp (hKle.trans hNormK')
  have hcomm : ⁅K, K'⁆ = ⊥ := by
    have hle : ⁅K, K'⁆ ≤ (⊥ : Subgroup G) := by
      have hle' : ⁅K, K'⁆ ≤ K ⊓ K' := le_inf h1 h2
      rwa [hbot] at hle'
    exact le_bot_iff.mp hle
  intro x hx y hy
  have hmem : ⁅x, y⁆ = 1 := by
    have hle : ⁅K, K'⁆ ≤ (⊥ : Subgroup G) := by rw [hcomm]
    have hx' : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := (Subgroup.commutator_le.mp hle) x hx y hy
    simpa using hx'
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

end Work.RED
