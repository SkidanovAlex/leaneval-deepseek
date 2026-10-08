import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.BenderST
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.ThmF.ChV12.exists_k_normalizing
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.lemma2a
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.Reductions.OddResidual
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageA

/-! ## Auxiliary: the `2`-elements lie in `O^{2'}` -/

/-- An element of `2`-power order lies in `O^{2'}` (= `oddResidual`, the intersection of the
normal subgroups of odd index). -/
theorem mem_oddResidual_of_pow_two_eq_one {L : Type} [Group L] [Finite L] {x : L} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ Submission.Blueprint.oddResidual L := by
  induction k generalizing x with
  | zero =>
      rw [pow_zero, pow_one] at hx
      rw [hx]
      exact Subgroup.one_mem _
  | succ k ih =>
      have h2 : (x * x) ^ 2 ^ k = 1 := by
        rw [← pow_two, ← pow_mul, ← pow_succ', hx]
      exact Work.Reductions.mem_oddResidual_of_mul_self_mem (ih h2)

/-- A `2`-subgroup is contained in `O^{2'}`. -/
theorem le_oddResidual_of_isPGroup {L : Type} [Group L] [Finite L] {S : Subgroup L}
    (hS : IsPGroup 2 S) : S ≤ Submission.Blueprint.oddResidual L := by
  intro x hx
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  refine mem_oddResidual_of_pow_two_eq_one (k := k) ?_
  have hdvd : orderOf x ∣ 2 ^ k := by
    have h1 : orderOf (⟨x, hx⟩ : S) ∣ Nat.card S := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hk] at h1
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

/-- An element whose order is a power of `2` lies in `O^{2'}`. -/
theorem mem_oddResidual_of_orderOf_eq_two_pow {L : Type} [Group L] [Finite L] {x : L}
    {k : ℕ} (hx : orderOf x = 2 ^ k) : x ∈ Submission.Blueprint.oddResidual L :=
  mem_oddResidual_of_pow_two_eq_one (k := k) (by rw [← hx, pow_orderOf_eq_one])

/-- An element of `2`-power order lies in every normal subgroup of odd index. -/
theorem mem_of_pow_two_eq_one_of_normal_odd_index {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [hN : N.Normal] (hodd : Odd N.index) {x : G} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hx, map_one]
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    rw [Subgroup.index_eq_card]; exact orderOf_dvd_natCard _
  obtain ⟨j, -, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h3 : 2 ^ j ∣ N.index := hje ▸ h2
  have hj0 : j = 0 := by
    by_contra hj
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have h2dvd : 2 ∣ N.index := by
      refine dvd_trans ?_ h3
      rw [ht, pow_succ]; exact dvd_mul_left 2 _
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  have hone : orderOf (QuotientGroup.mk' N x) = 1 := by rw [hje, hj0, pow_zero]
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hone)

/-- An element of `2`-power order lies in every normal subgroup of odd index. -/
theorem mem_of_orderOf_eq_two_pow_of_normal_odd_index {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [hN : N.Normal] (hodd : Odd N.index) {x : G} {k : ℕ}
    (hx : orderOf x = 2 ^ k) : x ∈ N :=
  mem_of_pow_two_eq_one_of_normal_odd_index hodd (by rw [← hx, pow_orderOf_eq_one])

/-- The order of an element of a `2`-subgroup is a power of `2`. -/
theorem exists_orderOf_eq_two_pow_of_mem_isPGroup {G : Type} [Group G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q) : ∃ k, orderOf x = 2 ^ k := by
  obtain ⟨k, hk⟩ := hQ (⟨x, hx⟩ : ↥Q)
  have hdvd : orderOf (⟨x, hx⟩ : ↥Q) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  obtain ⟨j, -, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨j, (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥Q)).symm ▸ hje⟩

/-- An element of `C` of `2`-power order lies in the image of `O^{2'}(C)` in `G`. -/
theorem mem_map_oddResidual_of_pow_eq_one {G : Type} [Group G] [Finite G]
    {C : Subgroup G} {x : G} (hx : x ∈ C) {k : ℕ} (h : x ^ 2 ^ k = 1) :
    x ∈ (Submission.Blueprint.oddResidual C).map C.subtype := by
  refine Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : ↥C), ?_, rfl⟩
  exact mem_oddResidual_of_pow_two_eq_one (x := (⟨x, hx⟩ : ↥C)) (by
    apply Subtype.ext
    simpa using h)

/-- Variant of `mem_map_oddResidual_of_pow_eq_one` with an order hypothesis. -/
theorem mem_map_oddResidual_of_orderOf_eq_two_pow {G : Type} [Group G] [Finite G]
    {C : Subgroup G} {x : G} (hx : x ∈ C) {k : ℕ} (h : orderOf x = 2 ^ k) :
    x ∈ (Submission.Blueprint.oddResidual C).map C.subtype :=
  mem_map_oddResidual_of_pow_eq_one hx (by rw [← h, pow_orderOf_eq_one])

/-- An element of `C` inside a `2`-subgroup `Q` lies in the image of `O^{2'}(C)` in `G`. -/
theorem mem_map_oddResidual_of_mem_isPGroup {G : Type} [Group G] [Finite G]
    {Q C : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q) (hxC : x ∈ C) :
    x ∈ (Submission.Blueprint.oddResidual C).map C.subtype := by
  obtain ⟨k, hk⟩ := hQ (⟨x, hx⟩ : ↥Q)
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg (fun g : ↥Q => (g : G)) hk
    simpa using this
  exact mem_map_oddResidual_of_pow_eq_one hxC hk'

/-- The centre of a finite group lies in every strongly embedded subgroup: a central element
`z ∉ H` would give `H ⊓ H^z = H` of odd order, contradicting `H` even. -/
theorem center_le_of_isStronglyEmbedded {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) : Subgroup.center G ≤ H := by
  intro z hz
  by_contra hzH
  have hodd := hH.2.2 z hzH
  have hle : H ≤ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) H := by
    intro x hx
    refine ⟨z⁻¹ * x * z, ?_, ?_⟩
    · have hcomm : x * z = z * x := (Subgroup.mem_center_iff.mp hz) x
      have hzx : z⁻¹ * x * z = x := by
        rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hzx]; exact hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hconj : H ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) H = H :=
    inf_eq_left.mpr hle
  rw [hconj] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hH.2.1

end Work.PSU3.StageA
