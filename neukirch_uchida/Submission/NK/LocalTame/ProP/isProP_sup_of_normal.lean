import Mathlib
import Submission.NK.LocalTame.Basic

/-!
# The join of two normal pro-`p` subgroups is pro-`p`

`IsProP p G` (see `NK.LocalTame.Basic`) says that every finite quotient of `G` has `p`-power
order.  The point of this file is that this property is stable under joins of *normal* subgroups:
if `M, N ⊴ G` are pro-`p`, then so is `M ⊔ N`.

The normality is essential: in the group `G ⧸ K` of a finite quotient `K` of `M ⊔ N`, the images
`MK/K` and `NK/K` of `M` and `N` are normal subgroups, so that quotient is the product of two
normal subgroups which are themselves finite quotients of `M` resp. `N` (second isomorphism
theorem), hence of `p`-power order.  Concretely the computation is

`[M ⊔ N : K] = [N : N ⊓ K] · [(N ⊔ K) : M]`,

where `[N : N ⊓ K] = p ^ b` by `IsProP p ↥N` and `[(N ⊔ K) : M] = [M : M ⊓ (N ⊔ K)] = p ^ e`
by `IsProP p ↥M`.  Both factors are indices inside the abstract group `↥(M ⊔ N)`, i.e. they are
`relIndex`es, so that the whole proof takes place inside `↥(M ⊔ N)` where `K` is normal.
-/

namespace NK.LocalTame.ProP

open Subgroup

/-- **Pro-`p`-ness passes to a subgroup of a subgroup.**  The composite of the isomorphism
`↥(S.subgroupOf T) ≃* ↥(S.map T.subtype) = ↥S` with `isProP_congr`. -/
theorem isProP_subgroupOf {G : Type*} [Group G] {p : ℕ} {S T : Subgroup G} (h : S ≤ T)
    (hS : IsProP p ↥S) : IsProP p ↥(S.subgroupOf T) := by
  have hmap : Subgroup.map T.subtype (S.subgroupOf T) = S := by
    rw [Subgroup.subgroupOf_map_subtype S T, inf_eq_left.mpr h]
  exact (isProP_congr ((Subgroup.equivMapOfInjective (S.subgroupOf T) T.subtype
    T.subtype_injective).trans (MulEquiv.subgroupCongr hmap)) p).mpr hS

theorem isProP_sup_of_normal {G : Type*} [Group G] {p : ℕ} {M N : Subgroup G} (hM : M.Normal)
    (hN : N.Normal) (hMp : IsProP p ↥M) (hNp : IsProP p ↥N) : IsProP p ↥(M ⊔ N) := by
  intro K hK hKfin
  have hMn : (M.subgroupOf (M ⊔ N)).Normal := hM.subgroupOf (M ⊔ N)
  have hNn : (N.subgroupOf (M ⊔ N)).Normal := hN.subgroupOf (M ⊔ N)
  -- the copies of `M` and `N` inside `↥(M ⊔ N)` are again pro-`p`
  have hM1p : IsProP p ↥(M.subgroupOf (M ⊔ N)) := isProP_subgroupOf le_sup_left hMp
  have hN1p : IsProP p ↥(N.subgroupOf (M ⊔ N)) := isProP_subgroupOf le_sup_right hNp
  -- and they join to the whole group
  have hsup : M.subgroupOf (M ⊔ N) ⊔ N.subgroupOf (M ⊔ N) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := M) (A' := N) (B := M ⊔ N) le_sup_left le_sup_right,
      Subgroup.subgroupOf_self]
  -- `K.index = [N : N ⊓ K] · [(N ⊔ K) : M]`
  have hB : K.index = K.relIndex (N.subgroupOf (M ⊔ N) ⊔ K) *
      (N.subgroupOf (M ⊔ N) ⊔ K).relIndex ⊤ := by
    rw [← Subgroup.relIndex_top_right K]
    exact (Subgroup.relIndex_mul_relIndex (H := K) (K := N.subgroupOf (M ⊔ N) ⊔ K)
      (L := ⊤) le_sup_right le_top).symm
  have hA : K.relIndex (N.subgroupOf (M ⊔ N) ⊔ K) = K.relIndex (N.subgroupOf (M ⊔ N)) :=
    Subgroup.relIndex_sup_right _ _
  -- the first factor is finite, hence the two factors of `hB` are non-zero
  have hne1 : K.relIndex (N.subgroupOf (M ⊔ N) ⊔ K) ≠ 0 := by
    intro h0
    have : K.index = 0 := by rw [hB, h0, zero_mul]
    exact Subgroup.finiteIndex_iff.mp hKfin this
  have hneN : K.relIndex (N.subgroupOf (M ⊔ N)) ≠ 0 := hA ▸ hne1
  have hneB : (N.subgroupOf (M ⊔ N) ⊔ K).relIndex ⊤ ≠ 0 := by
    intro h0
    have : K.index = 0 := by rw [hB, h0, mul_zero]
    exact Subgroup.finiteIndex_iff.mp hKfin this
  -- second isomorphism theorem for the second factor
  have hsup2 : M.subgroupOf (M ⊔ N) ⊔ (N.subgroupOf (M ⊔ N) ⊔ K) = ⊤ := by
    rw [← sup_assoc, hsup, top_sup_eq]
  have hC : (N.subgroupOf (M ⊔ N) ⊔ K).relIndex
      (M.subgroupOf (M ⊔ N) ⊔ (N.subgroupOf (M ⊔ N) ⊔ K)) =
      (N.subgroupOf (M ⊔ N) ⊔ K).relIndex (M.subgroupOf (M ⊔ N)) :=
    Subgroup.relIndex_sup_right _ _
  have hD : (N.subgroupOf (M ⊔ N) ⊔ K).relIndex ⊤ =
      (N.subgroupOf (M ⊔ N) ⊔ K).relIndex (M.subgroupOf (M ⊔ N)) := by
    rw [← hsup2, hC]
  have hneM : (N.subgroupOf (M ⊔ N) ⊔ K).relIndex (M.subgroupOf (M ⊔ N)) ≠ 0 := by
    rw [← hD]; exact hneB
  -- both factors are `p`-powers, by the two hypotheses
  obtain ⟨b, hb⟩ : ∃ b, K.relIndex (N.subgroupOf (M ⊔ N)) = p ^ b := by
    have hnorm : (K.subgroupOf (N.subgroupOf (M ⊔ N))).Normal := hK.subgroupOf _
    have hfi : (K.subgroupOf (N.subgroupOf (M ⊔ N))).FiniteIndex := by
      rw [Subgroup.finiteIndex_iff]
      exact hneN
    exact hN1p _ hfi
  obtain ⟨e, he⟩ :
      ∃ e, (N.subgroupOf (M ⊔ N) ⊔ K).relIndex (M.subgroupOf (M ⊔ N)) = p ^ e := by
    have hnorm : ((N.subgroupOf (M ⊔ N) ⊔ K).subgroupOf (M.subgroupOf (M ⊔ N))).Normal :=
      (Subgroup.sup_normal _ _).subgroupOf _
    have hfi : ((N.subgroupOf (M ⊔ N) ⊔ K).subgroupOf (M.subgroupOf (M ⊔ N))).FiniteIndex := by
      rw [Subgroup.finiteIndex_iff]
      exact hneM
    exact hM1p _ hfi
  exact ⟨b + e, by rw [hB, hA, hD, hb, he, ← pow_add]⟩

end NK.LocalTame.ProP
