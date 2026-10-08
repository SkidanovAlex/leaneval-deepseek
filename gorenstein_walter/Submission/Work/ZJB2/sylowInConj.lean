import Mathlib
import Submission.Work.ZJB2.Defs

namespace Work.ZJB2

open Work.ZJB
open Subgroup

open scoped Pointwise

/-- **G1 (helper).** If `T` is a Sylow `p`-subgroup of the subgroup `M ≤ G`, then
`T.subgroupOf M` is a Sylow `p`-subgroup of the group `↥M`. -/
noncomputable def subgroupOfIsSylow {G : Type*} [Group G] {p : ℕ} {T M : Subgroup G}
    (hT : IsSylowIn p T M) : Sylow p ↥M :=
  { toSubgroup := T.subgroupOf M
    isPGroup' := hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    is_maximal' := by
      intro Q hQ hTQ
      have hQmap : IsPGroup p ↥(Q.map M.subtype) := hQ.map M.subtype
      have hle : T ≤ Q.map M.subtype := by
        intro x hx
        exact ⟨⟨x, hT.1 hx⟩, hTQ (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
      have heq : Q.map M.subtype = T := hT.2.2 _ hle (Subgroup.map_subtype_le Q) hQmap
      exact Subgroup.map_injective (Subgroup.subtype_injective M)
        (heq.trans (Subgroup.map_subgroupOf_eq_of_le hT.1).symm) }

@[simp]
theorem subgroupOfIsSylow_coe {G : Type*} [Group G] {p : ℕ} {T M : Subgroup G}
    (hT : IsSylowIn p T M) :
    ((subgroupOfIsSylow hT : Sylow p ↥M) : Subgroup ↥M) = T.subgroupOf M := rfl

/-- **G1.** Sylow's conjugacy theorem inside a subgroup: every `p`-subgroup `V` of a subgroup `M`
is conjugated into any Sylow `p`-subgroup `T` of `M` by an element of `M`. -/
theorem sylowInConj (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.SylowInConjProp p G := by
  intro T M V hT hV hVp
  -- `T.subgroupOf M` is a Sylow `p`-subgroup of `↥M`
  let S : Sylow p ↥M := subgroupOfIsSylow hT
  have hS : (S : Subgroup ↥M) = T.subgroupOf M := subgroupOfIsSylow_coe hT
  -- `V.subgroupOf M` is a `p`-subgroup of `↥M`
  have hV'p : IsPGroup p ↥(V.subgroupOf M) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hV).symm
  obtain ⟨Q, hVQ⟩ := hV'p.exists_le_sylow
  -- conjugacy of Sylow subgroups of `↥M`
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq
    (self := Sylow.isPretransitive_of_finite) Q S
  have hmono : MulAut.conj g • (V.subgroupOf M : Subgroup ↥M) ≤ (S : Subgroup ↥M) := by
    have h1 : MulAut.conj g • (V.subgroupOf M : Subgroup ↥M) ≤
        MulAut.conj g • (Q : Subgroup ↥M) := by
      rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact Subgroup.map_mono hVQ
    rwa [← Sylow.coe_subgroup_smul, hg] at h1
  refine ⟨(g : G)⁻¹, M.inv_mem g.2, fun v hv => ?_⟩
  have hv' : (⟨v, hV hv⟩ : ↥M) ∈ V.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]; exact hv
  have hmem : (MulAut.conj g) (⟨v, hV hv⟩ : ↥M) ∈ (S : Subgroup ↥M) :=
    hmono (Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hv')
  rw [hS, Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

end Work.ZJB2
