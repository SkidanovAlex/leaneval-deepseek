import Mathlib
import Submission.Work.ZJB.Step1.Defs

namespace Work.ZJB2.Step1

open Subgroup
open Pointwise

/-- **Sylow conjugacy inside a subgroup.**  If `T` is a maximal `p`-subgroup of `N`
(`IsSylowIn p T N`) and `V ≤ N` is a `p`-subgroup, then some `m ∈ N` conjugates `V` into `T`.
This is the leaf `SylowInConjProp` of `ZJB2/Defs.lean`, stated with `N` named.

The proof passes to the group `↥N`: `T.subgroupOf N` is a `Sylow p ↥N` (it is a `p`-subgroup,
and maximality follows from the maximality of `T` in `N` via `Subgroup.subgroupOf_map_subtype`),
`V.subgroupOf N` lies in some Sylow `Q`, and the conjugation action of `↥N` on its Sylow
subgroups is transitive, so `y • Q = T.subgroupOf N` for some `y`.  Transporting back along the
subtype embedding gives `y⁻¹ (as element of G)` as the conjugating element. -/
theorem exists_mem_inv_mul_mem_of_isSylowIn {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {N V T : Subgroup G} (hT : Work.ZJB.IsSylowIn p T N) (hVN : V ≤ N)
    (hVp : IsPGroup p V) : ∃ m ∈ N, ∀ v ∈ V, m⁻¹ * v * m ∈ T := by
  have hTN : T ≤ N := hT.1
  have hT'sub_p : IsPGroup p (T.subgroupOf N) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm
  have hmax : ∀ {Q : Subgroup ↥N}, IsPGroup p Q → T.subgroupOf N ≤ Q → Q = T.subgroupOf N := by
    intro Q hQ hle
    have hQmap : IsPGroup p (Q.map N.subtype) := hQ.map N.subtype
    have hTleQmap : T ≤ Q.map N.subtype := by
      intro t ht
      have ht' : (⟨t, hTN ht⟩ : ↥N) ∈ Q := hle (Subgroup.mem_subgroupOf.mpr ht)
      exact Subgroup.mem_map.mpr ⟨⟨t, hTN ht⟩, ht', rfl⟩
    have hQmapN : Q.map N.subtype ≤ N := Subgroup.map_subtype_le Q
    have hQmapEq : Q.map N.subtype = T := hT.2.2 (Q.map N.subtype) hTleQmap hQmapN hQmap
    have hthis := Subgroup.comap_map_eq_self_of_injective N.subtype_injective Q
    rw [hQmapEq] at hthis
    rw [← hthis]
    rfl
  let T' : Sylow p ↥N := ⟨T.subgroupOf N, hT'sub_p, fun {Q} hQ hle => hmax hQ hle⟩
  let V' : Subgroup ↥N := V.subgroupOf N
  have hV'p : IsPGroup p ↥V' := hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVN).symm
  obtain ⟨Q, hV'Q⟩ := hV'p.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (M := ↥N) Q T'
  refine ⟨(y : G)⁻¹, N.inv_mem y.2, fun v hv => ?_⟩
  have hq : (⟨v, hVN hv⟩ : ↥N) ∈ Q := hV'Q (Subgroup.mem_subgroupOf.mpr hv)
  have hmem : MulAut.conj y (⟨v, hVN hv⟩ : ↥N) ∈ (T' : Subgroup ↥N) := by
    have h1 : MulAut.conj y (⟨v, hVN hv⟩ : ↥N) ∈ (MulAut.conj y) • (Q : Subgroup ↥N) :=
      (Subgroup.smul_mem_pointwise_smul_iff).mpr hq
    have h2 : ((y • Q : Sylow p ↥N) : Subgroup ↥N) = (MulAut.conj y) • (Q : Subgroup ↥N) :=
      Sylow.coe_subgroup_smul
    rwa [← h2, hy] at h1
  have hmemG : (↑(MulAut.conj y (⟨v, hVN hv⟩ : ↥N)) : G) ∈ T := Subgroup.mem_subgroupOf.mp hmem
  simpa [MulAut.conj_apply, inv_inv] using hmemG

end Work.ZJB2.Step1
