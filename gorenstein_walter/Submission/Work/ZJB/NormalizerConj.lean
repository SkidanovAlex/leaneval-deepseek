import Submission.Work.ZJB.Defs
import Submission.Work.ZJB.ZJBasic

/-!
# ZJB — Sylow conjugacy inside a normalizer

The one structural input of Glauberman's Lemma 5.1 that is not pure algebra: if `S` is a Sylow
`p`-subgroup of `G` with `S ≤ N`, then every `p`-subgroup `V ≤ N` is carried into `S` by an
element of `N`:

`exists_mem_normalizer_inv_mul_mem : ∃ m ∈ N, ∀ v ∈ V, m⁻¹ * v * m ∈ S`

(`S` is a Sylow `p`-subgroup of `N` because it is one of `G`; the proof passes to the group `↥N`,
uses Sylow's first theorem and the transitivity of the conjugation action on the Sylow subgroups,
and transports back along the subtype embedding.)
-/

namespace Work.ZJB

open Work.GW2
open Subgroup
open Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- **Sylow conjugacy inside a normalizer.**  If `S` is a Sylow `p`-subgroup of `G` with `S ≤ N`
and `V ≤ N` is a `p`-subgroup, then some `m ∈ N` satisfies `m⁻¹ * v * m ∈ S` for all `v ∈ V`. -/
theorem exists_mem_normalizer_inv_mul_mem {p : ℕ} [Fact p.Prime] (S : Sylow p G) {N V : Subgroup G}
    (hSN : (S : Subgroup G) ≤ N) (hVN : V ≤ N) (hVp : IsPGroup p V) :
    ∃ m ∈ N, ∀ v ∈ V, m⁻¹ * v * m ∈ (S : Subgroup G) := by
  haveI : Finite ↥N := Finite.of_injective (Subtype.val : ↥N → G) Subtype.val_injective
  let S' : Sylow p ↥N := S.subtype hSN
  let V' : Subgroup ↥N := V.subgroupOf N
  have hV'p : IsPGroup p ↥V' := hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVN).symm
  obtain ⟨Q, hV'Q⟩ := hV'p.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (M := ↥N) Q S'
  refine ⟨(y : G)⁻¹, N.inv_mem y.2, fun v hv => ?_⟩
  have hq : (⟨v, hVN hv⟩ : ↥N) ∈ Q := hV'Q (Subgroup.mem_subgroupOf.mpr hv)
  have hmem : MulAut.conj y (⟨v, hVN hv⟩ : ↥N) ∈ (S' : Subgroup ↥N) := by
    have h1 : MulAut.conj y (⟨v, hVN hv⟩ : ↥N) ∈ (MulAut.conj y) • (Q : Subgroup ↥N) :=
      (Subgroup.smul_mem_pointwise_smul_iff).mpr hq
    have h2 : ((y • Q : Sylow p ↥N) : Subgroup ↥N) = (MulAut.conj y) • (Q : Subgroup ↥N) :=
      Sylow.coe_subgroup_smul
    rwa [← h2, hy] at h1
  rw [Sylow.coe_subtype S hSN, Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply, inv_inv] using hmem

end Work.ZJB
