import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB2.sylowInConj

/-!
# G2: a Sylow subgroup of `M` meets a normal subgroup `L ⊴ M` in a Sylow subgroup of `L`

`Submission/Work/ZJB2/Defs.lean` states this as `SylowInInfNormalProp p G`; here it is proved.

**Mathematics.**  Let `T` be a maximal `p`-subgroup of `M` and `L ≤ M` with
`M ≤ N_G(L)`.  Then `T ⊓ L ≤ L` is a `p`-subgroup, and we must see it is maximal: if
`Q ≤ L` is a `p`-subgroup of `M` with `T ⊓ L ≤ Q`, Sylow conjugacy inside `M` gives `m ∈ M`
with `m⁻¹ Q m ≤ T`.  Since `m` normalises `L`, conjugating a subgroup of `L` by `m⁻¹` keeps
it inside `L`, so `m⁻¹ Q m ≤ T ⊓ L`.  Hence `|Q| = |m⁻¹ Q m| ≤ |T ⊓ L| ≤ |Q|`, forcing
`Q = T ⊓ L`.

The hypothesis `hML` is used only to see that the conjugate of a subgroup of `L` is again a
subgroup of `L`.

`exists_conj_le_of_isSylowIn` below is the leaf G1 (`Work.ZJB2.sylowInConj`,
`Work.ZJB.SylowInConjProp`) restated for a universe-polymorphic ambient group: the leaf G1
itself is fixed at `Type 0`, while the statement proved here is `Type*`, so the proof is
reproduced on top of the universe-polymorphic constructor `Work.ZJB2.subgroupOfIsSylow`.
-/

namespace Work.ZJB2.Step1

open Work.ZJB
open Subgroup

open scoped Pointwise

/-- **Sylow conjugacy inside a subgroup** (`IsSylowIn` form, universe-polymorphic).
Every `p`-subgroup `V` of `M` is conjugated into a Sylow `p`-subgroup `T` of `M` by an element
of `M` (in the paper's convention `v ↦ m⁻¹ * v * m`). -/
theorem exists_conj_le_of_isSylowIn {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T M V : Subgroup G} (hT : Work.ZJB.IsSylowIn p T M) (hVM : V ≤ M)
    (hVp : IsPGroup p V) :
    ∃ m ∈ M, ∀ v ∈ V, m⁻¹ * v * m ∈ T := by
  -- `T.subgroupOf M` is a Sylow `p`-subgroup of the group `↥M`.
  let S : Sylow p ↥M := subgroupOfIsSylow hT
  have hS : (S : Subgroup ↥M) = T.subgroupOf M := subgroupOfIsSylow_coe hT
  -- `V.subgroupOf M` is a `p`-subgroup of `↥M`, so it lies in a Sylow `p`-subgroup `Q`;
  -- all Sylow subgroups of `↥M` are conjugate.
  have hV'p : IsPGroup p ↥(V.subgroupOf M) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVM).symm
  obtain ⟨Q, hVQ⟩ := hV'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq
    (self := Sylow.isPretransitive_of_finite) Q S
  have hmono : MulAut.conj g • (V.subgroupOf M : Subgroup ↥M) ≤ (S : Subgroup ↥M) := by
    have h1 : MulAut.conj g • (V.subgroupOf M : Subgroup ↥M) ≤
        MulAut.conj g • (Q : Subgroup ↥M) := by
      rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact Subgroup.map_mono hVQ
    rwa [← Sylow.coe_subgroup_smul, hg] at h1
  refine ⟨(g : G)⁻¹, M.inv_mem g.2, fun v hv => ?_⟩
  have hv' : (⟨v, hVM hv⟩ : ↥M) ∈ V.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]; exact hv
  have hmem : (MulAut.conj g) (⟨v, hVM hv⟩ : ↥M) ∈ (S : Subgroup ↥M) :=
    hmono (Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hv')
  rw [hS, Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

/-- **G2.** A Sylow `p`-subgroup of `M` meets a subgroup `L` that is normalised by `M` in a
Sylow `p`-subgroup of `L`. -/
theorem sylowInInfNormal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T M L : Subgroup G} (hT : Work.ZJB.IsSylowIn p T M) (hLM : L ≤ M)
    (hML : M ≤ Subgroup.normalizer (L : Set G)) :
    Work.ZJB.IsSylowIn p (T ⊓ L) L := by
  refine ⟨inf_le_right, hT.2.1.to_inf_left, ?_⟩
  intro Q hQle hQL hQp
  -- `Q` is a `p`-subgroup of `M`, so some `M`-conjugate of it lies in `T`.
  have hQM : Q ≤ M := hQL.trans hLM
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_isSylowIn hT hQM hQp
  -- Conjugating `Q` by `m⁻¹` lands in `T` (by `hm`) and in `L` (as `m` normalises `L`).
  have hconj : Q.map (MulAut.conj m⁻¹).toMonoidHom ≤ T ⊓ L := by
    refine le_inf ?_ ?_
    · rw [map_le_iff_le_comap]
      intro q hq
      simpa [MulAut.conj_apply] using hm q hq
    · rw [map_le_iff_le_comap]
      intro q hq
      have hq' : m⁻¹ * q * m ∈ (L : Set G) :=
        ((Subgroup.mem_normalizer_iff'').mp (hML hmM) q).mp (hQL hq)
      simpa [MulAut.conj_apply] using hq'
  -- Conjugation is a bijection, so `|Q| ≤ |T ⊓ L|`; with `T ⊓ L ≤ Q` this is an equality.
  have hcard : Nat.card (Q.map (MulAut.conj m⁻¹).toMonoidHom) = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective
  have hle : Nat.card Q ≤ Nat.card ↥(T ⊓ L) := by
    rw [← hcard]
    exact Subgroup.card_le_of_le hconj
  exact (Subgroup.eq_of_le_of_card_ge hQle hle).symm

end Work.ZJB2.Step1
