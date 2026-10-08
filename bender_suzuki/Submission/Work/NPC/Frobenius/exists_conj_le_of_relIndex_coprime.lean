import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.NPC.Frobenius

/-- Conjugation of a subgroup by `MulAut.conj h` is the same as the pointwise image of `h`
acting by conjugation, which coincides with `Subgroup.map` along the monoid endomorphism
`MulAut.conj h`. -/
lemma conj_smul_eq_map {G : Type*} [Group G] (h : G) (T : Subgroup G) :
    (MulAut.conj h) • T = T.map (MulAut.conj h).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem exists_conj_le_of_relIndex_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H S T : Subgroup G} (hS : S ≤ H) (hT : T ≤ H) (hSp : IsPGroup p S) (hTp : IsPGroup p T)
    (hcop : ¬ p ∣ S.relIndex H) :
    ∃ h ∈ H, T.map (MulAut.conj h).toMonoidHom ≤ S := by
  -- View `S` and `T` as subgroups of `H`.
  have hSp' : IsPGroup p (S.subgroupOf H) := hSp.comap_subtype
  have hTp' : IsPGroup p (T.subgroupOf H) := hTp.comap_subtype
  -- `S` is a Sylow `p`-subgroup of `H` because its index is prime to `p`.
  have hSindex : ¬ p ∣ (S.subgroupOf H).index := hcop
  -- `T` lies in some Sylow `p`-subgroup `Q` of `H`, and `Q` is conjugate to `S`.
  obtain ⟨Q, hTQ⟩ := hTp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (hSp'.toSylow hSindex) Q
  have hQ : (MulAut.conj g) • (S.subgroupOf H) = (Q : Subgroup ↥H) := by
    rw [← hg, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe]
  have hTQ' : T.subgroupOf H ≤ (MulAut.conj g) • (S.subgroupOf H) := hQ ▸ hTQ
  -- Conjugate back: `(MulAut.conj g)⁻¹ • T ≤ S` inside `H`.
  have hstep1 : MulAut.conj g⁻¹ • (T.subgroupOf H) ≤ S.subgroupOf H := by
    have h := (Subgroup.subset_pointwise_smul_iff (a := MulAut.conj g)).mp hTQ'
    rw [map_inv]
    exact h
  -- Transport back to the ambient group `G`, using that `S, T ≤ H`.
  have hstep2 : MulAut.conj ((g⁻¹ : ↥H) : G) • T ≤ S := by
    have h := Subgroup.map_mono hstep1 (f := H.subtype)
    rw [Subgroup.conj_smul_subgroupOf hT g⁻¹, Subgroup.subgroupOf_map_subtype,
      Subgroup.map_subgroupOf_eq_of_le hS] at h
    rwa [inf_eq_left.mpr (Subgroup.conj_smul_le_of_le hT g⁻¹)] at h
  refine ⟨((g⁻¹ : ↥H) : G), (g⁻¹ : ↥H).2, ?_⟩
  rw [← conj_smul_eq_map]
  exact hstep2

end Work.NPC.Frobenius
