import Mathlib
import Submission.Work.PTCore.TransgressionDefs
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PTCore

open Work.SSGRoute

/-- The `I`-coordinate of the product, in terms of the coordinates of the factors:
`ip (g * u) = ip g * (proj g * ip u * (proj g)⁻¹)` for `g, u ∈ D`. -/
theorem ipG_mul_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (S : DCtx k Ω) {g u : Ω ≃ₐ[k] Ω}
    (hgD : g ∈ SSGRoute.decomp k S.A) (huD : u ∈ SSGRoute.decomp k S.A) :
    ipG S (g * u) = ipG S g * (projG S g * ipG S u * (projG S g)⁻¹) := by
  have hgu : ipG S (g * u) * (projG S g * projG S u) = g * u := by
    rw [← projG_mul S hgD huD]
    exact ipG_mul_projG S (mul_mem hgD huD)
  have hg : ipG S g * projG S g = g := ipG_mul_projG S hgD
  have hu : ipG S u * projG S u = u := ipG_mul_projG S huD
  have h1 : (ipG S g * (projG S g * ipG S u * (projG S g)⁻¹)) * (projG S g * projG S u)
      = (ipG S g * projG S g) * (ipG S u * projG S u) := by group
  have key : (ipG S g * (projG S g * ipG S u * (projG S g)⁻¹)) * (projG S g * projG S u)
      = g * u := by
    rw [h1, hg, hu]
  exact mul_right_cancel (by rw [hgu, key])

/-- `ip` of the identity of `D` is the identity of `I`. -/
theorem ipG_one {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (S : DCtx k Ω) : ipG S (1 : Ω ≃ₐ[k] Ω) = 1 := by
  have hfac := HS.ip_mul_proj S.A S.I S.σ S.hI S.hnorm
    (HS.CC_le_DD S.A S.σ S.hσ) S.hsup (1 : ↥(SSGRoute.decomp k S.A))
  have h := (HS.factor_unique S.A S.I S.σ S.hinf
    (HS.ip S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup
      (1 : ↥(SSGRoute.decomp k S.A))).2
    (S.I.one_mem)
    (HS.proj S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup
      (1 : ↥(SSGRoute.decomp k S.A))).2
    ((Subgroup.topologicalClosure (Subgroup.zpowers S.σ)).one_mem)
    (by rw [hfac]; rfl)).1
  rw [ipG_of_mem S (SSGRoute.decomp k S.A).one_mem]
  show ((HS.ip S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup
    (1 : ↥(SSGRoute.decomp k S.A))).1 : Ω ≃ₐ[k] Ω) = 1
  exact h

theorem betaG_isLocConstOn {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (S : Work.PTCore.DCtx k Ω) {M : Type} [AddCommGroup M]
    (β : (Ω ≃ₐ[k] Ω) → M) (hβ : SSGRoute.IsLocConstOn S.I β) :
    SSGRoute.IsLocConstOn (SSGRoute.decomp k S.A) (Work.PTCore.betaG S β) := by
  classical
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  obtain ⟨U₁, hU₁open, hU₁⟩ := hβ
  have hnhds : (U₁ : Set (Ω ≃ₐ[k] Ω)) ∈ nhds (1 : Ω ≃ₐ[k] Ω) :=
    hU₁open.mem_nhds U₁.one_mem
  obtain ⟨L₁, hL₁⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := k) (K := Ω)
      (U₁ : Set (Ω ≃ₐ[k] Ω))).mp hnhds
  let V : Subgroup (Ω ≃ₐ[k] Ω) := L₁.toIntermediateField.fixingSubgroup
  have hVsub : (V : Set (Ω ≃ₐ[k] Ω)) ⊆ U₁ := hL₁
  have hVnorm : V.Normal := by
    haveI : IsGalois k ↥L₁.toIntermediateField := L₁.isGalois
    exact IsGalois.fixingSubgroup_normal_of_isGalois L₁.toIntermediateField
  have hVopen : IsOpen (V : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen L₁.toIntermediateField
  let ipH : ↥(SSGRoute.decomp k S.A) → ↥S.I :=
    HS.ip S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup
  have hcont : Continuous ipH :=
    Work.SSGRoute.HSRow.continuous_ip k Ω S.A S.I S.σ S.hI S.hnorm S.hσ S.hsup S.hinf S.hIclosed
  have hODopen : IsOpen {d : ↥(SSGRoute.decomp k S.A) | (ipH d : Ω ≃ₐ[k] Ω) ∈ V} :=
    hVopen.preimage (continuous_subtype_val.comp hcont)
  obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp hODopen
  have h1O : (1 : Ω ≃ₐ[k] Ω) ∈ O := by
    have hmem : (⟨1, (SSGRoute.decomp k S.A).one_mem⟩ : ↥(SSGRoute.decomp k S.A)) ∈
        Subtype.val ⁻¹' (O : Set (Ω ≃ₐ[k] Ω)) := by
      rw [hOeq]
      show (ipH ⟨1, (SSGRoute.decomp k S.A).one_mem⟩ : Ω ≃ₐ[k] Ω) ∈ V
      have hip1 : (ipH ⟨1, (SSGRoute.decomp k S.A).one_mem⟩ : Ω ≃ₐ[k] Ω) = 1 := by
        rw [← ipG_of_mem S (SSGRoute.decomp k S.A).one_mem, ipG_one S]
      rw [hip1]
      exact V.one_mem
    simpa using hmem
  have hOnhds : O ∈ nhds (1 : Ω ≃ₐ[k] Ω) := hOopen.mem_nhds h1O
  obtain ⟨L₂, hL₂⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := k) (K := Ω) O).mp hOnhds
  refine ⟨L₂.toIntermediateField.fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen L₂.toIntermediateField, ?_⟩
  intro g hgD u huU huD
  rw [betaG_of_mem S β (mul_mem hgD huD), betaG_of_mem S β hgD]
  have hipuV : ipG S u ∈ V := by
    have huO : u ∈ O := hL₂ huU
    have hmemV : (ipH ⟨u, huD⟩ : Ω ≃ₐ[k] Ω) ∈ V := by
      have h2 : (⟨u, huD⟩ : ↥(SSGRoute.decomp k S.A)) ∈
          {d : ↥(SSGRoute.decomp k S.A) | (ipH d : Ω ≃ₐ[k] Ω) ∈ V} := by
        rw [← hOeq]
        exact huO
      exact h2
    rw [ipG_of_mem S huD]
    exact hmemV
  have hcI : projG S g * ipG S u * (projG S g)⁻¹ ∈ S.I :=
    S.hnorm (projG S g) (projG_mem_D S hgD) (ipG S u) (ipG_mem_I S huD)
  have hcV : projG S g * ipG S u * (projG S g)⁻¹ ∈ V :=
    hVnorm.conj_mem (ipG S u) hipuV (projG S g)
  rw [ipG_mul_conj S hgD huD]
  exact hU₁ (ipG S g) (ipG_mem_I S hgD)
    (projG S g * ipG S u * (projG S g)⁻¹) (hVsub hcV) hcI

end Work.PTCore
