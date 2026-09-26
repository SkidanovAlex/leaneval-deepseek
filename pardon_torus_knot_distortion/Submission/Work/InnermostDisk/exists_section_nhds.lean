import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

/-!
# Local continuous sections of the parametrisation of the standard torus

`Work.InnermostDisk.exists_section_nhds` shows that the parametrisation `ψ = torusMap` of the
standard torus, viewed as a map onto its image `F = standard.carrier`, admits a continuous local
section near every point `X ∈ F`: there is a neighbourhood `s` of `X` inside `F` and a continuous
map `σ : s → ℝ × ℝ` with `ψ (σ x).1 (σ x).2 = x` for all `x ∈ s`.

The parametrisation is a covering map onto its image
(`Work.TorusCover.isCoveringMap_psiMapToRange_param`), hence a local homeomorphism
(`IsCoveringMap.isLocalHomeomorph`); the local inverse `IsLocalHomeomorph.localInverseAt`
provides the section, and the target is transferred from the range-subtype to `F ⊆ ℝ³` along
the embedding `Subtype.val`.
-/

namespace Work.InnermostDisk

open LeanEval.KnotTheory.PardonDistortion Set
open Work.CoreTopology

noncomputable section

theorem exists_section_nhds (X : LeanEval.KnotTheory.PardonDistortion.R3)
    (hX : X ∈ Work.CoreTopology.standard.carrier) :
    ∃ (s : Set LeanEval.KnotTheory.PardonDistortion.R3) (σ : C(s, ℝ × ℝ)),
      X ∈ s ∧ (∀ x ∈ s, x ∈ Work.CoreTopology.standard.carrier) ∧
      (∀ x : s, Work.CoreTopology.standard.psi (σ x).1 (σ x).2 =
        (x : LeanEval.KnotTheory.PardonDistortion.R3)) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Work.CoreTopology.standard.carrier, dist x X < ε → x ∈ s) := by
  have hcarrier : Work.CoreTopology.standard.carrier =
      Set.range (Work.TorusCover.psiMap Work.CoreTopology.standard.psi) := rfl
  set ψ : Set R3 := Set.range (Work.TorusCover.psiMap Work.CoreTopology.standard.psi) with hψ
  have hcov : IsCoveringMap (Work.TorusCover.psiMapToRange Work.CoreTopology.standard.psi) :=
    Work.TorusCover.isCoveringMap_psiMapToRange_param Work.CoreTopology.standard
  have hf : IsLocalHomeomorph (Work.TorusCover.psiMapToRange Work.CoreTopology.standard.psi) :=
    hcov.isLocalHomeomorph
  have hXψ : X ∈ ψ := hcarrier ▸ hX
  let X' : ψ := ⟨X, hXψ⟩
  obtain ⟨p, hp⟩ :
      ∃ p : ℝ × ℝ, Work.TorusCover.psiMapToRange Work.CoreTopology.standard.psi p = X' := by
    obtain ⟨p, hp⟩ := Set.mem_range.mp X'.2
    exact ⟨p, Subtype.ext hp⟩
  let e : OpenPartialHomeomorph ψ (ℝ × ℝ) := hf.localInverseAt p
  have hX'_source : X' ∈ e.source := by
    have h := hf.apply_self_mem_localInverseAt_source (x := p)
    rw [← hp]; exact h
  have hsec : ∀ y ∈ e.source,
      Work.TorusCover.psiMapToRange Work.CoreTopology.standard.psi (e y) = y := by
    intro y hy
    exact hf.apply_localInverseAt_of_mem (x := p) hy
  have hEmb : Topology.IsEmbedding (Subtype.val : ψ → R3) := Topology.IsEmbedding.subtypeVal
  have hpre : (Subtype.val ⁻¹' (Subtype.val '' e.source) : Set ψ) = e.source :=
    Set.preimage_image_eq e.source hEmb.injective
  have hs_range : (Subtype.val '' e.source : Set R3) ⊆ Set.range (Subtype.val : ψ → R3) :=
    Set.image_subset_range _ _
  let homeo : (Subtype.val ⁻¹' (Subtype.val '' e.source) : Set ψ) ≃ₜ
      (Subtype.val '' e.source : Set R3) := hEmb.homeomorphOfSubsetRange hs_range
  have hσcont : Continuous (fun x : (Subtype.val '' e.source : Set R3) => e (homeo.symm x)) := by
    have hcont : Continuous ((Subtype.val ⁻¹' (Subtype.val '' e.source) : Set ψ).domRestrict
        (fun y : ψ => (e : ψ → ℝ × ℝ) y)) := by
      have h := e.continuousOn
      rw [← hpre] at h
      exact h.domRestrict
    exact hcont.comp homeo.symm.continuous
  refine ⟨Subtype.val '' e.source, ⟨fun x => e (homeo.symm x), hσcont⟩, ?_, ?_, ?_, ?_⟩
  · exact ⟨X', hX'_source, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hcarrier.symm ▸ y.2
  · intro x
    have h1 : (homeo (homeo.symm x) : R3) = (homeo.symm x : R3) :=
      hEmb.homeomorphOfSubsetRange_apply_coe hs_range (homeo.symm x)
    have h2 : (homeo (homeo.symm x) : R3) = (x : R3) :=
      congrArg Subtype.val (homeo.apply_symm_apply x)
    have hxy : (x : R3) = (homeo.symm x : R3) := h2.symm.trans h1
    have hy_src : (homeo.symm x : ψ) ∈ e.source := by
      obtain ⟨z, hz, hzx⟩ := (homeo.symm x).2
      have hz' : z = (homeo.symm x : ψ) := hEmb.injective hzx
      rwa [hz'] at hz
    have hsecx := hsec (↑(homeo.symm x)) hy_src
    have hfinal : Work.TorusCover.psiMap Work.CoreTopology.standard.psi (e ↑(homeo.symm x))
        = (x : R3) := by
      trans (homeo.symm x : R3)
      · exact congrArg Subtype.val hsecx
      · exact hxy.symm
    simpa [Work.TorusCover.psiMap] using hfinal
  · obtain ⟨V, hVopen, hVpre⟩ := isOpen_induced_iff.mp e.open_source
    have hs_eq : (Subtype.val '' e.source : Set R3) = V ∩ Work.CoreTopology.standard.carrier := by
      rw [← hVpre, Set.image_preimage_eq_inter_range, Subtype.range_val, ← hcarrier]
    have hX_in_V : X ∈ V := by
      have hmem : X ∈ (Subtype.val '' e.source : Set R3) := ⟨X', hX'_source, rfl⟩
      rw [hs_eq] at hmem
      exact hmem.1
    obtain ⟨ε, hεpos, hεball⟩ := (Metric.isOpen_iff.mp hVopen) X hX_in_V
    refine ⟨ε, hεpos, ?_⟩
    intro x hxcarrier hdist
    have hxV : x ∈ V := hεball (by rw [Metric.mem_ball]; exact hdist)
    rw [hs_eq]
    exact ⟨hxV, hxcarrier⟩

end

end Work.InnermostDisk
