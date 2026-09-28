import Mathlib

namespace Work.Analysis.LocalDiffeomorph

open scoped ContDiff Topology

open scoped ContDiff Topology in
theorem local_diffeomorph_partial_homeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {φ : E → E} {e : E ≃L[ℝ] E} {U V : Set E}
    (hU : U ∈ 𝓝 0) (hV : V ∈ 𝓝 0) (hφ0 : φ 0 = 0)
    (hφsm : ContDiffOn ℝ ∞ φ U) (hφd : HasFDerivAt φ (e : E →L[ℝ] E) 0) :
    ∃ ψ : OpenPartialHomeomorph E E, 0 ∈ ψ.source ∧ ψ 0 = 0 ∧ ψ.source ⊆ U ∩ V ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ x ∈ ψ.source, ψ x = φ x) := by
  have hφ0' : ContDiffAt ℝ ∞ φ 0 := hφsm.contDiffAt hU
  have hne : (∞ : ℕ∞ω) ≠ 0 := by simp
  let ψ₀ : OpenPartialHomeomorph E E := hφ0'.toOpenPartialHomeomorph φ hφd hne
  have hψ₀coe : ⇑ψ₀ = φ := ContDiffAt.toOpenPartialHomeomorph_coe hφ0' hφd hne
  have hmem0 : 0 ∈ ψ₀.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hφ0' hφd hne
  have hU₀ : IsOpen (interior U) := isOpen_interior
  have hV₀ : IsOpen (interior V) := isOpen_interior
  have hcont : ContinuousOn (fderiv ℝ φ) (interior U) :=
    (hφsm.mono interior_subset).continuousOn_fderiv_of_isOpen isOpen_interior (by simp)
  have h1 : IsOpen (interior U ∩ (fderiv ℝ φ) ⁻¹' Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E)) :=
    hcont.isOpen_inter_preimage isOpen_interior ContinuousLinearEquiv.isOpen
  let s : Set E := (interior U ∩ (fderiv ℝ φ) ⁻¹' Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E)) ∩ interior V
  have hsopen : IsOpen s := h1.inter hV₀
  have h0s : 0 ∈ s := by
    refine ⟨⟨mem_interior_iff_mem_nhds.mpr hU, ?_⟩, mem_interior_iff_mem_nhds.mpr hV⟩
    rw [Set.mem_preimage, Set.mem_range]
    exact ⟨e, by rw [hφd.fderiv]⟩
  refine ⟨ψ₀.restrOpen s hsopen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hmem0, h0s⟩
  · rw [OpenPartialHomeomorph.coe_restrOpen, hψ₀coe]
    exact hφ0
  · rw [OpenPartialHomeomorph.restrOpen_source]
    intro x hx
    exact ⟨interior_subset hx.2.1.1, interior_subset hx.2.2⟩
  · have hsub : (ψ₀.restrOpen s hsopen).source ⊆ U := by
      rw [OpenPartialHomeomorph.restrOpen_source]
      exact fun x hx => interior_subset hx.2.1.1
    refine (hφsm.mono hsub).congr (fun x hx => ?_)
    rw [OpenPartialHomeomorph.coe_restrOpen, hψ₀coe]
  · have htgt : (ψ₀.restrOpen s hsopen).target = ψ₀.target ∩ (ψ₀.symm) ⁻¹' s := by
      rw [OpenPartialHomeomorph.restrOpen_toPartialEquiv]
      exact PartialEquiv.restr_target _ _
    have hbody : ContDiffOn ℝ ∞ (⇑(ψ₀.symm) : E → E) (ψ₀.restrOpen s hsopen).target := by
      intro a ha
      rw [htgt] at ha
      have ha₀ : a ∈ ψ₀.target := ha.1
      have hxa : ψ₀.symm a ∈ s := ha.2
      have hxU : ψ₀.symm a ∈ interior U := hxa.1.1
      have hφx : ContDiffAt ℝ ∞ φ (ψ₀.symm a) :=
        (hφsm.mono interior_subset).contDiffAt (isOpen_interior.mem_nhds hxU)
      have hderiv : HasFDerivAt φ (fderiv ℝ φ (ψ₀.symm a)) (ψ₀.symm a) :=
        (hφx.differentiableAt hne).hasFDerivAt
      obtain ⟨e', he'⟩ := hxa.1.2
      have hderiv' : HasFDerivAt φ (e' : E →L[ℝ] E) (ψ₀.symm a) := by
        rw [he']; exact hderiv
      have hderiv'' : HasFDerivAt (⇑ψ₀) (e' : E →L[ℝ] E) (⇑ψ₀.symm a) := by
        rw [hψ₀coe]; exact hderiv'
      have hsmooth : ContDiffAt ℝ ∞ (⇑ψ₀) (⇑ψ₀.symm a) := by
        rw [hψ₀coe]; exact hφx
      exact (ψ₀.contDiffAt_symm ha₀ hderiv'' hsmooth).contDiffWithinAt
    refine hbody.congr (fun x hx => ?_)
    rw [OpenPartialHomeomorph.coe_restrOpen_symm]
  · intro x hx
    rw [OpenPartialHomeomorph.coe_restrOpen, hψ₀coe]

end Work.Analysis.LocalDiffeomorph
