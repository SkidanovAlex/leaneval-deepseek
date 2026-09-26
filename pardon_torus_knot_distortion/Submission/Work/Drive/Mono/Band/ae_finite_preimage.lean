import Mathlib

namespace Work.Drive.Mono.Band

open scoped Topology

section Aux

/-- A continuous linear endomorphism of a finite-dimensional real vector space whose determinant
is non-zero is invertible (as a continuous linear equivalence). -/
lemma isInvertible_of_det_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] E) (h : f.det ≠ 0) : f.IsInvertible := by
  have hunit : IsUnit (f : E →ₗ[ℝ] E) :=
    (LinearMap.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (show LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0 from h))
  obtain ⟨u, hu⟩ := hunit
  set g : E →L[ℝ] E := (↑u⁻¹ : E →ₗ[ℝ] E).toContinuousLinearMap with hg
  have hcomp1 : f ∘L g = ContinuousLinearMap.id ℝ E := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    have h1 : (↑u : E →ₗ[ℝ] E) * ↑u⁻¹ = 1 := u.mul_inv
    have := congrArg (fun (L : E →ₗ[ℝ] E) => L x) h1
    simpa [g, Module.End.mul_apply, hu] using this
  have hcomp2 : g ∘L f = ContinuousLinearMap.id ℝ E := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    have h1 : (↑u⁻¹ : E →ₗ[ℝ] E) * ↑u = 1 := u.inv_mul
    have := congrArg (fun (L : E →ₗ[ℝ] E) => L x) h1
    simpa [g, Module.End.mul_apply, hu] using this
  exact ContinuousLinearMap.IsInvertible.of_inverse hcomp1 hcomp2

/-- If the derivative of a `C¹` map at a point is invertible, then the map is injective on some
neighbourhood of that point (the inverse function theorem). -/
lemma injOn_of_isInvertible_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ψ : E → E} {x₀ : E} (hΨ : ContDiffAt ℝ 1 Ψ x₀)
    (h : (fderiv ℝ Ψ x₀).IsInvertible) : ∃ U ∈ 𝓝 x₀, Set.InjOn Ψ U := by
  obtain ⟨A, hA⟩ := h
  have hderiv : HasFDerivAt Ψ (fderiv ℝ Ψ x₀) x₀ :=
    (hΨ.differentiableAt one_ne_zero).hasFDerivAt
  have hstrict : HasStrictFDerivAt Ψ (A : E →L[ℝ] E) x₀ := by
    rw [hA]
    exact hΨ.hasStrictFDerivAt' hderiv one_ne_zero
  refine ⟨(hstrict.toOpenPartialHomeomorph Ψ).source, ?_, ?_⟩
  · exact (hstrict.toOpenPartialHomeomorph Ψ).open_source.mem_nhds
      hstrict.mem_toOpenPartialHomeomorph_source
  · intro x hx y hy hxy
    exact (hstrict.toOpenPartialHomeomorph Ψ).injOn hx hy hxy

end Aux

/-- Sard in fixed dimension, packaged for the thin-slab genericity: for a `C^1` map
`Ψ : ℝ² → ℝ²` and a **compact** `K`, the set of target values whose fibre in `K` is infinite has
measure zero.  (Compactness is essential: `Ψ x y = (sin x, y)` has infinite fibres, so the
accumulation step really uses it.  `C^1` is exactly the right strength; fixed-dimension Sard works
at `C^1` because the source is `2`-dimensional.)

Proof sketch: an infinite fibre inside the compact `K` has an accumulation point `x₀`; if
`fderiv Ψ x₀` were invertible, the inverse function result would make `Ψ` locally injective at `x₀`;
hence every such value lies in `Ψ '' {x | det (fderiv ℝ Ψ x) = 0}`, which is null by Mathlib's
equal-dimension Sard `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`
(`Mathlib/MeasureTheory/Function/Jacobian.lean`).  Measurability of the bad set is not needed:
it suffices to exhibit it inside the null image. -/
theorem ae_finite_preimage {Ψ : ℝ × ℝ → ℝ × ℝ} (hΨ : ContDiff ℝ 1 Ψ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) :
    MeasureTheory.volume {y : ℝ × ℝ | (Ψ ⁻¹' {y} ∩ K).Infinite} = 0 := by
  set s : Set (ℝ × ℝ) := {x | (fderiv ℝ Ψ x).det = 0} with hs
  have hnull : MeasureTheory.volume (Ψ '' s) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (MeasureTheory.volume) (s := s) (f := Ψ) (f' := fun x => fderiv ℝ Ψ x) ?_ ?_
    · intro x _
      exact (hΨ.contDiffAt.differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hx
  refine MeasureTheory.measure_mono_null ?_ hnull
  rintro y hy
  -- an infinite fibre in the compact `K` has an accumulation point `x₀ ∈ K`
  obtain ⟨x₀, _, hacc⟩ := hy.exists_accPt_of_subset_isCompact hK Set.inter_subset_right
  have hcl : x₀ ∈ closure (Ψ ⁻¹' {y} ∩ K) :=
    mem_closure_iff_nhds.mpr (clusterPt_principal_iff.mp hacc.clusterPt)
  -- by continuity, `Ψ x₀ = y`
  have hx₀y : Ψ x₀ = y :=
    closure_minimal (fun z hz => hz.1) (isClosed_singleton.preimage hΨ.continuous) hcl
  refine ⟨x₀, ?_, hx₀y⟩
  -- if the derivative at `x₀` were invertible, `Ψ` would be injective near `x₀`,
  -- contradicting that `x₀` is an accumulation point of the fibre
  by_contra hdet
  have hinv : (fderiv ℝ Ψ x₀).IsInvertible := isInvertible_of_det_ne_zero _ hdet
  obtain ⟨U, hU, hUinj⟩ := injOn_of_isInvertible_fderiv hΨ.contDiffAt hinv
  obtain ⟨z, ⟨hzU, hzs⟩, hzx⟩ := (accPt_iff_nhds.mp hacc) U hU
  exact hzx (hUinj hzU (mem_of_mem_nhds hU) (by rw [hzs.1, hx₀y]))

end Work.Drive.Mono.Band
