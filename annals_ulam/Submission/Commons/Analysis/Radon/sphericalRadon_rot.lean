import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Commons.Analysis.Radon.toSphere_neg

namespace Commons.Analysis.Radon

open MeasureTheory
open scoped RealInnerProductSpace Pointwise

/-! ### Measure preservation on the unit sphere

A linear isometry equivalence `S : E ≃ₗᵢ[ℝ] F` between finite-dimensional real inner product
spaces restricts to an equivalence of the unit spheres which preserves the surface measures
`MeasureTheory.Measure.toSphere volume`.  This is the change-of-variables tool used below to
prove rotational invariance of the spherical Radon transform. -/

section Helpers

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A linear isometry equivalence preserves the unit sphere. -/
private lemma linearIsometryEquiv_mem_sphere_iff (S : E ≃ₗᵢ[ℝ] F) (x : E) :
    S x ∈ Metric.sphere (0 : F) 1 ↔ x ∈ Metric.sphere (0 : E) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, S.norm_map, Metric.mem_sphere, dist_zero_right]

/-- A linear isometry equivalence commutes with the pointwise scalar action on sets. -/
private lemma smul_preimage_linearIsometryEquiv (S : E ≃ₗᵢ[ℝ] F) (C : Set F) :
    Set.Ioo (0 : ℝ) 1 • (S ⁻¹' C) = S ⁻¹' (Set.Ioo (0 : ℝ) 1 • C) := by
  ext x
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    exact ⟨r, hr, S y, hy, by rw [map_smul]⟩
  · rintro ⟨r, hr, c, hc, hrc⟩
    refine ⟨r, hr, S.symm c, ?_, ?_⟩
    · rw [Set.mem_preimage, LinearIsometryEquiv.apply_symm_apply]
      exact hc
    · have := congrArg (⇑S.symm) hrc
      simp only [map_smul, LinearIsometryEquiv.symm_apply_apply] at this
      exact this

end Helpers

section IsometrySphere

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The unit-sphere map induced by a linear isometry equivalence `S : E ≃ₗᵢ[ℝ] F`. -/
noncomputable def sphereCongr (S : E ≃ₗᵢ[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ᵐ Metric.sphere (0 : F) 1 where
  toFun u :=
    ⟨S u, by rw [Metric.mem_sphere, dist_zero_right, S.norm_map]; exact norm_eq_of_mem_sphere u⟩
  invFun v :=
    ⟨S.symm v, by
      rw [Metric.mem_sphere, dist_zero_right, S.symm.norm_map]; exact norm_eq_of_mem_sphere v⟩
  left_inv u := by ext; simp
  right_inv v := by ext; simp
  measurable_toFun := by
    apply Continuous.measurable
    apply Continuous.subtype_mk
    exact S.continuous.comp continuous_subtype_val
  measurable_invFun := by
    apply Continuous.measurable
    apply Continuous.subtype_mk
    exact S.symm.continuous.comp continuous_subtype_val

@[simp] lemma sphereCongr_apply (S : E ≃ₗᵢ[ℝ] F) (u : Metric.sphere (0 : E) 1) :
    (sphereCongr S u : F) = S u := rfl

/-- The image under the coercion to `E` of the preimage of `s` under the induced sphere map is the
preimage under `S` of the image of `s` under the coercion to `F`. -/
private lemma image_val_sphereCongr_preimage (S : E ≃ₗᵢ[ℝ] F)
    (s : Set (Metric.sphere (0 : F) 1)) :
    (Subtype.val '' ((sphereCongr S) ⁻¹' s)) = S ⁻¹' (Subtype.val '' s) := by
  have h1 : (sphereCongr S) ⁻¹' s = Subtype.val ⁻¹' (S ⁻¹' (Subtype.val '' s)) := by
    ext u
    show sphereCongr S u ∈ s ↔ S ↑u ∈ Subtype.val '' s
    constructor
    · intro hu
      exact ⟨sphereCongr S u, hu, (sphereCongr_apply S u)⟩
    · rintro ⟨v, hv, hvu⟩
      have : sphereCongr S u = v := by
        apply Subtype.ext
        rw [sphereCongr_apply S u, hvu]
      simpa [this] using hv
  rw [h1, Subtype.image_preimage_coe]
  apply Set.inter_eq_right.2
  rintro x ⟨v, hv, hvu⟩
  exact (linearIsometryEquiv_mem_sphere_iff S x).1 (hvu ▸ v.2)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The unit-sphere map induced by a linear isometry equivalence is measure preserving for the
surface measures `MeasureTheory.Measure.toSphere volume`. -/
theorem sphereCongr_measurePreserving (S : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (sphereCongr S) ((volume : Measure E).toSphere)
      ((volume : Measure F).toSphere) := by
  refine ⟨(sphereCongr S).measurable, ?_⟩
  ext s hs
  rw [MeasurableEquiv.map_apply,
    Measure.toSphere_apply' (volume : Measure E) (hs.preimage (sphereCongr S).measurable),
    Measure.toSphere_apply' (volume : Measure F) hs, S.toLinearEquiv.finrank_eq]
  congr 1
  have hvol : (volume : Measure E)
      (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereCongr S) ⁻¹' s)))
      = (volume : Measure F) (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    rw [image_val_sphereCongr_preimage S s,
      smul_preimage_linearIsometryEquiv S (Subtype.val '' s)]
    exact MeasurePreserving.measure_preimage_equiv (f := S.toMeasurableEquiv)
      (LinearIsometryEquiv.measurePreserving S) _
  exact hvol

end IsometrySphere

/-- **Rotational invariance of the spherical Radon transform.**  If `k` is an orthogonal
transformation of `E` and `f` is invariant under `k` (`f (k x) = f x`), then the integral of `f`
over the equator `S^{d-1} ∩ ξ^⊥` depends on `ξ` only through the orbit of `k`:
`𝓡 f (k ξ) = 𝓡 f ξ`.  Here the equator is the unit sphere of the orthogonal complement
`(ℝ ∙ ξ)ᗮ`, with its intrinsic surface measure `MeasureTheory.Measure.toSphere`.

Proof route (same toolkit as `Commons.Analysis.Radon.toSphere_neg`, with `k` in place of `-`):
`Submodule.map_orthogonal_equiv` turns `(ℝ ∙ k ξ)ᗮ` into the image of `(ℝ ∙ ξ)ᗮ` under `k`, the
restricted isometry `(ℝ ∙ ξ)ᗮ ≃ᵢ (ℝ ∙ k ξ)ᗮ` preserves `volume` by
`LinearIsometryEquiv.measurePreserving`, hence preserves `volume.toSphere`, and the change of
variables converts `∫ f` into `∫ f ∘ k = ∫ f`. -/
theorem sphericalRadon_rot {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (k : E ≃ₗᵢ[ℝ] E) (f : E → ℝ) (hf : ∀ x, f (k x) = f x) (ξ : Metric.sphere (0 : E) 1) :
    (∫ ω : Metric.sphere (0 : ((ℝ ∙ (k ξ.1))ᗮ)) 1, f ((ω : ((ℝ ∙ (k ξ.1))ᗮ)) : E)
        ∂(MeasureTheory.Measure.toSphere (volume : Measure ((ℝ ∙ (k ξ.1))ᗮ))))
      = (∫ ω : Metric.sphere (0 : ((ℝ ∙ (ξ.1))ᗮ)) 1, f ((ω : ((ℝ ∙ (ξ.1))ᗮ)) : E)
        ∂(MeasureTheory.Measure.toSphere (volume : Measure ((ℝ ∙ (ξ.1))ᗮ)))) := by
  -- `k` maps the orthogonal complement of `ξ` onto the orthogonal complement of `k ξ`
  have hspan : Submodule.map (k.toLinearEquiv : E →ₗ[ℝ] E) (ℝ ∙ ξ.1) = ℝ ∙ k ξ.1 := by
    rw [Submodule.map_span, Set.image_singleton]
    simp [LinearIsometryEquiv.coe_toLinearEquiv]
  have hK : Submodule.map (k.toLinearEquiv : E →ₗ[ℝ] E) ((ℝ ∙ ξ.1)ᗮ) = (ℝ ∙ (k ξ.1))ᗮ := by
    rw [Submodule.map_orthogonal_equiv (ℝ ∙ ξ.1) k, hspan]
  -- the restricted isometry equivalence `(ℝ ∙ ξ)ᗮ ≃ᵢ (ℝ ∙ k ξ)ᗮ`
  let e : ((ℝ ∙ ξ.1)ᗮ) ≃ₗᵢ[ℝ] ((ℝ ∙ (k ξ.1))ᗮ) :=
    { k.toLinearEquiv.ofSubmodules ((ℝ ∙ ξ.1)ᗮ) ((ℝ ∙ (k ξ.1))ᗮ) hK with
      norm_map' := fun x => by
        simp [LinearEquiv.ofSubmodules_apply, LinearIsometryEquiv.coe_toLinearEquiv] }
  have he_coe : ∀ x : ((ℝ ∙ ξ.1)ᗮ),
      ((e x : ((ℝ ∙ (k ξ.1))ᗮ)) : E) = k ((x : ((ℝ ∙ ξ.1)ᗮ)) : E) := by
    intro x
    change (((k.toLinearEquiv.ofSubmodules ((ℝ ∙ ξ.1)ᗮ) ((ℝ ∙ (k ξ.1))ᗮ) hK) x :
      ((ℝ ∙ (k ξ.1))ᗮ)) : E) = k ((x : ((ℝ ∙ ξ.1)ᗮ)) : E)
    rw [LinearEquiv.ofSubmodules_apply]
    rfl
  -- change of variables along the induced measure preserving sphere map
  have hmp := sphereCongr_measurePreserving e
  have hint := hmp.integral_comp'
    (fun y : Metric.sphere (0 : ((ℝ ∙ (k ξ.1))ᗮ)) 1 => f ((y : ((ℝ ∙ (k ξ.1))ᗮ)) : E))
  rw [← hint]
  apply integral_congr_ae
  filter_upwards with x
  show f (((e x : ((ℝ ∙ (k ξ.1))ᗮ)) : E)) = f ((x : ((ℝ ∙ ξ.1))ᗮ) : E)
  rw [he_coe x, hf]

end Commons.Analysis.Radon