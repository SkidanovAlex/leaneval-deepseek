import Mathlib

namespace Work.WilE7.DimAPI

/-- A continuous linear endomorphism of a finite-dimensional real normed space whose determinant
is nonzero is surjective. (Over a field, a finite-dimensional endomorphism is surjective if and
only if its determinant is nonzero.) -/
theorem surjective_of_det_ne_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (f : F →L[ℝ] F) (h : f.det ≠ 0) :
    Function.Surjective f := by
  change Function.Surjective ⇑(f : F →ₗ[ℝ] F)
  have hb : IsUnit (LinearMap.toMatrix (Module.finBasis ℝ F) (Module.finBasis ℝ F)
      (f : F →ₗ[ℝ] F)).det := by
    rw [LinearMap.det_toMatrix]
    exact isUnit_iff_ne_zero.2 h
  rw [← LinearEquiv.coe_ofIsUnitDet (v := Module.finBasis ℝ F) (v' := Module.finBasis ℝ F)
    (f := (f : F →ₗ[ℝ] F)) hb]
  exact (LinearEquiv.ofIsUnitDet hb).surjective

theorem eventually_surjective_of_det_ne_zero {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (G : X → (F →L[ℝ] F)) {c : X} (hG : ContinuousAt G c) (h : (G c).det ≠ 0) :
    ∀ᶠ x in nhds c, Function.Surjective (G x) := by
  have hcont : ContinuousAt (fun x => (G x).det) c :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hG
  filter_upwards [hcont.eventually_ne h] with x hx
  exact surjective_of_det_ne_zero (G x) hx

end Work.WilE7.DimAPI
