import Mathlib
import Submission.Commons.Analysis.MeasureTheory.sphere_linearIsometry_measurePreserving

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.Analysis.MeasureTheory

private def isometrySphereEquiv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (f : V ≃ₗᵢ[ℝ] V) :
    Metric.sphere (0 : V) 1 ≃ᵐ Metric.sphere (0 : V) 1 where
  toFun θ := ⟨f θ.1, by
    simpa [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] using (mem_sphere_zero_iff_norm.mp θ.2)⟩
  invFun θ := ⟨f.symm θ.1, by
    simpa [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] using (mem_sphere_zero_iff_norm.mp θ.2)⟩
  left_inv θ := by
    apply Subtype.ext
    simp [LinearIsometryEquiv.symm_apply_apply]
  right_inv θ := by
    apply Subtype.ext
    simp [LinearIsometryEquiv.apply_symm_apply]
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact f.continuous.measurable.comp measurable_subtype_coe
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact f.symm.continuous.measurable.comp measurable_subtype_coe

/-- A linear isometry of the ambient space acts on the unit sphere as a
measure-preserving measurable equivalence for the surface measure
`volume.toSphere`. -/
private lemma isometrySphereEquiv_measurePreserving {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    [Nontrivial V] (f : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (isometrySphereEquiv f : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1)
      (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) volume.toSphere := by
  change MeasurePreserving (fun θ : Metric.sphere (0 : V) 1 =>
      (⟨f θ.1, by simpa [mem_sphere_zero_iff_norm] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1))
      (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) volume.toSphere
  exact sphere_linearIsometry_measurePreserving (V := V) f

/-- The cosine kernel `|⟨u, ·⟩|` on the sphere is invariant under the joint
rotation of the test vector `u` and the integration variable: rotating the
integration variable back by `f⁻¹` (which preserves the surface measure)
transforms the integrand `|⟨u, θ⟩| g (f θ)` into `|⟨f u, θ⟩| g θ`.  This is
the rotation invariance of the cosine transform used throughout the
Hadwiger/Funk–Hecke analysis. -/
theorem cosine_rotate
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    (f : V ≃ₗᵢ[ℝ] V) (g : Metric.sphere (0 : V) 1 → ℝ) (u : V) :
    (∫ θ : Metric.sphere (0 : V) 1,
        |inner ℝ u (θ : V)| * g
          (⟨f θ.1, by simpa [mem_sphere_zero_iff_norm] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1)
      ∂MeasureTheory.volume.toSphere) =
    (∫ θ : Metric.sphere (0 : V) 1, |inner ℝ (f u) (θ : V)| * g θ ∂MeasureTheory.volume.toSphere) := by
  let e : Metric.sphere (0 : V) 1 ≃ᵐ Metric.sphere (0 : V) 1 := isometrySphereEquiv f
  let R : Metric.sphere (0 : V) 1 → ℝ := fun θ => |inner ℝ (f u) (θ : V)| * g θ
  have h_mp : MeasurePreserving (e : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1)
      (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) volume.toSphere := by
    exact isometrySphereEquiv_measurePreserving f
  have hint :
      (∫ θ : Metric.sphere (0 : V) 1, R (e θ) ∂(volume.toSphere : Measure (Metric.sphere (0 : V) 1))) =
      (∫ θ : Metric.sphere (0 : V) 1, R θ ∂(volume.toSphere : Measure (Metric.sphere (0 : V) 1))) :=
    MeasurePreserving.integral_comp' (f := e) h_mp R
  calc
    (∫ θ : Metric.sphere (0 : V) 1,
        |inner ℝ u (θ : V)| * g
          (⟨f θ.1, by simpa [mem_sphere_zero_iff_norm] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1)
      ∂MeasureTheory.volume.toSphere)
        = ∫ θ : Metric.sphere (0 : V) 1, R (e θ) ∂(volume.toSphere : Measure (Metric.sphere (0 : V) 1)) := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro θ
          change |inner ℝ u (θ : V)| * g (⟨f θ.1, _⟩ : Metric.sphere (0 : V) 1)
            = |inner ℝ (f u) ((e θ) : V)| * g (e θ)
          rw [show (e θ : V) = f (θ : V) by rfl]
          congr 1
          · congr 1
            exact (LinearIsometryEquiv.inner_map_map f u (θ : V)).symm
    _ = (∫ θ : Metric.sphere (0 : V) 1, |inner ℝ (f u) (θ : V)| * g θ ∂MeasureTheory.volume.toSphere) := by
          simpa [R] using hint

end Commons.Analysis.MeasureTheory
