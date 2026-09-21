import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise BigOperators

namespace Commons.Analysis.MeasureTheory

/-- The homeomorphism between the unit spheres induced by a linear isometry of the
ambient inner product spaces. -/
private def isometrySphereEquiv {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    (L : V₁ ≃ₗᵢ[ℝ] V₂) : Metric.sphere (0 : V₁) 1 ≃ₜ Metric.sphere (0 : V₂) 1 where
  toFun θ := ⟨L θ.1, by
    exact mem_sphere_zero_iff_norm.mpr (by
      calc ‖L θ.1‖ = ‖θ.1‖ := LinearIsometryEquiv.norm_map L θ.1
           _ = 1 := mem_sphere_zero_iff_norm.mp θ.2)⟩
  invFun θ := ⟨L.symm θ.1, by
    exact mem_sphere_zero_iff_norm.mpr (by
      calc ‖L.symm θ.1‖ = ‖θ.1‖ := LinearIsometryEquiv.norm_map L.symm θ.1
           _ = 1 := mem_sphere_zero_iff_norm.mp θ.2)⟩
  left_inv θ := by
    apply Subtype.ext
    simp [LinearIsometryEquiv.symm_apply_apply]
  right_inv θ := by
    apply Subtype.ext
    simp [LinearIsometryEquiv.apply_symm_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Pulling a cone in `V₂` back along a linear isomorphism `V₁ → V₂` yields the cone
over the pullback. -/
private lemma cone_preimage_isometry {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    (L : V₁ ≃ₗᵢ[ℝ] V₂) (B : Set V₂) :
    Ioo (0 : ℝ) 1 • ((L : V₁ → V₂) ⁻¹' B) = (L : V₁ → V₂) ⁻¹' (Ioo (0 : ℝ) 1 • B) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_smul] at hx
    rcases hx with ⟨r, hr, y, hy, hxy⟩
    rw [Set.mem_preimage]
    rw [Set.mem_preimage] at hy
    rw [Set.mem_smul]
    refine ⟨r, hr, (L : V₁ → V₂) y, hy, ?_⟩
    calc
      r • ((L : V₁ → V₂) y) = (L : V₁ → V₂) (r • y) := by rw [map_smul]
      _ = (L : V₁ → V₂) x := by rw [hxy]
  · intro hx
    rw [Set.mem_preimage] at hx
    rw [Set.mem_smul] at hx
    rcases hx with ⟨r, hr, b, hb, hLx⟩
    rw [Set.mem_smul]
    refine ⟨r, hr, (L.symm : V₂ → V₁) b, ?_, ?_⟩
    · rw [Set.mem_preimage]
      simpa using hb
    · calc
        r • ((L.symm : V₂ → V₁) b) = (L.symm : V₂ → V₁) (r • b) := by rw [map_smul]
        _ = (L.symm : V₂ → V₁) ((L : V₁ → V₂) x) := by rw [hLx]
        _ = x := by simp

/-- The Lebesgue volume measure is invariant under a linear isometry between two
finite-dimensional real inner product spaces, even on non-measurable sets. -/
private lemma volume_preimage_isometry {V₁ V₂ : Type*} [NormedAddCommGroup V₁]
    [InnerProductSpace ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁] [FiniteDimensional ℝ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MeasurableSpace V₂]
    [BorelSpace V₂] [FiniteDimensional ℝ V₂]
    (L : V₁ ≃ₗᵢ[ℝ] V₂) (X : Set V₂) :
    volume ((L : V₁ → V₂) ⁻¹' X) = volume X := by
  let e : V₁ ≃ᵐ V₂ := L.toMeasurableEquiv
  have he : ⇑e = (L : V₁ → V₂) := rfl
  have hemap : Measure.map (⇑e) volume = volume := by
    simpa [he] using (LinearIsometryEquiv.measurePreserving L).map_eq
  calc
    volume ((L : V₁ → V₂) ⁻¹' X) = volume ((e : V₁ → V₂) ⁻¹' X) := by rw [he]
    _ = (volume.map e) X := (MeasurableEquiv.map_apply e X).symm
    _ = volume X := by rw [hemap]

/-- Under the projection from the sphere of `V₁` to `V₁`, the preimage under the sphere
isometry of a set on the sphere of `V₂` corresponds to the preimage under `L` of its image. -/
private lemma isometrySphereEquiv_preimage_image {V₁ V₂ : Type*} [NormedAddCommGroup V₁]
    [InnerProductSpace ℝ V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    (L : V₁ ≃ₗᵢ[ℝ] V₂) (A : Set (Metric.sphere (0 : V₂) 1)) :
    (fun θ : Metric.sphere (0 : V₁) 1 => (θ : V₁)) '' (isometrySphereEquiv L ⁻¹' A) =
      (L : V₁ → V₂) ⁻¹' ((fun θ : Metric.sphere (0 : V₂) 1 => (θ : V₂)) '' A) := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rw [Set.mem_preimage]
    refine ⟨isometrySphereEquiv L θ, hθ, ?_⟩
    rfl
  · intro hx
    rw [Set.mem_preimage] at hx
    rcases hx with ⟨a, ha, hLx⟩
    have hmem : x ∈ Metric.sphere (0 : V₁) 1 := by
      rw [mem_sphere_zero_iff_norm]
      calc
        ‖x‖ = ‖(L : V₁ → V₂) x‖ := (LinearIsometryEquiv.norm_map L x).symm
        _ = ‖(a : V₂)‖ := by rw [← hLx]
        _ = 1 := (mem_sphere_zero_iff_norm.mp a.2)
    refine ⟨⟨x, hmem⟩, ?_, rfl⟩
    have hEq : (isometrySphereEquiv L) ⟨x, hmem⟩ = a := by
      apply Subtype.ext
      change (L : V₁ → V₂) (⟨x, hmem⟩ : Metric.sphere (0 : V₁) 1).1 = (a : V₂)
      exact hLx.symm
    simpa [hEq] using ha

/-- The homeomorphism of the unit sphere induced by a linear isometry between the
ambient finite-dimensional inner product spaces preserves the surface measures
`volume.toSphere`.  The proof computes the measure of the preimage of a measurable set
by `Measure.toSphere_apply'` (`toSphere s = finrank • volume (cone over s)`) and
uses the invariance of the volume measure under the isometry `L`. -/
private theorem isometrySphereEquiv_measurePreserving {V₁ V₂ : Type*} [NormedAddCommGroup V₁]
    [InnerProductSpace ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁] [FiniteDimensional ℝ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MeasurableSpace V₂]
    [BorelSpace V₂] [FiniteDimensional ℝ V₂]
    (L : V₁ ≃ₗᵢ[ℝ] V₂) :
    MeasurePreserving (isometrySphereEquiv L : Metric.sphere (0 : V₁) 1 → Metric.sphere (0 : V₂) 1)
      (volume.toSphere : Measure (Metric.sphere (0 : V₁) 1)) volume.toSphere := by
  refine ⟨(isometrySphereEquiv L).measurable, ?_⟩
  apply Measure.ext
  intro A hA
  let f : Metric.sphere (0 : V₁) 1 → Metric.sphere (0 : V₂) 1 := isometrySphereEquiv L
  have hpre : MeasurableSet (f ⁻¹' A) := (isometrySphereEquiv L).measurable hA
  have hfin : (↑(Module.finrank ℝ V₁) : ℝ≥0∞) = ↑(Module.finrank ℝ V₂) := by
    rw [LinearEquiv.finrank_eq (LinearIsometryEquiv.toLinearEquiv L)]
  calc
    (Measure.map f (volume.toSphere : Measure (Metric.sphere (0 : V₁) 1))) A
        = (volume.toSphere : Measure (Metric.sphere (0 : V₁) 1)) (f ⁻¹' A) := by
            rw [Measure.map_apply (isometrySphereEquiv L).measurable hA]
    _ = (↑(Module.finrank ℝ V₁) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V₁) 1 => (θ : V₁)) '' (f ⁻¹' A))) := by
            rw [Measure.toSphere_apply' (μ := (volume : Measure V₁)) (s := f ⁻¹' A) hpre]
    _ = (↑(Module.finrank ℝ V₁) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((L : V₁ → V₂) ⁻¹' ((fun θ : Metric.sphere (0 : V₂) 1 => (θ : V₂)) '' A))) := by
            congr 1
            rw [isometrySphereEquiv_preimage_image L A]
    _ = (↑(Module.finrank ℝ V₁) : ℝ≥0∞) * volume
          ((L : V₁ → V₂) ⁻¹' (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V₂) 1 => (θ : V₂)) '' A))) := by
            congr 1
            rw [cone_preimage_isometry L]
    _ = (↑(Module.finrank ℝ V₁) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V₂) 1 => (θ : V₂)) '' A)) := by
            congr 1
            rw [volume_preimage_isometry L]
    _ = (↑(Module.finrank ℝ V₂) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V₂) 1 => (θ : V₂)) '' A)) := by
            rw [hfin]
    _ = (volume.toSphere : Measure (Metric.sphere (0 : V₂) 1)) A := by
            rw [Measure.toSphere_apply' (μ := (volume : Measure V₂)) (s := A) hA]

theorem sphere_isometry_measurableEquiv_measurePreserving
    {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [MeasurableSpace V₁]
    [BorelSpace V₁] [FiniteDimensional ℝ V₁] [Nontrivial V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MeasurableSpace V₂]
    [BorelSpace V₂] [FiniteDimensional ℝ V₂] [Nontrivial V₂]
    (L : V₁ ≃ₗᵢ[ℝ] V₂) :
    ∃ e : Metric.sphere (0 : V₁) 1 ≃ᵐ Metric.sphere (0 : V₂) 1,
      MeasureTheory.MeasurePreserving (⇑e)
        (MeasureTheory.volume.toSphere : MeasureTheory.Measure (Metric.sphere (0 : V₁) 1))
        (MeasureTheory.volume.toSphere : MeasureTheory.Measure (Metric.sphere (0 : V₂) 1)) ∧
      ∀ θ : Metric.sphere (0 : V₁) 1, ((e θ : Metric.sphere (0 : V₂) 1) : V₂) = L (θ : V₁) := by
  let h : Metric.sphere (0 : V₁) 1 ≃ₜ Metric.sphere (0 : V₂) 1 := isometrySphereEquiv L
  refine ⟨h.toMeasurableEquiv, ?_, ?_⟩
  · have hMP : MeasurePreserving
        (isometrySphereEquiv L : Metric.sphere (0 : V₁) 1 → Metric.sphere (0 : V₂) 1)
        (volume.toSphere : Measure (Metric.sphere (0 : V₁) 1)) volume.toSphere :=
      isometrySphereEquiv_measurePreserving (V₁ := V₁) (V₂ := V₂) (L := L)
    simpa [h] using hMP
  · intro θ
    rfl

end Commons.Analysis.MeasureTheory
