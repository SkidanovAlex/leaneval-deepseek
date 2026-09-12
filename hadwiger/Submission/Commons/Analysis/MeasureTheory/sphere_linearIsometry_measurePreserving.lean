import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Commons.Analysis.MeasureTheory.toSphere_neg_preimage

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise BigOperators

namespace Commons.Analysis.MeasureTheory

/-- The homeomorphism of the unit sphere induced by a linear isometry of the ambient space. -/
private def isometrySphere {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V ≃ₗᵢ[ℝ] V) : Metric.sphere (0 : V) 1 ≃ₜ Metric.sphere (0 : V) 1 where
  toFun θ := ⟨L θ.1, by
    simpa [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] using (mem_sphere_zero_iff_norm.mp θ.2)⟩
  invFun θ := ⟨L.symm θ.1, by
    simpa [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] using (mem_sphere_zero_iff_norm.mp θ.2)⟩
  left_inv θ := by
    apply Subtype.ext
    simp [LinearIsometryEquiv.symm_apply_apply]
  right_inv θ := by
    apply Subtype.ext
    simp [LinearIsometryEquiv.apply_symm_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The volume (Lebesgue measure) on `V` is invariant under a linear isometry,
even on non-measurable sets (we use the measurable equivalence associated to
the homeomorphism `L`). -/
private lemma volume_preimage_isometry {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (L : V ≃ₗᵢ[ℝ] V) (X : Set V) :
    volume ((L : V → V) ⁻¹' X) = volume X := by
  let e : V ≃ᵐ V := L.toHomeomorph.toMeasurableEquiv
  have he : ⇑e = (L : V → V) := rfl
  have hemap : Measure.map (⇑e) volume = volume := by
    simpa [he] using (LinearIsometryEquiv.measurePreserving L).map_eq
  calc
    volume ((L : V → V) ⁻¹' X) = volume ((e : V → V) ⁻¹' X) := by rw [he]
    _ = (volume.map e) X := (MeasurableEquiv.map_apply e X).symm
    _ = volume X := by rw [hemap]

/-- Pulling a cone back along a linear isomorphism yields the cone over the pullback. -/
private lemma cone_preimage_isometry {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V ≃ₗᵢ[ℝ] V) (B : Set V) :
    Ioo (0 : ℝ) 1 • ((L : V → V) ⁻¹' B) = (L : V → V) ⁻¹' (Ioo (0 : ℝ) 1 • B) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_smul] at hx
    rcases hx with ⟨r, hr, y, hy, hxy⟩
    rw [Set.mem_preimage]
    rw [Set.mem_preimage] at hy
    rw [Set.mem_smul]
    refine ⟨r, hr, (L : V → V) y, hy, ?_⟩
    calc
      r • ((L : V → V) y) = (L : V → V) (r • y) := by rw [map_smul]
      _ = (L : V → V) x := by rw [hxy]
  · intro hx
    rw [Set.mem_preimage] at hx
    rw [Set.mem_smul] at hx
    rcases hx with ⟨r, hr, b, hb, hLx⟩
    rw [Set.mem_smul]
    refine ⟨r, hr, (L.symm : V → V) b, ?_, ?_⟩
    · rw [Set.mem_preimage]
      simpa using hb
    · calc
        r • ((L.symm : V → V) b) = (L.symm : V → V) (r • b) := by rw [map_smul]
        _ = (L.symm : V → V) ((L : V → V) x) := by rw [hLx]
        _ = x := by simp

/-- Under the projection from the sphere to the ambient space, the preimage of a
set on the sphere corresponds to the preimage under `L` of its image. -/
private lemma isometrySphere_preimage_image {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V ≃ₗᵢ[ℝ] V) (A : Set (Metric.sphere (0 : V) 1)) :
    (fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' (isometrySphere L ⁻¹' A) =
      (L : V → V) ⁻¹' ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' A) := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rw [Set.mem_preimage]
    refine ⟨isometrySphere L θ, hθ, ?_⟩
    rfl
  · intro hx
    rw [Set.mem_preimage] at hx
    rcases hx with ⟨a, ha, hLx⟩
    have hmem : x ∈ Metric.sphere (0 : V) 1 := by
      rw [mem_sphere_zero_iff_norm]
      calc
        ‖x‖ = ‖(L : V → V) x‖ := (LinearIsometryEquiv.norm_map L x).symm
        _ = ‖(a : V)‖ := by rw [← hLx]
        _ = 1 := (mem_sphere_zero_iff_norm.mp a.2)
    refine ⟨⟨x, hmem⟩, ?_, rfl⟩
    have hEq : (isometrySphere L) ⟨x, hmem⟩ = a := by
      apply Subtype.ext
      change (L : V → V) (⟨x, hmem⟩ : Metric.sphere (0 : V) 1).1 = (a : V)
      exact hLx.symm
    simpa [hEq] using ha

/-- The homeomorphism of the unit sphere induced by a linear isometry of the
ambient finite-dimensional inner product space preserves the surface measure
`volume.toSphere` on the sphere.  This is the core statement: the surface
measure on a sphere is rotation invariant.  The proof computes the measure of
the preimage of a measurable set by the formula
`Measure.toSphere_apply'` (`toSphere s = finrank • volume (cone over s)`)
and uses the invariance of the volume measure under the isometry `L`. -/
private theorem isometrySphere_measurePreserving {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (L : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (isometrySphere L : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1)
      (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) volume.toSphere := by
  refine ⟨(isometrySphere L).measurable, ?_⟩
  apply Measure.ext
  intro A hA
  let f : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1 := isometrySphere L
  have hpre : MeasurableSet (f ⁻¹' A) := (isometrySphere L).measurable hA
  calc
    (Measure.map f (volume.toSphere : Measure (Metric.sphere (0 : V) 1))) A
        = (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) (f ⁻¹' A) := by
            rw [Measure.map_apply (isometrySphere L).measurable hA]
    _ = (↑(Module.finrank ℝ V) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' (f ⁻¹' A))) := by
            rw [Measure.toSphere_apply' (μ := (volume : Measure V)) (s := f ⁻¹' A) hpre]
    _ = (↑(Module.finrank ℝ V) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((L : V → V) ⁻¹' ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' A))) := by
            congr 1
            rw [isometrySphere_preimage_image L A]
    _ = (↑(Module.finrank ℝ V) : ℝ≥0∞) * volume
          ((L : V → V) ⁻¹' (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' A))) := by
            congr 1
            rw [cone_preimage_isometry L]
    _ = (↑(Module.finrank ℝ V) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' A)) := by
            congr 1
            rw [volume_preimage_isometry L]
    _ = (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) A := by
            rw [Measure.toSphere_apply' (μ := (volume : Measure V)) (s := A) hA]

theorem sphere_linearIsometry_measurePreserving
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    (f : V ≃ₗᵢ[ℝ] V) :
    MeasureTheory.MeasurePreserving
      (fun θ : Metric.sphere (0 : V) 1 =>
        (⟨f θ.1, by simpa [mem_sphere_zero_iff_norm] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1))
      MeasureTheory.volume.toSphere MeasureTheory.volume.toSphere := by
  have hMP : MeasurePreserving
      (isometrySphere f : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1)
      MeasureTheory.volume.toSphere MeasureTheory.volume.toSphere :=
    isometrySphere_measurePreserving (V := V) (L := f)
  have hfun : (fun θ : Metric.sphere (0 : V) 1 =>
        (⟨f θ.1, by simpa [mem_sphere_zero_iff_norm] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1)) =
      (isometrySphere f : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1) := by
    ext θ
    simp [isometrySphere]
  simpa [hfun] using hMP

end Commons.Analysis.MeasureTheory