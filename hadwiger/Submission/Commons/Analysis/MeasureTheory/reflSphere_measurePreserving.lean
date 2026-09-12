import Mathlib
import Submission.Commons.Analysis.MeasureTheory.toSphere_neg_preimage

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical

namespace Commons.Analysis.MeasureTheory

/-- The antipodal map on the unit sphere is measure preserving for the surface
measure `volume.toSphere`. -/
theorem reflSphere_measurePreserving
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V] :
    MeasureTheory.MeasurePreserving
      (fun θ : Metric.sphere (0 : V) 1 =>
        (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1))
      MeasureTheory.volume.toSphere MeasureTheory.volume.toSphere := by
  let S : Type _ := Metric.sphere (0 : V) 1
  let f : S → S := fun θ =>
    (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1)
  change MeasurePreserving f MeasureTheory.volume.toSphere MeasureTheory.volume.toSphere
  refine ⟨?_, ?_⟩
  · -- measurability of the antipodal map
    change Measurable f
    unfold f
    apply Measurable.subtype_mk
    exact measurable_neg.comp measurable_subtype_coe
  · -- measure preservation
    apply Measure.ext
    intro A hA
    rw [Measure.map_apply ?_ hA]
    · have hSmeas : MeasurableSet (Metric.sphere (0 : V) 1 : Set V) :=
        isClosed_sphere.measurableSet
      have hemb : MeasurableEmbedding (Subtype.val : S → V) :=
        (MeasurableEmbedding.subtype_coe hSmeas)
      let B : Set V := (Subtype.val : S → V) '' A
      have hBmeas : MeasurableSet B := by
        dsimp [B]
        exact hemb.measurableSet_image' hA
      have hBsub : B ⊆ Metric.sphere (0 : V) 1 := by
        intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact a.2
      have hpre : f ⁻¹' A = {θ : S | -(θ : V) ∈ B} := by
        ext θ
        constructor
        · intro hθ
          refine ⟨f θ, hθ, ?_⟩
          rfl
        · intro hθ
          rcases hθ with ⟨a, haA, hval⟩
          have hsame : f θ = a := by
            apply Subtype.ext
            simp [f, hval]  -- hval : val a = -(θ : V)
          simpa [hsame] using haA
      rw [hpre]
      rw [Commons.Analysis.MeasureTheory.toSphere_neg_preimage (V := V) B hBmeas hBsub]
      have hpost : {θ : S | (θ : V) ∈ B} = A := by
        ext θ
        constructor
        · intro hθ
          rcases hθ with ⟨a, haA, hval⟩
          have hsame : θ = a := by
            apply Subtype.ext
            simpa [B] using hval.symm
          simpa [hsame] using haA
        · intro hθ
          refine ⟨θ, hθ, rfl⟩
      rw [hpost]
    · -- measurability of f, needed for `Measure.map_apply`
      change Measurable f
      unfold f
      apply Measurable.subtype_mk
      exact measurable_neg.comp measurable_subtype_coe

end Commons.Analysis.MeasureTheory
