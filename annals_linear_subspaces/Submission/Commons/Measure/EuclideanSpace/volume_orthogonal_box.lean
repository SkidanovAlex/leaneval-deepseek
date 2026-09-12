import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.orthogonalSplit_measurePreserving
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim

open MeasureTheory
open scoped ENNReal

namespace Commons.Measure.EuclideanSpace

/-- **Volume of an orthogonal product box.** For a subspace `V ⊆ ℝᵈ` of dimension `ℓ ≤ d`, the set `{v : ‖π_V v‖ ≤ A ∧ ‖π_{Vᗮ} v‖ ≤ δ}` is the image under the (measure preserving) orthogonal splitting map `(w,u) ↦ w + u : V × Vᗮ → ℝᵈ` of the product of the closed balls of radii `A` and `δ`; hence its volume is `A^ℓ δ^{d−ℓ}` times the product of the unit-ball volumes of dimensions `ℓ` and `d − ℓ`. Proof route: `Commons.Analysis.InnerProductSpace.orthogonalSplit_measurePreserving` (measure preserving splitting), `MeasureTheory.Measure.prod` on `V × Vᗮ` with `MeasureTheory.Measure.addHaar_real_closedBall` (ball volume scaling, `μ.real (closedBall x r) = r^finrank · μ.real (ball 0 1)`), and `Commons.Analysis.InnerProductSpace.unitBall_volume_eq_finrank` (to rewrite the unit-ball volumes of `V` and `Vᗮ` as those of `EuclideanSpace ℝ (Fin ℓ)` and `EuclideanSpace ℝ (Fin (d − ℓ))`). -/
theorem volume_orthogonal_box {d ℓ : ℕ} (hℓ : ℓ ≤ d)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hV : Module.finrank ℝ V = ℓ)
    {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    (MeasureTheory.volume {v : EuclideanSpace ℝ (Fin d) |
        ‖(V.starProjection v : EuclideanSpace ℝ (Fin d))‖ ≤ A ∧
        ‖((Vᗮ).starProjection v : EuclideanSpace ℝ (Fin d))‖ ≤ δ}).toReal =
      A ^ ℓ * δ ^ (d - ℓ) *
        (MeasureTheory.volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1)).toReal *
        (MeasureTheory.volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - ℓ))) 1)).toReal := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin d)) :=
    {v : EuclideanSpace ℝ (Fin d) |
      ‖(V.starProjection v : EuclideanSpace ℝ (Fin d))‖ ≤ A ∧
      ‖((Vᗮ).starProjection v : EuclideanSpace ℝ (Fin d))‖ ≤ δ} with hSdef
  -- The projections of an orthogonal sum are its two components.
  have hproj1 : ∀ p : V × Vᗮ,
      V.starProjection ((p.1 : EuclideanSpace ℝ (Fin d)) + (p.2 : EuclideanSpace ℝ (Fin d))) =
        (p.1 : EuclideanSpace ℝ (Fin d)) :=
    fun p => V.eq_starProjection_of_mem_orthogonal' p.1.property p.2.property rfl
  have hproj2 : ∀ p : V × Vᗮ,
      (Vᗮ).starProjection ((p.1 : EuclideanSpace ℝ (Fin d)) + (p.2 : EuclideanSpace ℝ (Fin d))) =
        (p.2 : EuclideanSpace ℝ (Fin d)) := by
    intro p
    refine (Vᗮ).eq_starProjection_of_mem_orthogonal' p.2.property
      (V.le_orthogonal_orthogonal p.1.property) ?_
    rw [add_comm]
  -- The preimage of `S` under the splitting map is the product of the two balls.
  have hpre : (fun p : V × Vᗮ =>
        (p.1 : EuclideanSpace ℝ (Fin d)) + (p.2 : EuclideanSpace ℝ (Fin d))) ⁻¹' S =
      Metric.closedBall (0 : V) A ×ˢ Metric.closedBall (0 : Vᗮ) δ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Metric.mem_closedBall, dist_zero_right, hSdef,
      Set.mem_ofPred_eq, hproj1 p, hproj2 p, Submodule.coe_norm]
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact ((isClosed_le (continuous_norm.comp V.starProjection.continuous)
      continuous_const).inter
      (isClosed_le (continuous_norm.comp (Vᗮ).starProjection.continuous)
        continuous_const)).measurableSet
  have hmp : MeasureTheory.MeasurePreserving
      (fun p : V × Vᗮ =>
        (p.1 : EuclideanSpace ℝ (Fin d)) + (p.2 : EuclideanSpace ℝ (Fin d)))
      MeasureTheory.volume MeasureTheory.volume :=
    Commons.Analysis.InnerProductSpace.orthogonalSplit_measurePreserving
      (E := EuclideanSpace ℝ (Fin d)) V
  have hvol : MeasureTheory.volume S =
      MeasureTheory.volume (Metric.closedBall (0 : V) A) *
        MeasureTheory.volume (Metric.closedBall (0 : Vᗮ) δ) := by
    calc MeasureTheory.volume S
        = MeasureTheory.volume ((fun p : V × Vᗮ =>
            (p.1 : EuclideanSpace ℝ (Fin d)) + (p.2 : EuclideanSpace ℝ (Fin d))) ⁻¹' S) :=
          (hmp.measure_preimage hSmeas.nullMeasurableSet).symm
      _ = MeasureTheory.volume
            (Metric.closedBall (0 : V) A ×ˢ Metric.closedBall (0 : Vᗮ) δ) := by rw [hpre]
      _ = MeasureTheory.volume (Metric.closedBall (0 : V) A) *
            MeasureTheory.volume (Metric.closedBall (0 : Vᗮ) δ) := by
          rw [MeasureTheory.Measure.volume_eq_prod V Vᗮ, MeasureTheory.Measure.prod_prod]
  have hA_real : (MeasureTheory.volume (Metric.closedBall (0 : V) A)).toReal =
      A ^ Module.finrank ℝ V *
        (MeasureTheory.volume (Metric.closedBall (0 : V) 1)).toReal := by
    simpa [MeasureTheory.measureReal_def] using MeasureTheory.Measure.addHaar_real_closedBall'
      (μ := (MeasureTheory.volume : MeasureTheory.Measure V)) (x := (0 : V)) hA.le
  have hδ_real : (MeasureTheory.volume (Metric.closedBall (0 : Vᗮ) δ)).toReal =
      δ ^ Module.finrank ℝ Vᗮ *
        (MeasureTheory.volume (Metric.closedBall (0 : Vᗮ) 1)).toReal := by
    simpa [MeasureTheory.measureReal_def] using MeasureTheory.Measure.addHaar_real_closedBall'
      (μ := (MeasureTheory.volume : MeasureTheory.Measure Vᗮ)) (x := (0 : Vᗮ)) hδ.le
  have hfinVperp : Module.finrank ℝ Vᗮ = d - ℓ := by
    have h := V.finrank_add_finrank_orthogonal (𝕜 := ℝ)
    rw [hV, finrank_euclideanSpace_fin] at h
    omega
  have hunitV : (MeasureTheory.volume (Metric.closedBall (0 : V) 1)).toReal =
      (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1)).toReal :=
    Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim (E := V) hV
  have hunitW : (MeasureTheory.volume (Metric.closedBall (0 : Vᗮ) 1)).toReal =
      (MeasureTheory.volume
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - ℓ))) 1)).toReal :=
    Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim (E := Vᗮ) hfinVperp
  calc (MeasureTheory.volume S).toReal
      = (MeasureTheory.volume (Metric.closedBall (0 : V) A) *
          MeasureTheory.volume (Metric.closedBall (0 : Vᗮ) δ)).toReal := by rw [hvol]
    _ = (MeasureTheory.volume (Metric.closedBall (0 : V) A)).toReal *
          (MeasureTheory.volume (Metric.closedBall (0 : Vᗮ) δ)).toReal :=
        ENNReal.toReal_mul
    _ = (A ^ Module.finrank ℝ V *
            (MeasureTheory.volume (Metric.closedBall (0 : V) 1)).toReal) *
          (δ ^ Module.finrank ℝ Vᗮ *
            (MeasureTheory.volume (Metric.closedBall (0 : Vᗮ) 1)).toReal) := by
        rw [hA_real, hδ_real]
    _ = A ^ ℓ * δ ^ (d - ℓ) *
          (MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1)).toReal *
          (MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - ℓ))) 1)).toReal := by
        rw [hV, hfinVperp, hunitV, hunitW]
        ring

end Commons.Measure.EuclideanSpace
