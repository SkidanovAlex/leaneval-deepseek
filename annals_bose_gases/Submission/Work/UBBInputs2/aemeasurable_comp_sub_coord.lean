import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs2.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs2

open MeasureTheory

/-- Please place this result in namespace `Work.UBBInputs2` (file
`Submission/Work/UBBInputs2/aemeasurable_comp_sub_coord.lean`). Note the statement is written with
fully qualified `MeasureTheory.` names so that it elaborates without any `open`.

Delegated piece of `Work.UBBInputs2.integrable_qLHSBIntegrand`: a.e.-measurability of the composite
`q ↦ u (q.1.2 i - q.2)` on the triple space `(ℝ³ × X N) × ℝ³` equipped with
`(volume.prod volume).prod (volume.restrict (acube L))`, for an a.e.-measurable `u : ℝ³ → ℝ`.
Here `Submission.BoseGases.X N = Fin N → ℝ³`.

Proof sketch (same `AEMeasurable.mk` reduction as in `aemeasurable_comp_sub_index`): let
`w := AEMeasurable.mk u hu` (measurable, `u =ᵐ w`), then `q ↦ w (q.1.2 i - q.2)` is measurable
(composition with the continuous map `q ↦ q.1.2 i - q.2`). Their difference vanishes off
`{q | q.1.2 i - q.2 ∈ T}` for a measurable null set `T ⊇ {y | u y ≠ w y}`
(`MeasureTheory.exists_measurable_superset_of_null`); that set is null by
`MeasureTheory.Measure.prod_apply` applied to it (it is measurable): its measure is
`∫⁻ p, (volume.restrict (acube L)) {y | p.2 i - y ∈ T}`, and each fibre is zero because the map
`y ↦ p.2 i - y` is measure-preserving (`measurePreserving_neg` composed with
`measurePreserving_sub_right`, then `MeasureTheory.MeasurePreserving.measure_preimage`) and `T` is
null; intersecting with `acube L` preserves nullity. Conclude with
`MeasureTheory.AEStronglyMeasurable.congr`. -/
theorem aemeasurable_comp_sub_coord {N : ℕ} {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : AEMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) (i : Fin N)
    (L : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
          EuclideanSpace ℝ (Fin 3) => u (q.1.2 i - q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube L))) := by
  set w : EuclideanSpace ℝ (Fin 3) → ℝ := hu.mk u with hwdef
  have hw : Measurable w := by rw [hwdef]; exact hu.measurable_mk
  have huw : u =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))] w := by
    rw [hwdef]; exact hu.ae_eq_mk
  have hφ_meas : Measurable
      (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
        EuclideanSpace ℝ (Fin 3) => q.1.2 i - q.2) := by
    fun_prop
  have hcomp : MeasureTheory.AEStronglyMeasurable
      (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
        EuclideanSpace ℝ (Fin 3) => w (q.1.2 i - q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube L))) :=
    hw.aestronglyMeasurable.comp_measurable hφ_meas
  refine hcomp.congr ?_
  have hT0 : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      {y | u y ≠ w y} = 0 := by
    simpa using MeasureTheory.ae_iff.mp huw
  obtain ⟨T, hTsub, hTmeas, hTnull⟩ := MeasureTheory.exists_measurable_superset_of_null hT0
  set S : Set ((EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
      EuclideanSpace ℝ (Fin 3)) := {q | q.1.2 i - q.2 ∈ T} with hSdef
  have hS_meas : MeasurableSet S := by
    rw [hSdef]; exact hTmeas.preimage hφ_meas
  have hS_null : (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube L))) S = 0 := by
    rw [MeasureTheory.Measure.prod_apply hS_meas]
    have hfib : ∀ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N,
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube L)) (Prod.mk p ⁻¹' S) = 0 := by
      intro p
      have hset : Prod.mk p ⁻¹' S =
          (fun y : EuclideanSpace ℝ (Fin 3) => p.2 i - y) ⁻¹' T := by
        rw [hSdef]; ext y; simp
      rw [hset]
      have hpmp : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin 3) => p.2 i - y)
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
        convert (Measure.measurePreserving_neg
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).comp
            (measurePreserving_sub_right
              (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
              (p.2 i)) using 1
        ext y
        simp [Function.comp, neg_sub]
      have hbound : ((MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube L))
            ((fun y : EuclideanSpace ℝ (Fin 3) => p.2 i - y) ⁻¹' T) ≤ 0 := by
        calc ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube L)) ((fun y : EuclideanSpace ℝ (Fin 3) => p.2 i - y) ⁻¹' T)
            ≤ (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
                ((fun y : EuclideanSpace ℝ (Fin 3) => p.2 i - y) ⁻¹' T) := Measure.restrict_le_self _
          _ = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) T :=
                hpmp.measure_preimage hTmeas.nullMeasurableSet
          _ = 0 := hTnull
      exact le_antisymm hbound zero_le
    simp only [hfib, MeasureTheory.lintegral_zero]
  have hsub : {q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
        EuclideanSpace ℝ (Fin 3) | w (q.1.2 i - q.2) ≠ u (q.1.2 i - q.2)} ⊆ S := by
    intro q hq
    rw [hSdef]
    by_contra hmem
    exact hq (not_not.mp (fun h => hmem (hTsub h))).symm
  have hdiff : (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube L)))
        {q | w (q.1.2 i - q.2) ≠ u (q.1.2 i - q.2)} = 0 :=
    MeasureTheory.measure_mono_null hsub hS_null
  exact MeasureTheory.ae_iff.mpr hdiff

end Work.UBBInputs2
