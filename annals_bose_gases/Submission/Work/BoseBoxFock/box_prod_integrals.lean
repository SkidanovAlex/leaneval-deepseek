import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.K1pairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

/-- **The three elementary double integrals over `Λ(ℓ) × Λ(ℓ)`.**

* the `(w,y) ↦ h (w - y)` fold `∫∫ ‖F (w-y)‖² = ℓ³ ∫ ‖F‖²` for an `ℓℤ³`-periodic, bounded `F`
  (Fubini to the iterated integral, then the fundamental-domain fold `periodic_double_fold`);
* the degenerate version with `F p.1` (the `y`-integral of a constant);
* the total mass `∫∫ c = c ℓ⁶` of the product of the two box measures.

The only non-elementary point is the Fubini step of the first two items: the (a.e. strongly
measurable) composition `p ↦ F (p.1 - p.2)` is `AEStronglyMeasurable` for `μ.prod μ`,
`μ = volume.restrict (Λ(ℓ))`, because `(w,y) ↦ w - y` is quasi-measure-preserving from
`volume.prod volume` to `volume` and `μ.prod μ ≪ volume.prod volume`. -/
theorem box_prod_integrals {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ {F : EuclideanSpace ℝ (Fin 3) → ℂ}, MeasureTheory.AEStronglyMeasurable F MeasureTheory.volume →
        (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
        (∀ (m : Fin 3 → ℤ) (z : EuclideanSpace ℝ (Fin 3)),
          F (z + ℓ • Work.BoseBoxFock.latVec m) = F z) →
      (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ‖F (p.1 - p.2)‖ ^ 2
          ∂((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
              (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))))
        = ℓ ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ‖F z‖ ^ 2)
    ∧ (∀ {F : EuclideanSpace ℝ (Fin 3) → ℂ}, MeasureTheory.AEStronglyMeasurable F MeasureTheory.volume →
        (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
      (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ‖F p.1‖ ^ 2
          ∂((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
              (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))))
        = ℓ ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ‖F z‖ ^ 2)
    ∧ (∀ c : ℝ, (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), c
          ∂((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
              (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)))) = c * ℓ ^ 6) := by
  -- pass to the closed cube `[-ℓ/2,ℓ/2]³ = Work.BoseFixR.cell ℓ`, where `periodic_double_fold` lives
  rw [corpusBox_boxL_eq_cell hℓ]
  -- the volume of the box
  have hboxvol : (volume : Measure E3) (Work.BoseFixR.cell ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
    rw [Work.BoseFixR.cell_eq_boxL]
    exact Work.BoseFixR.volume_boxL ℓ
  have hvolreal : volume.real (Work.BoseFixR.cell ℓ) = ℓ ^ 3 := by
    show (volume (Work.BoseFixR.cell ℓ)).toReal = ℓ ^ 3
    rw [hboxvol, ENNReal.toReal_ofReal (by positivity)]
  -- the restricted measure is finite
  haveI hfin : IsFiniteMeasure ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, hboxvol]
    exact ENNReal.ofReal_ne_top
  refine ⟨?_, ?_, ?_⟩
  · -- ## the fold `(w,y) ↦ ‖F (w-y)‖²`
    intro F hFmeas hFbound hFper
    obtain ⟨C, hC⟩ := hFbound
    have hle : ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)).prod
        ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ))
        ≤ (volume : Measure E3).prod (volume : Measure E3) :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    -- `(w,y) ↦ w - y` is quasi-measure-preserving (from the full product to the full volume)
    have hmeas : AEStronglyMeasurable (fun p : E3 × E3 => F (p.1 - p.2))
        (((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)).prod
          ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ))) :=
      hFmeas.comp_quasiMeasurePreserving
        ((MeasureTheory.quasiMeasurePreserving_sub (volume : Measure E3) (volume : Measure E3)).mono_left
          (Measure.absolutelyContinuous_of_le hle))
    have hInt : Integrable (fun p : E3 × E3 => ‖F (p.1 - p.2)‖ ^ 2)
        (((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)).prod
          ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ))) := by
      refine Integrable.of_bound (hmeas.norm.pow 2) (C ^ 2) ?_
      filter_upwards with p
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
    rw [integral_prod (fun p : E3 × E3 => ‖F (p.1 - p.2)‖ ^ 2) hInt]
    exact periodic_double_fold hℓ (h := fun z => ‖F z‖ ^ 2) (fun m z => by rw [hFper m z])
  · -- ## the degenerate fold `(w,y) ↦ ‖F w‖²`
    intro F hFmeas hFbound
    obtain ⟨C, hC⟩ := hFbound
    have hFμ : AEStronglyMeasurable F ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)) :=
      hFmeas.mono_measure Measure.restrict_le_self
    have hmeas : AEStronglyMeasurable (fun p : E3 × E3 => F p.1)
        (((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)).prod
          ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ))) :=
      hFμ.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_fst
    have hInt : Integrable (fun p : E3 × E3 => ‖F p.1‖ ^ 2)
        (((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)).prod
          ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ))) := by
      refine Integrable.of_bound (hmeas.norm.pow 2) (C ^ 2) ?_
      filter_upwards with p
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
    rw [integral_prod (fun p : E3 × E3 => ‖F p.1‖ ^ 2) hInt]
    have hinner : ∀ w : E3,
        (∫ y in Work.BoseFixR.cell ℓ, ‖F w‖ ^ 2) = ℓ ^ 3 * ‖F w‖ ^ 2 := by
      intro w
      rw [setIntegral_const, hvolreal, smul_eq_mul]
    simp_rw [hinner]
    rw [MeasureTheory.integral_const_mul]
  · -- ## the mass of the product of the two box measures
    intro c
    have hreal : (((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)).prod
        ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ))).real Set.univ = ℓ ^ 6 := by
      simp only [← Set.univ_prod_univ, MeasureTheory.measureReal_prod_prod,
        MeasureTheory.measureReal_restrict_apply_univ]
      rw [hvolreal]; ring
    rw [integral_const, hreal, smul_eq_mul]
    ring

end Work.BoseBoxFock
