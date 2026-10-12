import Mathlib
import Submission.Work.BoseBoxFock.K1pairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem aesm_prod_comp_sub {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hm : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (c : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f (p.1 - p.2 + c))
      ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)))
    ∧ MeasureTheory.AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f p.1)
      ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)))
    ∧ MeasureTheory.AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f p.2)
      ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))) := by
  -- `volume` is invariant under translations, for every measurable set.
  have htrans : ∀ (t : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet t →
      ∀ a, MeasureTheory.volume ((fun y : EuclideanSpace ℝ (Fin 3) => y + a) '' t) =
        MeasureTheory.volume t := by
    intro t ht a
    have h := MeasureTheory.Measure.measure_preimage_of_map_eq_self
      (f := fun z : EuclideanSpace ℝ (Fin 3) => z + (-a))
      (MeasureTheory.map_add_right_eq_self MeasureTheory.volume (-a))
        (measurable_add_const (-a)).aemeasurable ht.nullMeasurableSet
    rw [Set.image_add_right]
    exact h
  -- The reflected difference `p.2 - p.1 + c` is quasi-measure preserving.
  have hQMP'' : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.2 - p.1 + c)
      ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)))
      MeasureTheory.volume := by
    refine ⟨by fun_prop, ?_⟩
    refine MeasureTheory.Measure.AbsolutelyContinuous.mk (fun s hs hvol => ?_)
    rw [MeasureTheory.Measure.map_apply (by fun_prop : Measurable (fun p : EuclideanSpace ℝ (Fin 3) ×
          EuclideanSpace ℝ (Fin 3) => p.2 - p.1 + c)) hs,
      MeasureTheory.Measure.prod_apply (hs.preimage (by fun_prop : Measurable (fun p : EuclideanSpace ℝ (Fin 3) ×
          EuclideanSpace ℝ (Fin 3) => p.2 - p.1 + c)))]
    -- every slice is a translate of `s`, hence null
    have hinner : ∀ x : EuclideanSpace ℝ (Fin 3),
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))
          (Prod.mk x ⁻¹' ((fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            p.2 - p.1 + c) ⁻¹' s)) = 0 := by
      intro x
      have h1 : (Prod.mk x ⁻¹' ((fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            p.2 - p.1 + c) ⁻¹' s))
          = (fun y : EuclideanSpace ℝ (Fin 3) => y + (x - c)) '' s := by
        ext y
        simp only [Set.mem_preimage]
        constructor
        · intro hy
          exact ⟨y - x + c, hy, by abel_nf⟩
        · rintro ⟨z, hz, hzy⟩
          rw [← hzy]
          convert hz using 2
          simp only [neg_one_smul]
          abel
      rw [h1]
      have hmeas : MeasurableSet ((fun y : EuclideanSpace ℝ (Fin 3) => y + (x - c)) '' s) := by
        rw [Set.image_add_right]
        exact hs.preimage (by fun_prop)
      rw [MeasureTheory.Measure.restrict_apply hmeas]
      exact le_antisymm (le_trans (MeasureTheory.measure_mono (Set.inter_subset_left))
        (le_of_eq (htrans s hs (x - c) |>.trans hvol))) zero_le
    rw [MeasureTheory.lintegral_congr hinner]
    simp
  -- Precomposing with the measure preserving swap turns `T''` into `T`.
  have hQMP : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.1 - p.2 + c)
      ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)))
      MeasureTheory.volume := by
    have hswap : MeasureTheory.Measure.QuasiMeasurePreserving
        (Prod.swap : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) →
          EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
          (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)))
        ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
          (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))) :=
      ⟨measurable_swap, by rw [MeasureTheory.Measure.prod_swap]⟩
    have hcomp := hQMP''.comp hswap
    simpa [Function.comp_def] using hcomp
  refine ⟨hm.comp_quasiMeasurePreserving hQMP, ?_, ?_⟩
  · exact (hm.mono_measure MeasureTheory.Measure.restrict_le_self).comp_fst
  · exact (hm.mono_measure MeasureTheory.Measure.restrict_le_self).comp_snd

end Work.BoseBoxFock
