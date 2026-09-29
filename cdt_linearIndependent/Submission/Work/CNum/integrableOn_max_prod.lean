import Mathlib

namespace Work.CNum

open MeasureTheory Set

/-- The maximum of `g` over the two coordinates is integrable on the unit square of `(0,1]²`
whenever `g` is continuous on `[0,1]`.  The bound comes from compactness of `[0,1]`, the
measurability from continuity on the compact square (and the fact that `(0,1]² ⊆ [0,1]²`), and
the finiteness of the measure from `volume (Ioc 0 1) = 1`. -/
theorem integrableOn_max_prod {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc (0:ℝ) 1)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => max (g p.1) (g p.2))
      (Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1) (MeasureTheory.volume.prod MeasureTheory.volume) := by
  set A : Set (ℝ × ℝ) := Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1 with hA
  set S : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 with hS
  have hmemS : ∀ p : ℝ × ℝ, p ∈ S ↔ p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ∈ Set.Icc (0:ℝ) 1 := by
    intro p; rw [hS]; exact Set.mem_prod
  have hmemA : ∀ p : ℝ × ℝ, p ∈ A ↔ p.1 ∈ Set.Ioc (0:ℝ) 1 ∧ p.2 ∈ Set.Ioc (0:ℝ) 1 := by
    intro p; rw [hA]; exact Set.mem_prod
  -- `(0,1]² ⊆ [0,1]²`
  have hAS : A ⊆ S := by
    intro p hp
    rw [hmemS, hmemA] at *
    exact ⟨Ioc_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩
  -- continuity of the two projections of `g` on the closed square
  have hcont1 : ContinuousOn (fun p : ℝ × ℝ => g p.1) S :=
    hg.comp' continuous_fst.continuousOn (fun p hp => ((hmemS p).mp hp).1)
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => g p.2) S :=
    hg.comp' continuous_snd.continuousOn (fun p hp => ((hmemS p).mp hp).2)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => max (g p.1) (g p.2)) S := by
    simpa using hcont1.sup hcont2
  have hScompact : IsCompact S := by rw [hS]; exact isCompact_Icc.prod isCompact_Icc
  have hAmeas : MeasurableSet A := by rw [hA]; exact measurableSet_Ioc.prod measurableSet_Ioc
  -- almost-everywhere strong measurability with respect to the restricted measure on `A`
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => max (g p.1) (g p.2))
      ((volume.prod volume).restrict A) :=
    hcont.aestronglyMeasurable_of_subset_isCompact hScompact hAmeas hAS
  -- a uniform bound from compactness
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn hcont
  refine IntegrableOn.of_bound ?_ haesm C ?_
  · rw [hA, Measure.prod_prod, Real.volume_Ioc]
    simp
  · filter_upwards [ae_restrict_mem hAmeas] with p hp
    exact hC p (hAS hp)

end Work.CNum
