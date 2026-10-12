import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem prod_restrict_shift_eq_zero {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : MeasurableSet S)
    (c : EuclideanSpace ℝ (Fin 3)) {s : Set (EuclideanSpace ℝ (Fin 3))} (hs : MeasurableSet s)
    (hs0 : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) s = 0) :
    (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict S).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict S))
      {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.2 - p.1 + c ∈ s} = 0 := by
  -- The set is measurable: it is the preimage of `s` under the continuous map `p ↦ p.2 - p.1 + c`.
  have hmeas : MeasurableSet
      {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.2 - p.1 + c ∈ s} :=
    hs.preimage ((measurable_snd.sub measurable_fst).add_const c)
  rw [MeasureTheory.Measure.prod_apply hmeas]
  -- Fubini: it suffices that every vertical slice is null for the first marginal.
  have hzero : ∀ x : EuclideanSpace ℝ (Fin 3),
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict S)
        {a : EuclideanSpace ℝ (Fin 3) | a - x + c ∈ s} = 0 := by
    intro x
    -- The slice is a translate of `s`, so it is `volume`-null, hence also null for the
    -- restriction of `volume` to `S`.
    have hset : {a : EuclideanSpace ℝ (Fin 3) | a - x + c ∈ s}
        = (fun y : EuclideanSpace ℝ (Fin 3) => y + (c - x)) ⁻¹' s := by
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [show y - x + c = y + (c - x) by abel]
    rw [hset]
    refine le_antisymm ?_ (by simp)
    calc ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict S)
            ((fun y : EuclideanSpace ℝ (Fin 3) => y + (c - x)) ⁻¹' s)
        ≤ (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            ((fun y => y + (c - x)) ⁻¹' s) := MeasureTheory.Measure.restrict_apply_le _ _
      _ = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) s := by
          rw [MeasureTheory.measure_preimage_add_right]
      _ = 0 := hs0
  simp [hzero]

end Work.BoseBoxFock.PCFU
