import Mathlib
import Submission.Work.Mostow.stdFermiDefs

/-!
# `coordMap` pushes the planar Lebesgue measure to the Lebesgue measure of `E 2`

`FermiTwo.coordMap p = p.1 • axis + p.2 • axisPerp` is the linear coordinate identification
`(s,r) ↦ ![s,r]` read through the `WithLp 2` wrapper that presents `Fin 2 → ℝ` as the Euclidean
space `E 2 = EuclideanSpace ℝ (Fin 2)`.  Consequently it pushes `volume.prod volume` on `ℝ × ℝ`
forward to the translation invariant Lebesgue measure `volume` of `E 2`.

The proof factors `coordMap` as

  `coordMap = WithLp.toLp 2 ∘ (MeasurableEquiv.finTwoArrow ℝ).symm`,

the composition of the two standard volume preserving identifications
`ℝ × ℝ ≃ᵐ (Fin 2 → ℝ)` and `(Fin 2 → ℝ) ≃ᵐ E 2`.
-/

namespace Work.Mostow

open Submission.Mostow MeasureTheory

/-- `coordMap` is the linear coordinate identification `(s,r) ↦ ![s,r]` read through the
`WithLp 2` wrapper turning `Fin 2 → ℝ` into `E 2 = EuclideanSpace ℝ (Fin 2)`. -/
private lemma fermiTwo_coordMap_eq_toLp (p : ℝ × ℝ) :
    FermiTwo.coordMap p = WithLp.toLp 2 (![p.1, p.2] : Fin 2 → ℝ) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [FermiTwo.coordMap, FermiTwo.axis, FermiTwo.axisPerp]

theorem stdFermiCoordMapMap :
    MeasureTheory.Measure.map Work.Mostow.FermiTwo.coordMap
        (MeasureTheory.Measure.prod (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E 2)) := by
  -- `coordMap` is the composition of the two standard volume-preserving identifications.
  have hfun : FermiTwo.coordMap =
      (fun x : Fin 2 → ℝ => WithLp.toLp 2 x) ∘ (MeasurableEquiv.finTwoArrow (α := ℝ)).symm := by
    funext p
    rw [Function.comp_apply, MeasurableEquiv.finTwoArrow_symm_apply]
    exact fermiTwo_coordMap_eq_toLp p
  have hmp : MeasurePreserving FermiTwo.coordMap
      (Measure.prod (volume : Measure ℝ) (volume : Measure ℝ))
      (volume : Measure (E 2)) := by
    rw [hfun]
    exact (PiLp.volume_preserving_toLp (Fin 2)).comp ((volume_preserving_finTwoArrow ℝ).symm)
  exact hmp.map_eq

end Work.Mostow
