import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.W1L2Infra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

set_option linter.unusedVariables false

/-- If `f =ᵐ g` on `ℝ³`, then the pullback `p ↦ f (p 0 - p 1)` agrees with
`p ↦ g (p 0 - p 1)` almost everywhere on the two-particle centred box `abox 2 s`.

The set `{x | f x ≠ g x}` has Lebesgue measure zero; its `toMeasurable` hull `M` is a
measurable null set containing it, and `M` pulls back to a null set of
`volume.restrict (abox 2 s)` along the difference map `p ↦ p 0 - p 1`
(`abox_sub_preimage_null`); monotonicity of the outer measure finishes. -/
lemma sub_pullback_ae {s : ℝ} (hs : 0 < s)
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Measurable g)
    (hfg : f =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))] g) :
    (fun p : Submission.BoseGases.X 2 => f (p 0 - p 1))
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 s)]
      (fun p : Submission.BoseGases.X 2 => g (p 0 - p 1)) := by
  set G : Set (EuclideanSpace ℝ (Fin 3)) := {x | f x ≠ g x} with hG
  have hG0 : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) G = 0 := by
    have h := (MeasureTheory.ae_iff.mp hfg :
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        {a | ¬ f a = g a} = 0)
    simpa [G] using h
  refine MeasureTheory.ae_iff.mpr ?_
  refine MeasureTheory.measure_mono_null ?_ (abox_sub_preimage_null (s := s)
    (G := MeasureTheory.toMeasurable MeasureTheory.volume G)
    (MeasureTheory.measurableSet_toMeasurable _ _) ?_)
  · intro p hp
    exact MeasureTheory.subset_toMeasurable MeasureTheory.volume G hp
  · rw [MeasureTheory.measure_toMeasurable]; exact hG0

end Work.SmallBoxA0
