import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dictIIDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.dictIIAux

/-- A symmetric a.e. strongly measurable kernel has a **measurable symmetric** representative: given
`f` a.e. strongly measurable and pointwise symmetric (`f y w = f w y`), symmetrising any measurable
representative `F` of `f` by `g w y = (F (w,y) + F (y,w))/2` produces a measurable symmetric `g`
which is still a.e. equal to `f`.  The only measure-theoretic input is that the coordinate swap
`Prod.swap` preserves the (product) Lebesgue measure. -/
theorem symmMeasRep {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable (Function.uncurry f) MeasureTheory.volume)
    (hsym : ∀ w y, f y w = f w y) :
    ∃ g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ,
      Measurable (Function.uncurry g) ∧ (∀ w y, g w y = g y w) ∧
        Function.uncurry g =ᵐ[MeasureTheory.volume] Function.uncurry f := by
  classical
  refine ⟨fun w y => (hf.mk (Function.uncurry f) (w, y)
      + hf.mk (Function.uncurry f) (y, w)) / 2, ?_, ?_, ?_⟩
  · -- measurability: a sum of a measurable function and its swap-composition, divided by `2`
    have h1 : Measurable (hf.mk (Function.uncurry f)) := hf.measurable_mk
    have h2 : Measurable fun p : EuclideanSpace ℝ (Fin 3) × _ =>
        hf.mk (Function.uncurry f) (Prod.swap p) := h1.comp measurable_swap
    exact (h1.add h2).div_const 2
  · -- symmetry is built in
    intro w y; ring
  · -- a.e. equality: `Prod.swap` preserves `volume`, and `f` is symmetric
    have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving
        (Prod.swap : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → _)
        (MeasureTheory.volume) (MeasureTheory.volume) :=
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
        (ν := (MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3))))).quasiMeasurePreserving
    have hcomp := (hqmp.ae_eq_comp (hf.ae_eq_mk (f := Function.uncurry f))).symm
    filter_upwards [hf.ae_eq_mk (f := Function.uncurry f), hcomp] with p hp hp'
    have hp1 : f p.1 p.2 = hf.mk (Function.uncurry f) p := by
      simpa only [Function.uncurry] using hp
    have hp2 : hf.mk (Function.uncurry f) p.swap = f p.2 p.1 := by
      simpa only [Function.uncurry, Function.comp_apply, Prod.swap] using hp'
    show (hf.mk (Function.uncurry f) p + hf.mk (Function.uncurry f) p.swap) / 2 = f p.1 p.2
    rw [← hp1, hp2, hsym p.1 p.2]
    ring

end Work.BoseBoxFock.dictIIAux
