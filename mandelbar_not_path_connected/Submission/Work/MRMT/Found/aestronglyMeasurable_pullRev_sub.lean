import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.QC.eLpNorm_fderiv_le_two_mul_add

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

/-- `pullRev μn f` is (strongly) measurable: it is a measurable function of `dz f`,
`dzbar f` and `μn ∘ f`, all of which are Borel measurable when `μn` is continuous and
`star ∘ f` is complex-differentiable (hence `f` is continuous). -/
theorem aestronglyMeasurable_pullRev_sub {μn f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f))
    (hμn : Continuous μn) :
    MeasureTheory.AEStronglyMeasurable (fun z => Work.MRMT.Found.pullRev μn f z - μn z)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have hfcont : Continuous f := by
    have h := continuous_star.comp hf.continuous
    simpa [Function.comp_def] using h
  have hdz : Measurable (Work.MRMT.dz f) := Work.MRMT.QC.measurable_dz f
  have hdzbar : Measurable (Work.MRMT.dzbar f) := Work.MRMT.QC.measurable_dzbar f
  have hcomp : Measurable (fun z => μn (f z)) := hμn.measurable.comp hfcont.measurable
  have hpull : Measurable (fun z => Work.MRMT.Found.pullRev μn f z) := by
    have h1 : Measurable (fun z => star (Work.MRMT.dz f z) + star (μn (f z)) * Work.MRMT.dzbar f z) :=
      (continuous_star.measurable.comp hdz).add ((continuous_star.measurable.comp hcomp).mul hdzbar)
    have h2 : Measurable (fun z => star (Work.MRMT.dzbar f z) + star (μn (f z)) * Work.MRMT.dz f z) :=
      (continuous_star.measurable.comp hdzbar).add ((continuous_star.measurable.comp hcomp).mul hdz)
    have h4 : (fun z => Work.MRMT.Found.pullRev μn f z)
        = ((fun z => star (Work.MRMT.dz f z) + star (μn (f z)) * Work.MRMT.dzbar f z) /
           (fun z => star (Work.MRMT.dzbar f z) + star (μn (f z)) * Work.MRMT.dz f z)) := by
      funext z
      simp only [Work.MRMT.Found.pullRev, Pi.div_apply]
    rw [h4]
    exact h1.div h2
  exact (hpull.sub hμn.measurable).aestronglyMeasurable

end Work.MRMT.Found
