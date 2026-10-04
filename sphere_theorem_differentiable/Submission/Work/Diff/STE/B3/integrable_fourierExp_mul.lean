import Mathlib
import Submission.Work.Diff.STE.bessel_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

theorem integrable_fourierExp_mul {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℂ} (m : ι → ℤ)
    (hf : MeasureTheory.Integrable f MeasureTheory.volume) :
    MeasureTheory.Integrable (fun z => Work.Diff.STE.fourierExp m z * f z)
      MeasureTheory.volume := by
  classical
  refine hf.bdd_mul (c := 1)
    (Work.Diff.STE.BesselCont.continuous_fourierExp_char m).aestronglyMeasurable ?_
  filter_upwards with z
  simp [Work.Diff.STE.BesselCont.norm_fourierExp_char]

end Work.Diff.STE.B3
