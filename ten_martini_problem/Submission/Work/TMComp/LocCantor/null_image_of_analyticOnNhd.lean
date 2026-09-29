import Mathlib

namespace Work.TMComp.LocCantor

theorem null_image_of_analyticOnNhd {a b : ℝ} {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f (Set.Ioo a b))
    {s : Set ℝ} (hs : s ⊆ Set.Ioo a b) (h0 : MeasureTheory.volume s = 0) :
    MeasureTheory.volume (f '' s) = 0 := by
  have hdiff : DifferentiableOn ℝ f s := (hf.differentiableOn).mono hs
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    MeasureTheory.volume hdiff h0

end Work.TMComp.LocCantor
