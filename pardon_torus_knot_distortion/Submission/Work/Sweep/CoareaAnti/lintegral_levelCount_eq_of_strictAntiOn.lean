import Mathlib
import Submission.Work.Sweep.LevelCount

/-!
# One-dimensional coarea formula for a strictly antitone function

For a strictly antitone function `f` on a measurable set `s` on which `f` is differentiable, the
"level count" form of the coarea formula holds:

`∫⁻ y, w y * levelCount f s y = ∫⁻ x in s, ENNReal.ofReal (-(f' x)) * w (f x)`.

Since `f` is injective on `s` (`StrictAntiOn.injOn`), the level count is the indicator function of
the image `f '' s`, so the left-hand side is the integral of `w` over `f '' s`.  The statement is
then exactly Mathlib's change-of-variables formula for antitone functions,
`MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn`, which is valid for an
arbitrary (not necessarily measurable) weight `w`.
-/

namespace Work.Sweep.CoareaAnti

theorem lintegral_levelCount_eq_of_strictAntiOn {f f' : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hanti : StrictAntiOn f s)
    (hderiv : ∀ x ∈ s, HasDerivAt f (f' x) x) (w : ℝ → ENNReal) :
    ∫⁻ y, w y * Work.Sweep.levelCount f s y = ∫⁻ x in s, ENNReal.ofReal (-(f' x)) * w (f x) := by
  have hmeas : MeasurableSet (f '' s) := hs.image_of_antitoneOn hanti.antitoneOn
  -- `StrictAntiOn` gives injectivity, so the level count is the indicator of the image.
  have key : ∫⁻ y, w y * Work.Sweep.levelCount f s y = ∫⁻ y in f '' s, w y := by
    rw [Work.Sweep.levelCount_eq_indicator_of_injOn hanti.injOn]
    rw [← MeasureTheory.lintegral_indicator hmeas w]
    refine MeasureTheory.lintegral_congr fun y => ?_
    by_cases hy : y ∈ f '' s
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  rw [key, MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hanti.antitoneOn w]

end Work.Sweep.CoareaAnti
