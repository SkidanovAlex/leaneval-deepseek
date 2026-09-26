import Mathlib
import Submission.Work.Sweep.LevelCount

open MeasureTheory Set
open scoped ENNReal

namespace Work.Sweep.CoareaMono

theorem lintegral_levelCount_eq_of_strictMonoOn {f f' : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hmono : StrictMonoOn f s)
    (hderiv : ∀ x ∈ s, HasDerivAt f (f' x) x) (w : ℝ → ENNReal) :
    ∫⁻ y, w y * Work.Sweep.levelCount f s y = ∫⁻ x in s, ENNReal.ofReal (f' x) * w (f x) := by
  have hlevel := Work.Sweep.levelCount_eq_indicator_of_injOn (f := f) (s := s) hmono.injOn
  have hfun : (fun y => w y * Work.Sweep.levelCount f s y) = (f '' s).indicator w := by
    funext y
    rw [hlevel]
    by_cases hy : y ∈ f '' s
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have himg : MeasurableSet (f '' s) := MeasurableSet.image_of_monotoneOn hs hmono.monotoneOn
  rw [hfun, MeasureTheory.lintegral_indicator himg w]
  exact MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hmono.monotoneOn w

end Work.Sweep.CoareaMono
