import Mathlib
import Submission.Work.TMComp.Kotani.RectDefs

namespace Work.TMComp.Kotani

/-- Splitting a rectangle `[a,b] × [c,d]` at intermediate height `m` (with `c ≤ m ≤ d` the natural
case, but the identity is unconditional): the boundary integral over the big rectangle is the sum
of the boundary integrals over the two horizontal strips.  The two horizontal integrals at height
`m` cancel, and the vertical integrals combine by additivity of the interval integral over adjacent
intervals. -/
theorem rectBdIntegral_split {a b c d m : ℝ} {f : ℂ → ℂ}
    (hb1 : IntervalIntegrable (fun y : ℝ => f ((b:ℂ) + (y:ℂ) * Complex.I)) MeasureTheory.volume c m)
    (hb2 : IntervalIntegrable (fun y : ℝ => f ((b:ℂ) + (y:ℂ) * Complex.I)) MeasureTheory.volume m d)
    (ha1 : IntervalIntegrable (fun y : ℝ => f ((a:ℂ) + (y:ℂ) * Complex.I)) MeasureTheory.volume c m)
    (ha2 : IntervalIntegrable (fun y : ℝ => f ((a:ℂ) + (y:ℂ) * Complex.I)) MeasureTheory.volume m d) :
    Work.TMComp.Kotani.rectBdIntegral a b c d f
      = Work.TMComp.Kotani.rectBdIntegral a b m d f
        + Work.TMComp.Kotani.rectBdIntegral a b c m f := by
  simp only [rectBdIntegral]
  rw [← intervalIntegral.integral_add_adjacent_intervals hb1 hb2,
      ← intervalIntegral.integral_add_adjacent_intervals ha1 ha2]
  ring

end Work.TMComp.Kotani
