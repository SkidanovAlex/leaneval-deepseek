import Mathlib
import Submission.Work.OddEnvelope.Defs

namespace Work.OddEnvelope.Semicircle

/-- The unit semicircle `t ↦ √(1-t²)` is differentiable on `(-1,1)` with derivative
`t ↦ -t / √(1-t²)`: the derivative of `√u` at `u = 1-t² > 0` is
`u' / (2√u) = (-2t)/(2√(1-t²)) = -t/√(1-t²)`. -/
theorem deriv_semicircle {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv Work.OddEnvelope.semicircle t = -t / Work.OddEnvelope.semicircle t := by
  -- `1 - t² > 0` on the open interval
  have hpos : 0 < (1 - t) * (1 + t) := mul_pos (by linarith [ht.2]) (by linarith [ht.1])
  have hsq : t ^ 2 < 1 := by nlinarith [hpos]
  -- derivative of the inner function `t ↦ 1 - t²`
  have hderiv : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * t) t := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    simpa using h2.const_sub 1
  have hne : (1 - t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  -- chain rule for `Real.sqrt`
  have hsqrt := hderiv.sqrt hne
  have hsd : Work.OddEnvelope.semicircle = fun y : ℝ => Real.sqrt (1 - y ^ 2) := rfl
  rw [hsd, hsqrt.deriv]
  -- `(-2t)/(2√(1-t²)) = -t/√(1-t²)`
  field_simp

end Work.OddEnvelope.Semicircle
