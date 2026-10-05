import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.signedArea_circle_scaled

namespace Work.RPB.B5

/-- The signed area of the `τ = 0` target circle `ktarg δ k σ` of radius `√(2+2σ)`.

`ktarg δ k σ` is, by definition, the phase-shifted circle
`t ↦ (√(2+2σ) : ℂ) * exp ((t + kphc δ k σ) · I)`, so `signedArea_circle_scaled` gives the value
`(√(2+2σ)) ^ 2 * π`, and `Real.sq_sqrt` turns the square of the square root into `2 + 2σ`
under the hypothesis `0 ≤ 2 + 2σ`.  The phase shift `kphc δ k σ` is irrelevant to the value: it
only rotates the curve. -/
theorem ktarg_signedArea (δ : ℝ) (k : ℤ) (σ : ℝ) (hσ : 0 ≤ 2 + 2 * σ) :
    Work.RPB.signedArea (fun t => Work.RPB.B5.ktarg δ k σ t)
      = (2 + 2 * σ) * Real.pi := by
  have hfun : (fun t => Work.RPB.B5.ktarg δ k σ t)
      = (fun t : ℝ => (Work.RPB.B5.krd σ : ℂ) *
          Complex.exp ((t + Work.RPB.B5.kphc δ k σ) * Complex.I)) := rfl
  rw [hfun, signedArea_circle_scaled, krd, Real.sq_sqrt hσ]

end Work.RPB.B5
