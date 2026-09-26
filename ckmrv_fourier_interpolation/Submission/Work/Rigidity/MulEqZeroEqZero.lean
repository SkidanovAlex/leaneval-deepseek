import Mathlib
import Submission.Work.Rigidity.Basic

open scoped Manifold

namespace Work.Rigidity

/-- The upper half plane has no zero divisors for holomorphic functions: if the
product of two functions whose lift to `ℂ` is holomorphic on `{z | 0 < z.im}`
vanishes identically, then one of the two factors vanishes.

This is the standard identity-theorem argument: the hypotheses say exactly that
the two functions are `MDiff` on `ℍ`, whence `UpperHalfPlane.mul_eq_zero_iff`
concludes. -/
theorem MulEqZeroEqZero {F G : UpperHalfPlane → ℂ}
    (hF : DifferentiableOn ℂ (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im})
    (hG : DifferentiableOn ℂ (fun z : ℂ => G (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im})
    (h : ∀ τ : UpperHalfPlane, F τ * G τ = 0) : F = 0 ∨ G = 0 := by
  have hF' : MDiff F := by
    simpa [UpperHalfPlane.mdifferentiable_iff, Function.comp_def] using hF
  have hG' : MDiff G := by
    simpa [UpperHalfPlane.mdifferentiable_iff, Function.comp_def] using hG
  exact (UpperHalfPlane.mul_eq_zero_iff hF' hG').mp (funext h)

end Work.Rigidity
