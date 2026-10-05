import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- The derivative of a Laurent polynomial at a nonzero point: differentiate term by term,
each monomial `w ↦ w ^ n` (`n : ℤ`) being differentiable with derivative `n * w ^ (n - 1)`
away from the origin. -/
theorem hasDerivAt_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (laurentPoly N a)
      (∑ n ∈ Finset.Icc (-(N : ℤ)) N, a n * (n : ℂ) * w ^ (n - 1)) w := by
  unfold laurentPoly
  convert (HasDerivAt.sum (𝕜 := ℂ) (F := ℂ) (x := w) (u := Finset.Icc (-(N : ℤ)) N)
      (A := fun n y => a n * y ^ n)
      (A' := fun n => a n * (n : ℂ) * w ^ (n - 1)) ?_) using 1
  · ext y; simp only [Finset.sum_apply]
  · intro n _
    simpa only [mul_assoc] using (hasDerivAt_zpow n w (Or.inl hw)).const_mul (a n)

theorem laurentPoly_differentiableOn (N : ℕ) (a : ℤ → ℂ) :
    DifferentiableOn ℂ (laurentPoly N a) {0}ᶜ := by
  intro w hw
  simp only [mem_compl_iff, mem_singleton_iff] at hw
  exact (hasDerivAt_laurentPoly N a hw).differentiableAt.differentiableWithinAt

end Work.RPB1a
