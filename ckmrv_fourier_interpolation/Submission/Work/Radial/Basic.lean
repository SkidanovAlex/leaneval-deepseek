import Mathlib
import Submission.Work.Core.Basic

/-!
# Vocabulary for the Gaussian density lemma

This file collects the definitions shared between the main file
`Submission/Work/Radial/gaussians_dense.lean` and the auxiliary lemmas proved
for it.

The mathematical content of the target statement is the density, in the space of
radial Schwartz functions on `R^n`, of the set of complex Gaussians
`x ↦ exp (π i τ ‖x‖²)` with fixed imaginary part `Im τ = y > 0`.
-/

open LeanEval.Analysis.CKMRVInterpolation
open scoped SchwartzMap

namespace Work.Radial

/-- The first coordinate vector of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def axis (n : ℕ) [NeZero n] : EuclideanSpace ℝ (Fin n) := realIncl (n := n) 1

/-- The profile of a function on `EuclideanSpace ℝ (Fin n)`, viewed as a function of
`‖x‖²` (for `t < 0` the value is the value at the origin, since `Real.sqrt t = 0`). -/
noncomputable def profile {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (t : ℝ) : ℂ := f (Real.sqrt t • axis n)

/-- The Gaussian weight `x ↦ exp (-π y ‖x‖²)` as a function, for `y : ℝ`. -/
noncomputable def gaussianWeight {n : ℕ} [NeZero n] (y : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ := Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ)))

/-- The function `x ↦ exp (-π y ‖x‖²) h (‖x‖²)` for `h : ℝ → ℂ`. -/
noncomputable def gaussianTimesProfile {n : ℕ} [NeZero n] (y : ℝ) (h : ℝ → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ := gaussianWeight y x * h (‖x‖ ^ 2)

end Work.Radial
