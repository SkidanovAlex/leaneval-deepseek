import Mathlib

namespace Work.Radial

/-- Every iterated (real) Fréchet derivative of `Complex.exp` at `y` is bounded by
`Real.exp y.re = ‖Complex.exp y‖`.

The proof reduces the real-scalar iterated derivative to the complex-scalar one via
scalar restriction (`ContDiffAt.restrictScalars_iteratedFDeriv`); the norm of a continuous
multilinear map is unchanged by `restrictScalars`, and for a one-dimensional field the norm of
the `n`-th iterated Fréchet derivative equals the norm of the `n`-th iterated derivative. -/
lemma exp_iteratedFDeriv_bound (k : ℕ) (y : ℂ) : ‖iteratedFDeriv ℝ k Complex.exp y‖ ≤ Real.exp y.re := by
  have hcd : ContDiffAt ℂ (k : WithTop ℕ∞) Complex.exp y := by
    have : ContDiff ℂ (k : WithTop ℕ∞) Complex.exp := by
      simpa using ContDiff.cexp (𝕜 := ℂ) (n := (k : WithTop ℕ∞)) (f := id) contDiff_id
    exact this.contDiffAt
  have hres : (iteratedFDeriv ℂ k Complex.exp y).restrictScalars ℝ = iteratedFDeriv ℝ k Complex.exp y :=
    ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) (𝕜' := ℂ) hcd
  rw [← hres, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp,
    Complex.norm_exp]

end Work.Radial
