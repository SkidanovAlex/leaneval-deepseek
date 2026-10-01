import Mathlib
import Submission.Work.LinnikAreas.CIDeps

namespace Work.LinnikAreas

open DirichletCharacter Complex

/-- The zero-multiplicity weighted sum `Σ_u ord_u(Λ(χ,·)) · ‖Φ u‖` is summable, for `χ` a
non-principal primitive character mod `N` and `Φ` decaying like `A/‖u‖²` in the critical strip.

This is a direct consequence of `divisorSum_summable_and_tendsto` (the absolute summability of
the divisor-weighted zero sum of `Λ(χ,·)`): writing `Λ = completedLFunction χ`, which is entire,
the divisor of `Λ` on `Set.univ` is the analytic vanishing order, so it suffices to replace the
complex coefficient `(divisor Λ univ u : ℂ)` by its norm. -/
theorem summable_zeroMult_norm_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {Φ : ℂ → ℂ} {A : ℝ} (hA : 0 < A)
    (hΦ : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → ‖Φ u‖ ≤ A / ‖u‖ ^ 2) :
    Summable (fun u : ℂ => (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) * ‖Φ u‖) := by
  obtain ⟨hsum, -⟩ :=
    Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto χ hχ hχprim hA hΦ
  -- `Λ` is entire, so its `Set.univ` divisor is the analytic vanishing order everywhere.
  have hdiv : ∀ u : ℂ, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u
      = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) := by
    intro u
    have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
      DirichletCharacter.differentiable_completedLFunction hχ
    exact Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (fun z _ => hdiff.analyticAt z) (Set.mem_univ u)
  -- replace the integer divisor coefficient by the natural vanishing order
  have hfun : (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u : ℤ)) : ℂ) * Φ u)
      = (fun u : ℂ =>
        (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ)) : ℂ) * Φ u) := by
    funext u
    rw [hdiv u]
    simp
  rw [hfun] at hsum
  -- take norms: `‖(n : ℂ) * Φ u‖ = (n : ℝ) * ‖Φ u‖`
  have hnorm := hsum.norm
  have hnorm' : (fun u : ℂ =>
        ‖(((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ)) : ℂ) * Φ u‖)
      = (fun u : ℂ =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) * ‖Φ u‖) := by
    funext u
    rw [norm_mul, Complex.norm_natCast]
  rw [hnorm'] at hnorm
  exact hnorm

end Work.LinnikAreas
