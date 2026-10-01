import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_window_cover
import Submission.Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_chi

namespace Commons.NumberTheory.DirichletCharacter

/-- **Uniform zero count of the completed Dirichlet L-function in an arbitrary disk.**

This is the zero-count estimate used downstream by the Linnik project: there is an absolute
constant `c > 0` such that, for every primitive non-trivial Dirichlet character `χ mod N` and
every disk `B(a, ρ)` with `ρ ≥ 1`, the (multiplicity-weighted, signed) divisor sum of
`Λ(s, χ) = completedLFunction χ s` over `B(a, ρ)` is at most
`c · (ρ + 1) · (log(‖a‖ + ρ + 2) + log N + 2)`.

It is the `BombieriVinogradov` uniform zero-count theorem, restated in the
`DirichletCharacter` namespace where the Linnik development consumes it. -/
theorem completedL_ballZeroCount_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
        c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) :=
  Commons.NumberTheory.BombieriVinogradov.ball_zeroCount_uniformL

end Commons.NumberTheory.DirichletCharacter
