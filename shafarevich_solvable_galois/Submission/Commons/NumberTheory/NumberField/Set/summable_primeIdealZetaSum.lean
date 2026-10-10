import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Set

/-- For every real `s > 1`, the Dirichlet series `∑' 𝔭, (N 𝔭) ^ (-s)` over the nonzero prime
ideals of `𝓞 K` is summable.

This is the summability of the "prime-ideal zeta sum" of a number field.  The statement is already
available in the shared commons as `summable_primeIdealNorm` (proved there by grouping the prime
ideals by their absolute norm and invoking the `O(N)` bound on the ideal-counting function
`N ↦ #{I | absNorm I ≤ N}` together with the `L`-series convergence criterion); we reuse it here
under the name requested for this project. -/
theorem summable_primeIdealZetaSum {K : Type*} [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
  summable_primeIdealNorm K hs

end Commons.NumberTheory.NumberField.Set
