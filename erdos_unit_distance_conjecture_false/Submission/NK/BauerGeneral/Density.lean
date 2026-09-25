import Mathlib
import Submission.NK.BauerGeneral.Basic
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum
import Submission.Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_finite
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl

/-!
# Monotonicity of the Dirichlet density

The Dirichlet density of a set of primes is monotone with respect to inclusion: if `A ⊆ B` and both
have a Dirichlet density, then `δ(A) ≤ δ(B)`.  This is immediate from the definition, because the
partial sums `∑_{𝔭 ∈ A} N𝔭^{-s}` are monotone in `A`
(`NumberField.Set.primeIdealZetaSum_mono`).

Consequences recorded here:

* `NK.BauerGeneral.hasDirichletDensity_of_sdiff_finite` — if `A` and `B` differ by a finite set
  (more precisely `A \ B` is finite), then `A` and `B` have the same Dirichlet density whenever
  either of these densities exists.  This is the tool that lets one replace the set of *completely
  split* primes by the corresponding set defined by a Frobenius condition, which can differ on the
  finite set of ramified primes.

The analytic content (summability of the prime-ideal zeta sum, divergence of its unrestricted form,
and the density `1/[L : K]` of the completely split primes of a finite Galois extension) is proved
in `Submission/Commons/NumberTheory/NumberField/Set/`.  Nothing here uses Čebotarev.
-/

set_option linter.unusedVariables false

namespace NK.BauerGeneral

open Filter IsDedekindDomain Topology Set

variable {K : Type*} [Field K] [NumberField K]

/-- **Monotonicity of the Dirichlet density.**  If `A ⊆ B` are sets of primes of a number field and
both have a Dirichlet density, then `δ(A) ≤ δ(B)`. -/
theorem hasDirichletDensity_mono {A B : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    {α β : ℝ} (hAB : A ⊆ B) (hA : NumberField.Set.HasDirichletDensity A α)
    (hB : NumberField.Set.HasDirichletDensity B β) : α ≤ β := by
  unfold NumberField.Set.HasDirichletDensity at hA hB
  refine le_of_tendsto_of_tendsto hA hB ?_
  filter_upwards [self_mem_nhdsWithin,
    (Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT K).eventually
      (eventually_gt_atTop (0 : ℝ))] with s hs hpos
  have hs1 : 1 < s := Set.mem_Ioi.mp hs
  exact div_le_div_of_nonneg_right
    (Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_mono hAB hs1) (le_of_lt hpos)

/-- The completely split primes of a finite Galois extension have Dirichlet density
`1 / [L : K]`, in the set form `NK.BauerGeneral.splitPrimes` used in this chapter. -/
theorem hasDirichletDensity_splitPrimes {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    NumberField.Set.HasDirichletDensity (splitPrimes K L) (1 / (Module.finrank K L : ℝ)) :=
  Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely (K := K) (L := L)

end NK.BauerGeneral
