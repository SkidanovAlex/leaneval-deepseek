import Mathlib
import Submission.NK.Chebotarev.LFunctions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trivial-character prime sum is the prime-ideal zeta sum

For a finite Galois extension `L/K` of number fields, the character-twisted prime sum
`NK.Chebotarev.charPrimeSum χ s = ∑_𝔭 χ(Frob_𝔭) N𝔭^{-s}` (the Euler product of the Hecke
`L`-function of `χ`) reduces, for the trivial character `χ = 1`, to the full prime-ideal
zeta sum of `K`:

`charPrimeSum (1 : Gal(L/K) →* ℂ) s = ((primeIdealZetaSum univ s : ℝ) : ℂ)`.

This is the `k = 1` term of the Euler product of the Dedekind zeta function `ζ_K`, i.e. the
identity responsible for the fact that `L(1, s) = ζ_K(s)` up to the factors at ramified primes
and the higher-degree Euler factors `k ≥ 2`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Filter IsDedekindDomain
open scoped BigOperators Classical

namespace NK.Chebotarev

/-- **The trivial-character prime sum is the full prime-ideal zeta sum.**  Both sides are the
sum `∑_𝔭 N𝔭^{-s}` over all nonzero prime ideals of `K`: on the left every Frobenius is sent to
`1` by the trivial character, and on the right the sum is taken over `Set.univ`.  The only
content is the identification of a `tsum` over the subtype `↥(univ : Set (PrimeIdeal K))` with
the `tsum` over `PrimeIdeal K` (`tsum_univ`), followed by `Complex.ofReal_tsum`. -/
theorem charPrimeSum_one_eq {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {s : ℝ} (hs : 1 < s) :
    NK.Chebotarev.charPrimeSum (K := K) (L := L) (1 : Gal(L/K) →* ℂ) s =
      ((NumberField.Set.primeIdealZetaSum (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) s : ℝ) : ℂ) := by
  rw [charPrimeSum]
  simp only [MonoidHom.one_apply, one_mul]
  rw [NumberField.Set.primeIdealZetaSum_def]
  rw [tsum_univ (f := fun 𝔭 : NK.Chebotarev.PrimeIdeal K =>
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))]
  rw [Complex.ofReal_tsum]

end NK.Chebotarev
