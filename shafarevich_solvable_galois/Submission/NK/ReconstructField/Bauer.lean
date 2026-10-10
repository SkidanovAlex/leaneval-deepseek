import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.Reconstruct.eq_of_splitPrimes_eq
import Submission.NK.ReconstructField.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bauer's theorem in the vocabulary of this chapter

The completely split primes determine a finite Galois subextension: if `E`, `E'` are finite normal
number-field subextensions of a Galois extension `Ω/K` with `SplitsCompletely` sets equal, then
`E = E'`.  This is `NK.Reconstruct.eq_of_splitPrimes_eq` (whose proof is the Dirichlet-density
argument of Bauer, using the unconditional density `1/[L : K]` of the completely split primes of a
finite Galois extension `L/K`, `Commons…hasDirichletDensity_primes_splitsCompletely`, together with
multiplicativity of `e` and `f` in towers), restated for the predicate
`NK.ReconstructField.SplitsCompletely` used throughout this chapter.

This is the analytic engine of the reconstruction: it is what upgrades the correspondence of the
*completely split primes* at corresponding levels
(`NK.ReconstructField.splitsCompletely_levelMap_iff`) into an equality of the levels.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open IsDedekindDomain

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

/-- **Bauer's theorem**: two finite normal number-field subextensions of a common Galois extension
with the same completely split primes are equal. -/
theorem eq_of_splitsCompletely_iff [IsGalois K Ω]
    (E E' : IntermediateField K Ω) [FiniteDimensional K E] [Normal K E] [NumberField ↥E]
    [FiniteDimensional K E'] [Normal K E'] [NumberField ↥E']
    (h : ∀ p : NK.Chebotarev.PrimeIdeal K,
      SplitsCompletely K ↥E p ↔ SplitsCompletely K ↥E' p) :
    E = E' := by
  haveI hgalE : IsGalois K ↥E :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hgalE' : IsGalois K ↥E' :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  refine NK.Reconstruct.eq_of_splitPrimes_eq (K := K) (K' := Ω) (L := E) (M := E')
    (fun p => ?_)
  exact (NK.Reconstruct.splitsCompletely_iff_ncard K ↥E p).trans
    ((h p).trans (NK.Reconstruct.splitsCompletely_iff_ncard K ↥E' p).symm)

end NK.ReconstructField
