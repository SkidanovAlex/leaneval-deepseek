import Mathlib
import Submission.Work.Tower.Defs

/-!
# The set of primes splitting completely in an intermediate field

`Work.CFTLib.splitsCompletelySet L` is the set of primes `v` of `𝓞 K` which split completely in
the finite extension `↥L / K`, phrased with the explicit-family predicate
`Work.Tower.SplitsCompletelyIn K ↥L v.asIdeal` (all primes of `𝓞 ↥L` above `v` are unramified
with residue field `(𝓞 K) ⧸ v`, and there are `[L : K]` of them).

Its Dirichlet density is `1 / [L : K]` for `L/K` Galois
(`Work.CFTLib.hasDirichletDensity_splitsCompletelySet`), the completely split primes differing
from the inertia-degree-one primes only in the finite set of primes ramifying in `L`.
-/

open NumberField

namespace Work.CFTLib

/-- The set of primes of `𝓞 K` that split completely in the intermediate field `L` of the
common extension `A` of `K`. -/
def splitsCompletelySet {K A : Type*} [Field K] [Field A] [Algebra K A]
    (L : IntermediateField K A) : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  {v | Work.Tower.SplitsCompletelyIn K ↥L v.asIdeal}

@[simp]
theorem mem_splitsCompletelySet {K A : Type*} [Field K] [Field A] [Algebra K A]
    (L : IntermediateField K A) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    v ∈ splitsCompletelySet L ↔ Work.Tower.SplitsCompletelyIn K ↥L v.asIdeal := Iff.rfl

end Work.CFTLib
