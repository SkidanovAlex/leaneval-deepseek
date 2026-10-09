/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Submission.NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trivial Frobenius is the splitting-completely condition

For a finite Galois extension `L/K` of number fields and an unramified prime `P` of `𝓞 L` over `p`,
the Frobenius at `P` is trivial exactly when `p` has a single prime above it of inertia degree one,
i.e. exactly when the inertia degree of `P` is `1`.  This is the bridge between the Frobenius
vocabulary of this chapter and the "primes splitting completely" density statement of the commons
(`Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`).
-/

set_option linter.unusedSectionVars false

namespace NK.Chebotarev

open IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The Frobenius at an unramified prime is trivial iff the inertia degree is one.** -/
theorem IsFrobAt_eq_one_iff_inertiaDeg_eq_one {p : PrimeIdeal K} {P : PrimeIdeal L}
    (hP : P.asIdeal.LiesOver p.asIdeal)
    (hunr : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    IsFrobAt P (1 : Gal(L/K)) ↔ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
  constructor
  · intro h
    simpa using (IsFrobAtOrderOfEqInertiaDeg (K := K) (L := L) (p := p) (P := P) hP hunr
      h).symm
  · intro h
    obtain ⟨σ, hσ⟩ := exists_isFrobAt (K := K) (L := L) p P hP
    have hσ1 : σ = 1 := by
      have hord := IsFrobAtOrderOfEqInertiaDeg (K := K) (L := L) (p := p) (P := P) hP hunr hσ
      rw [h] at hord
      exact orderOf_eq_one_iff.mp hord
    rwa [hσ1] at hσ

end NK.Chebotarev
