import Mathlib
import Submission.Work.DSM2p.RootClosure
import Submission.Work.DSM2p.rootClosure_flat
import Submission.Work.DSM2p.rootClosure_algEquiv_monoidAlgebra

/-!
# `p` is a nonzerodivisor on the `p`-th root closure

The root-system ring `rootClosure A p ι = A[X_{i,n} | i ∈ ι, n ∈ ℕ]/(X_{i,n+1}^p - X_{i,n})` is the
monoid algebra of the monoid of monomials
`⟨x_{i,n} | x_{i,n+1}^p = x_{i,n}⟩ = ((ι × ℕ) →₀ ℕ) / ∼` presented by the root relations
(`rootClosureMonoid`, `rootClosure_flat`):

`rootClosure A p ι ≃ₐ[A] A[rootClosureMonoid p ι]`.

Since the monoid algebra of *any* monoid is a free `A`-module (`MonoidAlgebra.basis`), it is a
direct sum of copies of `A`; scalar multiplication by `p` acts coefficientwise, so a
nonzerodivisor of `A` remains a nonzerodivisor on the root closure.  Nothing else about `A`, `p`
or `ι` is used (in particular `p = 0` is covered: then `A` is subsingleton and so is the root
closure).

## Main result

* `rootClosure_isSMulRegular` — `IsSMulRegular A p → IsSMulRegular (rootClosure A p ι) p`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- An `A`-algebra equivalence transports regularity of a scalar: if the image `e a` acts
regularly on `S`, then `a` acts regularly on `R`. -/
lemma IsSMulRegular.of_algEquiv {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (e : R ≃ₐ[A] S) {a : R} (h : IsSMulRegular S (e a)) :
    IsSMulRegular R a := by
  intro x y hxy
  have hxy' : a * x = a * y := hxy
  refine e.injective (h ?_)
  show (e a) • (e x) = (e a) • (e y)
  rw [smul_eq_mul, smul_eq_mul, ← map_mul, ← map_mul, hxy']

/-- A nonzerodivisor of `A` is a nonzerodivisor on any monoid algebra over `A`: `A[M]` is the free
`A`-module on `M` and the scalar action is coefficientwise, so `(p : A[M]) = single 1 p` acts on
coefficients by multiplication by `p`. -/
private lemma monoidAlgebra_natCast_isSMulRegular (A : Type u) [CommRing A] (M : Type u)
    [Monoid M] (p : ℕ) (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (MonoidAlgebra A M) (p : MonoidAlgebra A M) := by
  intro x y hxy
  have hxy' : (p : MonoidAlgebra A M) * x = (p : MonoidAlgebra A M) * y := hxy
  have hp' : (p : MonoidAlgebra A M) = MonoidAlgebra.single 1 (p : A) := by
    rw [← map_natCast (algebraMap A (MonoidAlgebra A M)) p, MonoidAlgebra.coe_algebraMap]
    rfl
  rw [hp'] at hxy'
  refine MonoidAlgebra.ext (Finsupp.ext fun m => ?_)
  have h := congrArg (fun z : MonoidAlgebra A M => z.coeff m) hxy'
  rw [MonoidAlgebra.coeff_single_one_mul, MonoidAlgebra.coeff_single_one_mul] at h
  exact hp h

theorem rootClosure_isSMulRegular (A : Type u) [CommRing A] (p : ℕ) (ι : Type u)
    (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (rootClosure A p ι) (p : rootClosure A p ι) := by
  obtain ⟨e⟩ := rootClosure_algEquiv_monoidAlgebra A p ι
  refine IsSMulRegular.of_algEquiv e ?_
  simpa using monoidAlgebra_natCast_isSMulRegular A (rootClosureMonoid p ι) p hp

end Work.DSM2p
