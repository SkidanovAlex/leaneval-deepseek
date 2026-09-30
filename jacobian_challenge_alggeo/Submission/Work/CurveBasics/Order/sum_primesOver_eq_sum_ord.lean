import Mathlib
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.SumPrimesAux
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.CurveBasics.Order.spso_inertiaDeg_eq
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.Place.degree_eq_finrank
import Submission.Work.CurveBasics.Place.exists_place_of_valuationSubring

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.CurveBasics.Order

open Work.CurveBasics

open Work.CurveBasics in
/-- **The dictionary between the divisor of zeros of a rational function and the primes of the
integral closure of `k[h]` over the prime `(h)`.**

Let `C` be a curve over a field `k`, let `h ∈ K(C)` be transcendental over `k`, and put
`A = k[h]`, `B = k[h]^int ⊆ K(C)`.  Assume `K(C)/k(h)` is finite and `B` is a finite `A`-module
(these are the hypotheses under which the bridge `Q ↦ B ∩ 𝔪_Q` between the places where `h`
vanishes and the primes of `B` over `(h)` is available separability-free, see
`Work.CurveBasics.Order.spso_surj` and `Work.CurveBasics.Order.spso_inj`).

Then the sum, over the primes `q` of `B` above `(h)`, of the ramification index times the inertia
degree, equals the sum over the zeros `Q` of `h` of the order of vanishing times the residue
degree: both compute the degree `[K(C) : k(h)]`, the first by
`Ideal.sum_ramification_inertia_eq_finrank` and the second by the dictionary above. -/
theorem sum_primesOver_eq_sum_ord {k : Type*} [Field k] (C : Curve k) (h : C.functionField)
    (hh : Transcendental k h)
    [FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField]
    [Module.Finite (C.ordBase h) (C.ordClosure h)]
    [Fintype ((C.ordIdeal h).primesOver (C.ordClosure h))] :
    ∑ q : (C.ordIdeal h).primesOver (C.ordClosure h),
        ((q.1.ramificationIdx (C.ordBase h) : ℤ) * (q.1.inertiaDeg (C.ordBase h) : ℤ))
      = ∑ Q ∈ (C.finite_support_ordAt h).toFinset.filter (fun Q => 0 < C.ordAt h Q),
          C.ordAt h Q * (C.hom.residueDegree Q.point : ℤ) := by
  classical
  -- the two Finsets that are reindexed against each other
  set Z : Finset C.Place := (C.finite_support_ordAt h).toFinset.filter (fun Q => 0 < C.ordAt h Q)
    with hZ
  have hmem : ∀ Q ∈ Z, 0 < C.ordAt h Q := by
    intro Q hQ
    rw [hZ] at hQ
    exact (Finset.mem_filter.mp hQ).2
  -- the bridge, as a function on the zeros of `h`
  let i : ∀ Q ∈ Z, (C.ordIdeal h).primesOver (C.ordClosure h) := fun Q hQ =>
    ⟨kxPrimeOfPlace C h Q (hmem Q hQ).le, kxPrimeOfPlace_isPrime C h Q (hmem Q hQ).le,
      kxPrimeOfPlace_liesOver C h hh Q (hmem Q hQ)⟩
  -- the termwise identities `e = ord` and `f = [κ(Q) : k]`
  have hterm : ∀ (Q : C.Place) (hQ : Q ∈ Z),
      ((i Q hQ).1.ramificationIdx (C.ordBase h) : ℤ)
        * ((i Q hQ).1.inertiaDeg (C.ordBase h) : ℤ)
      = C.ordAt h Q * (C.hom.residueDegree Q.point : ℤ) := by
    intro Q hQ
    rw [spso_ramificationIdx_eq C h hh (Q := Q) (hmem Q hQ)]
    rw [spso_inertiaDeg_eq C h hh Q (hmem Q hQ)]
  -- the reindexing
  refine (Finset.sum_bij i (fun Q hQ => Finset.mem_univ _) ?_ ?_ ?_).symm
  · intro Q hQ Q' hQ' heq
    exact spso_inj C h hh (hmem Q hQ) (hmem Q' hQ') (Subtype.ext_iff.mp heq)
  · intro q _
    obtain ⟨Q, hQpos, heq⟩ := spso_surj C h hh q
    refine ⟨Q, ?_, Subtype.ext heq⟩
    rw [hZ, Finset.mem_filter]
    exact ⟨(Set.Finite.mem_toFinset (C.finite_support_ordAt h)).mpr (ne_of_gt hQpos), hQpos⟩
  · intro Q hQ
    exact (hterm Q hQ).symm

end Work.CurveBasics.Order
