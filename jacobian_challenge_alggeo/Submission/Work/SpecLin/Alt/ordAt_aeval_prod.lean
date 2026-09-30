import Mathlib
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Alt

-- Auxiliary lemmas for `Work.SpecLin.Alt.ordAt_aeval_prod`, kept in a nested namespace so
-- that they cannot clash with names contributed by neighbouring files.
namespace ordAtAevalProd

section Curve

variable {K : Type*} [Field K]

/-- The order of vanishing at a place of the constant function `1` is zero. -/
lemma ordAt_one (C : Work.CurveBasics.Curve K) (Q : C.Place) :
    C.ordAt (1 : C.functionField) Q = 0 := by
  show AlgebraicGeometry.Scheme.ord (1 : C.left.functionField) Q.point = 0
  by_cases hx : Order.coheight Q.point = 1
  · rw [AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one hx, map_one]
    simp
  · simp [AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- The order of vanishing at a place is additive on products of nonzero functions. -/
lemma ordAt_mul (C : Work.CurveBasics.Curve K) {a b : C.functionField}
    (ha : a ≠ 0) (hb : b ≠ 0) (Q : C.Place) :
    C.ordAt (a * b) Q = C.ordAt a Q + C.ordAt b Q :=
  AlgebraicGeometry.Scheme.ord_mul ha hb

/-- The order of vanishing at a place of a finite product of nonzero functions is the sum of
the orders of vanishing of the factors. -/
lemma ordAt_finset_prod (C : Work.CurveBasics.Curve K) {ι : Type*}
    (s : Finset ι) (g : ι → C.functionField) (hg : ∀ i ∈ s, g i ≠ 0) (Q : C.Place) :
    C.ordAt (∏ i ∈ s, g i) Q = ∑ i ∈ s, C.ordAt (g i) Q := by
  classical
  induction s using Finset.induction with
  | empty => simp [ordAt_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [ordAt_mul C (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hg i (Finset.mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

/-- The value at a transcendental element of a nonzero polynomial is nonzero. -/
lemma aeval_ne_zero {A : Type*} [CommRing A] [Algebra K A]
    (t : A) (ht : Transcendental K t) {p : Polynomial K} (hp : p ≠ 0) :
    Polynomial.aeval t p ≠ 0 :=
  fun h => hp ((transcendental_iff.mp ht) p h)

end Curve

end ordAtAevalProd

/-- The order of vanishing at a place of the value at a transcendental element `t` of a product
of nonzero polynomials is the sum of the orders of vanishing of the individual values. -/
theorem ordAt_aeval_prod {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (t : C.functionField) (ht : Transcendental K t) (s : Finset C.Place)
    (f : C.Place → Polynomial K) (hf : ∀ Q ∈ s, f Q ≠ 0) (Q : C.Place) :
    C.ordAt (Polynomial.aeval t (∏ Q' ∈ s, f Q')) Q
      = ∑ Q' ∈ s, C.ordAt (Polynomial.aeval t (f Q')) Q := by
  classical
  rw [map_prod (Polynomial.aeval t) f s]
  exact ordAtAevalProd.ordAt_finset_prod C s (fun Q' => Polynomial.aeval t (f Q'))
    (fun Q' hQ' h => hf Q' hQ' ((transcendental_iff.mp ht) (f Q') h)) Q

end Work.SpecLin.Alt
