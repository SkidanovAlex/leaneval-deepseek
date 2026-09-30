import Mathlib
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

open Work.CurveBasics in
/-- The ideal `(x)` of `k[x]` is maximal: `k[x] ≅ k[X]` and the evaluation of a polynomial at the
constant term is a surjection onto the field `k`. -/
theorem kxIdeal_isMaximal {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x) : (Curve.kxIdeal C x).IsMaximal := by
  rw [Curve.kxIdeal, Curve.kx_span_gen_eq_ker C x hx]
  refine RingHom.ker_isMaximal_of_surjective _ ?_
  intro y
  refine ⟨algebraMap k ↥(Algebra.adjoin k ({x} : Set C.functionField)) y, ?_⟩
  change (C.kxEvalZero x hx) (algebraMap k _ y) = y
  rw [AlgHom.commutes]
  simp

open Work.CurveBasics in
/-- The class of the generator `x` of `k[x]` lies in the prime of `k[x]^int` attached to a place
at which `x` vanishes. -/
theorem kxGen_mem_kxPrimeOfPlace {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x) (Q : C.Place) (hQ : 0 < C.ordAt x Q) :
    algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) (C.kxClosure x)
      (Curve.kxGen C x) ∈ kxPrimeOfPlace C x Q hQ.le := by
  show Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ.le)
      (algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) (C.kxClosure x)
        (C.kxGen x)) ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring)
  -- the element of the valuation ring corresponding to the generator `x`
  set a := Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ.le)
    (algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) (C.kxClosure x)
      (C.kxGen x)) with ha
  have hcoe : (a : C.functionField) = x := by
    rw [ha, Subring.coe_inclusion, Subalgebra.coe_algebraMap]
    rfl
  have hx0 : (a : C.functionField) ≠ 0 := by
    rw [hcoe]
    exact fun h => hx (h ▸ isAlgebraic_zero)
  rw [mem_maximalIdeal_iff_ord_pos C Q a hx0, hcoe]
  exact hQ

open Work.CurveBasics in
/-- The prime of `k[x]^int` attached to a place where `x` vanishes lies over the prime `(x)` of
`k[x]`. -/
theorem kxPrimeOfPlace_liesOver {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x) (Q : C.Place) (hQ : 0 < C.ordAt x Q) :
    (kxPrimeOfPlace C x Q hQ.le).LiesOver (Curve.kxIdeal C x) := by
  classical
  -- The contraction of the prime of `k[x]^int` is a prime ideal, hence proper.
  have hne : Ideal.under ↥(Algebra.adjoin k ({x} : Set C.functionField))
      (kxPrimeOfPlace C x Q hQ.le) ≠ ⊤ :=
    (Ideal.IsPrime.comap (f := algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField))
      (C.kxClosure x)) (K := kxPrimeOfPlace C x Q hQ.le)
      (hK := kxPrimeOfPlace_isPrime C x Q hQ.le)).ne_top
  -- `(x)` is contained in the contraction because `x` vanishes at `Q`.
  have hle : Curve.kxIdeal C x ≤ Ideal.under (↥(Algebra.adjoin k ({x} : Set C.functionField)))
      (kxPrimeOfPlace C x Q hQ.le) := by
    rw [Curve.kxIdeal, Ideal.span_le, Set.singleton_subset_iff]
    exact kxGen_mem_kxPrimeOfPlace C x hx Q hQ
  -- a maximal ideal below a proper ideal is equal to it
  exact ⟨(kxIdeal_isMaximal C x hx).eq_of_le hne hle⟩

end Work.CurveBasics.Order
