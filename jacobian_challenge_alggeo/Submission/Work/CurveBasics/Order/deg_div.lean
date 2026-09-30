import Mathlib
import Submission.Work.CurveBasics.Order
import Submission.Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic
import Submission.Work.CurveBasics.Order.deg_div_split
import Submission.Work.CurveBasics.Order.sum_ord_neg_eq_finrank
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Order

open Work.CurveBasics

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

noncomputable section

variable {k : Type*} [Field k]

/-- The degree of a principal divisor is the sum, over the support of `ordAt h`, of the order of
vanishing of `h` weighted by the residue degree. -/
lemma deg_div_eq_sum (C : Curve k) (h : C.functionField) :
    C.deg (C.div h) = ∑ Q ∈ (C.finite_support_ordAt h).toFinset,
      C.ordAt h Q * (C.hom.residueDegree Q.point : ℤ) := by
  show (C.div h).sum (fun Q n => n * (C.hom.residueDegree Q.point : ℤ)) = _
  have hsupp : (C.div h).support = (C.finite_support_ordAt h).toFinset := by
    ext Q
    rw [Finsupp.mem_support_iff, Curve.div_apply, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  rw [Finsupp.sum, hsupp]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [Curve.div_apply]

/-- Membership in the set of zeros of `h` used below. -/
lemma mem_filter_ord_pos_iff (C : Curve k) (h : C.functionField) (Q : C.Place) :
    Q ∈ (C.finite_support_ordAt h).toFinset.filter (fun Q => 0 < C.ordAt h Q) ↔
      0 < C.ordAt h Q := by
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun x => x.2, fun hq => ⟨ne_of_gt hq, hq⟩⟩

open Work.CurveBasics in
theorem deg_div {k : Type*} [Field k] (C : Curve k) (h : C.functionField) :
    C.deg (C.div h) = 0 := by
  rcases eq_or_ne h 0 with rfl | h0
  · rw [Curve.div_zero, Curve.deg_zero]
  by_cases halg : IsAlgebraic k h
  · obtain ⟨c, rfl⟩ := Basic.eq_algebraMap_of_isAlgebraic C halg
    rw [div_algebraMap_eq_zero, Curve.deg_zero]
  · have htr : Transcendental k h := halg
    haveI : FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField))
        C.functionField := finiteDimensional_adjoin_functionField C htr
    rw [deg_div_split C h h0, sum_ord_pos_eq_finrank_general' C h htr,
      sum_ord_neg_eq_finrank C h htr, sub_self]

end

end Work.CurveBasics.Order
