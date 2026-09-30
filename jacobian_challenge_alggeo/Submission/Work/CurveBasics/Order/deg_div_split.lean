import Mathlib
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Classical

namespace Work.CurveBasics.Order

open Work.CurveBasics

/-- Splitting a sum of products over a finite set according to the sign of the first factor.

For any finite set `S` and functions `o r : α → ℤ`,
`∑_{Q ∈ S} o Q * r Q` equals the sum of `o Q * r Q` over the points with `o Q > 0`
minus the sum of `(-o Q) * r Q` over the points with `o Q < 0`.  (The points with
`o Q = 0` contribute nothing.)  No hypothesis on `r` is needed. -/
lemma sum_split_sign {α : Type*} [DecidableEq α] (S : Finset α) (o r : α → ℤ) :
    ∑ Q ∈ S, o Q * r Q
      = (∑ Q ∈ S.filter (fun Q => 0 < o Q), o Q * r Q)
      - (∑ Q ∈ S.filter (fun Q => o Q < 0), (-o Q) * r Q) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h1 h2
  · exfalso; omega
  · ring
  · ring
  · have ho : o x = 0 := by omega
    rw [ho]; ring

/-- The degree of a principal divisor is the sum, over the support of `ordAt h`, of the order
of vanishing of `h` weighted by the residue degree.  (Local copy of `deg_div_eq_sum`, kept here
to avoid the heavier imports of the module it lives in.) -/
lemma deg_div_eq_sum' {k : Type*} [Field k] (C : Curve k) (h : C.functionField) :
    C.deg (C.div h) = ∑ Q ∈ (C.finite_support_ordAt h).toFinset,
      C.ordAt h Q * (C.hom.residueDegree Q.point : ℤ) := by
  show (C.div h).sum (fun Q n => n * (C.hom.residueDegree Q.point : ℤ)) = _
  have hsupp : (C.div h).support = (C.finite_support_ordAt h).toFinset := by
    ext Q
    rw [Finsupp.mem_support_iff, Curve.div_apply, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  rw [Finsupp.sum, hsupp]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [Curve.div_apply]

open Work.CurveBasics in
theorem deg_div_split {k : Type*} [Field k] (C : Curve k) (h : C.functionField) (hh : h ≠ 0) :
    C.deg (C.div h) =
      (∑ Q ∈ (C.finite_support_ordAt h).toFinset.filter (fun Q => 0 < C.ordAt h Q),
          C.ordAt h Q * (C.hom.residueDegree Q.point : ℤ))
      - (∑ Q ∈ (C.finite_support_ordAt h).toFinset.filter (fun Q => C.ordAt h Q < 0),
          (-C.ordAt h Q) * (C.hom.residueDegree Q.point : ℤ)) := by
  rw [deg_div_eq_sum']
  exact sum_split_sign _ (fun Q => C.ordAt h Q)
    (fun Q => (C.hom.residueDegree Q.point : ℤ))

end Work.CurveBasics.Order
