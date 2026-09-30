/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The open subscheme on which a rational function is regular

For a curve `C` over a field `K` and a rational function `x : K(C)`, the *poles* of `x` are
the places `Q` with `ord_Q x < 0`; by `Curve.finite_support_ordAt` there are only finitely
many of them, so they form a closed subset of `C` and their complement

`regularOpens C x`

is an open subscheme of `C`.  It is the largest open subscheme on which `x` is a regular
function, and the basic object of study of this file.

The main results of the *affine chart* analysis of `Work.SpecLin.Core.linEquiv_of_sections`
are recorded as separate lemmas (see `Work.SpecLin.Chart.isAffineOpen_regularOpens` and
`Work.SpecLin.Chart.exists_transcendental_regular`).
-/
import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.exists_separating_element

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SpecLin.Chart

open Work.CurveBasics

variable {K : Type u} [Field K]

/-- The set of poles of a rational function on a curve, as a subset of the underlying
topological space: the points of the places at which the order of vanishing is negative. -/
def poleSet (C : Curve K) (x : C.functionField) : Set C.left :=
  ⋃ Q ∈ {Q : C.Place | C.ordAt x Q < 0}, ({Q.point} : Set C.left)

/-- The poles of a rational function form a closed subset. -/
theorem isClosed_poleSet (C : Curve K) (x : C.functionField) : IsClosed (poleSet C x) := by
  have h : {Q : C.Place | C.ordAt x Q < 0}.Finite :=
    (C.finite_support_ordAt x).subset fun Q hQ => ne_of_lt hQ
  refine h.isClosed_biUnion ?_
  intro Q _
  exact Q.isClosed

variable (C : Curve K) (x : C.functionField)

/-- The largest open subscheme of a curve on which a rational function is regular: the
complement of its poles. -/
noncomputable def regularOpens : C.left.Opens :=
  ⟨(poleSet C x)ᶜ, (isClosed_poleSet C x).isOpen_compl⟩

/-- Membership in `regularOpens C x`: a point on which `x` has no pole. -/
theorem mem_regularOpens {z : C.left} :
    z ∈ regularOpens C x ↔ ∀ Q : C.Place, Q.point = z → 0 ≤ C.ordAt x Q := by
  constructor
  · intro hz Q hQ
    by_contra hneg
    have hmem : z ∈ poleSet C x := by
      refine Set.mem_iUnion₂.mpr ⟨Q, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]; omega
      · simpa [hQ]
    exact hz hmem
  · intro hz hmem
    rw [poleSet, Set.mem_iUnion₂] at hmem
    obtain ⟨Q, hQ, hQz⟩ := hmem
    simp only [Set.mem_ofPred_eq] at hQ
    exact absurd (hz Q (by simpa using hQz.symm)) (not_le.mpr hQ)

/-- `x` is regular on `regularOpens C x`. -/
theorem regularOn_regularOpens : C.RegularOn (regularOpens C x) x := by
  intro Q hQ
  have h := (mem_regularOpens C x).mp hQ
  exact h Q rfl

/-- Every point at which `x` is regular lies in `regularOpens C x`. -/
theorem mem_regularOpens_of {z : C.left} (hz : ∀ Q : C.Place, Q.point = z → 0 ≤ C.ordAt x Q) :
    z ∈ regularOpens C x :=
  (mem_regularOpens C x).mpr hz

/-- The points of `regularOpens C x` which are places are exactly the places where `x` is
regular. -/
theorem place_mem_regularOpens_iff (Q : C.Place) :
    Q.point ∈ regularOpens C x ↔ 0 ≤ C.ordAt x Q :=
  ⟨fun h => regularOn_regularOpens C x Q h,
   fun h => mem_regularOpens_of C x fun Q' hQ' => by
     have hQ'eq : Q' = Q := Subtype.ext hQ'
     subst hQ'eq
     exact h⟩

end Work.SpecLin.Chart
