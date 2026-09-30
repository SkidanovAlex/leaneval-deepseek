/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: the exported interface

The lemmas of this area are proved in the sub-namespaces `Work.RiemannRoch.Duality`,
`Work.RiemannRoch.Canonical`, `Work.RiemannRoch.RR6` and `Work.RiemannRoch.RR8` (one file per
lemma, as they are delegated to individual agents).  This file re-exports the ones the rest of
the Jacobian development uses under the stable names of the blueprint
(`Submission/Work/NOTES_LEAD_jacobian_RR.md`, §"EXPORT for GC"), in the namespace
`Work.RiemannRoch.Curve`:

* `isCanonical_iff`;
* `exists_nonspecial`;
* `finite_setOf_i_add_place_eq`, `i_add_place_of_degree_one` (RR6);
* `deg_divMap`, `genus_eq`, `i_divMap`, `isCanonical_divMap` (RR8, base change).

Everything is stated for an arbitrary field, and nothing here uses the separability or
perfectness of `k`.
-/
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Canonical.Properties
import Submission.Work.RiemannRoch.Canonical.isCanonical_iff
import Submission.Work.RiemannRoch.RR6.finite_setOf_i_add_place_eq
import Submission.Work.RiemannRoch.RR6.i_add_place_of_degree_one
import Submission.Work.RiemannRoch.RR6.exists_nonspecial
import Submission.Work.RiemannRoch.RR8.deg_divMap
import Submission.Work.RiemannRoch.RR8.genus_eq
import Submission.Work.RiemannRoch.RR8.i_divMap
import Submission.Work.RiemannRoch.RR8.IsCanonicalDivMap
import Submission.Work.RiemannRoch.RR6.i_add_generic
import Submission.Work.RiemannRoch.Curve.GenericPlace

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- **Numerical criterion for canonical divisors**: a divisor of degree `2g - 2` whose space of
sections has dimension `g` is canonical.  This is the form in which canonicality is transported
along base change. -/
theorem isCanonical_iff (C : Curve k) (W : C.Div) :
    IsCanonical C W ↔ C.deg W = 2 * (genus C : ℤ) - 2 ∧ C.l W = genus C :=
  Canonical.isCanonical_iff C W

/-- **RR6, nonspecial divisor**: if there are infinitely many places of degree one, there is an
effective divisor of degree `g` with `i D = 0` and `l D = 1`. -/
theorem exists_nonspecial (C : Curve k) (h : {P : C.Place | P.degree = 1}.Infinite) :
    ∃ D : C.Div, D.IsEffective ∧ C.deg D = (genus C : ℤ) ∧ i C D = 0 ∧ C.l D = 1 :=
  RR6.exists_nonspecial C h

/-- **RR6**: the places at which the index of speciality does not drop when `[P]` is added to a
special divisor `D` form a finite set. -/
theorem finite_setOf_i_add_place_eq (C : Curve k) {D : C.Div} (hD : i C D ≠ 0) :
    {P : C.Place | i C (D + Curve.Div.place P) = i C D}.Finite :=
  RR6.finite_setOf_i_add_place_eq C hD

/-- **RR6**: away from the base locus, adding a place of degree one drops `i` by exactly one. -/
theorem i_add_place_of_degree_one (C : Curve k) {D : C.Div} {P : C.Place}
    (hP : P.degree = 1) (h : i C (D + Curve.Div.place P) ≠ i C D) :
    i C (D + Curve.Div.place P) + 1 = i C D :=
  RR6.i_add_place_of_degree_one C hP h

variable {C : Curve k}
variable {F : Type u} [Field F] [Algebra k F] {C' : Curve F}

/-- **RR8**: the degree of a divisor is preserved by base change (with the CB6 input `hl`
taken as an explicit hypothesis; see `ExportCB.deg_divMap` for the unconditional form). -/
theorem deg_divMap_of (S : Work.CurveBasics.Curve.BCSquare C C')
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D) (D : C.Div) :
    C'.deg (S.divMap D) = C.deg D :=
  RR8.deg_divMap S hl D

/-- **RR8**: the genus is invariant under base change (conditional on CB6's `l_divMap`). -/
theorem genus_eq_of (S : Work.CurveBasics.Curve.BCSquare C C')
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D) : genus C' = genus C :=
  RR8.genus_eq S hl

/-- **RR8**: the index of speciality is invariant under base change (conditional on CB6's
`l_divMap`). -/
theorem i_divMap_of (S : Work.CurveBasics.Curve.BCSquare C C')
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D) (D : C.Div) :
    i C' (S.divMap D) = i C D :=
  RR8.i_divMap S hl D

/-- **RR8**: the pullback of a canonical divisor is canonical (conditional on CB6's
`l_divMap`). -/
theorem isCanonical_divMap_of (S : Work.CurveBasics.Curve.BCSquare C C')
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D) {W : C.Div} (hW : IsCanonical C W) :
    IsCanonical C' (S.divMap W) :=
  RR8.isCanonical_divMap S hl hW

/-- **RR6, generic-place form**: adding the generic place of `C` (over the generic point of
`C`, of degree one, where pulled back functions have order zero) to a divisor of positive index
of speciality drops `i` by exactly one.  This is the general statement; `ExportCB.i_add_generic`
instantiates it at `genericPlace C` and discharges `hl`/`hmem` from CB6. -/
theorem i_add_generic_of (C : Curve k) (A : C.Div) (hA : 0 < i C A)
    (hl : ∀ D : C.Div, (C.baseChange (C.functionField : Type u)).l
      ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).divMap D) = C.l D)
    (hmem : ∀ {D : C.Div} {f : C.functionField}, f ∈ C.L D →
      (Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).fieldMap.hom f
        ∈ (C.baseChange (C.functionField : Type u)).L
            ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).divMap D)) :
    i (C.baseChange (C.functionField : Type u))
        ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).divMap A
          + Curve.Div.place (genericPlace C)) + 1
      = i C A :=
  RR6.i_add_generic C A hA (genericPlace C) (degree_genericPlace C)
    (fun f hf => ordAt_genericPlace C hf) (genericPlace_not_mem_image C) hl hmem

end

end Curve

end Work.RiemannRoch
