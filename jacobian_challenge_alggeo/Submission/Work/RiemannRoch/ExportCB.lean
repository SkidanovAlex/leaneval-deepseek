/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: the exported interface, with the CB6 input discharged

The RR8 lemmas of this area take the CB6 statement "`l` is invariant under `divMap`" as an
explicit hypothesis `hl` (this kept area RR independent of the base-change work in flight in
area CB).  CB now provides the two theorems that discharge it
(`Curve.BCSquare.l_divMap` and `Curve.BCSquare.L_divMap`), and this file records the resulting
unconditional statements, under the names of the blueprint's "EXPORT for GC":

* `deg_divMap`, `genus_eq`, `i_divMap`, `isCanonical_divMap` (RR8);
* `i_add_generic` (RR6 at the generic place).

Nothing in this file is used by the rest of area RR; it is the interface consumed by area GC.
-/
import Submission.Work.RiemannRoch.Export
import Submission.Work.CurveBasics.Curve.BCSquare.l_divMap
import Submission.Work.CurveBasics.Curve.BCSquare.L_divMap

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
variable {C : Curve k}
variable {F : Type u} [Field F] [Algebra k F] {C' : Curve F}

/-- **RR8**: the degree of a divisor is preserved by base change. -/
theorem deg_divMap (S : Work.CurveBasics.Curve.BCSquare C C') (D : C.Div) :
    C'.deg (S.divMap D) = C.deg D :=
  RR8.deg_divMap S (fun D => Work.CurveBasics.Curve.BCSquare.l_divMap S D) D

/-- **RR8**: the genus is invariant under base change. -/
theorem genus_eq (S : Work.CurveBasics.Curve.BCSquare C C') : genus C' = genus C :=
  RR8.genus_eq S (fun D => Work.CurveBasics.Curve.BCSquare.l_divMap S D)

/-- **RR8**: the index of speciality is invariant under base change. -/
theorem i_divMap (S : Work.CurveBasics.Curve.BCSquare C C') (D : C.Div) :
    i C' (S.divMap D) = i C D :=
  RR8.i_divMap S (fun D => Work.CurveBasics.Curve.BCSquare.l_divMap S D) D

/-- **RR8**: the pullback of a canonical divisor is canonical. -/
theorem isCanonical_divMap (S : Work.CurveBasics.Curve.BCSquare C C') {W : C.Div}
    (hW : IsCanonical C W) : IsCanonical C' (S.divMap W) :=
  RR8.isCanonical_divMap S (fun D => Work.CurveBasics.Curve.BCSquare.l_divMap S D) hW

/-- **RR6 at the generic place**: adding the generic place of `C` to a divisor of positive index
of speciality drops `i` by exactly one.  This is the statement consumed by area GC. -/
theorem i_add_generic (C : Curve k) (A : C.Div) (hA : 0 < i C A) :
    i (C.baseChange (C.functionField : Type u))
        ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).divMap A
          + Curve.Div.place (genericPlace C)) + 1
      = i C A :=
  i_add_generic_of C A hA
    (fun D => Work.CurveBasics.Curve.BCSquare.l_divMap
      (Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)) D)
    (fun {D f} hf => by
      rw [Work.CurveBasics.Curve.BCSquare.L_divMap
        (Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)) D]
      exact Submodule.subset_span ⟨f, hf, rfl⟩)

end

end Curve

end Work.RiemannRoch
