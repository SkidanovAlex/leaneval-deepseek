/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: the generic place of a curve

`C_{K(C)}` has a canonical `K(C)`-rational point over the generic point of `C`: the image of
the section `Spec K(C) ⟶ C`.  Area CB proves its existence (`Curve.exists_place_genericPoint`);
here we name it `genericPlace C` and record the three properties used by RR6:

* it has residue degree one (so adding it raises the degree by exactly one);
* `ord` of any pulled back nonzero function at it is `0`;
* it does not lie over a closed point of `C`, so the coefficient of `divMap D` at it vanishes.
-/
import Submission.Work.CurveBasics.Curve.exists_place_genericPoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The generic place of `C`: the canonical `K(C)`-rational point of `C_{K(C)}` lying over the
generic point of `C` (chosen once and for all from `Curve.exists_place_genericPoint`). -/
noncomputable def genericPlace (C : Curve k) :
    (C.baseChange (C.functionField : Type u)).Place :=
  Classical.choose (Work.CurveBasics.Curve.exists_place_genericPoint C)

theorem degree_genericPlace (C : Curve k) : (genericPlace C).degree = 1 :=
  (Classical.choose_spec (Work.CurveBasics.Curve.exists_place_genericPoint C)).1

theorem ordAt_genericPlace (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    (C.baseChange (C.functionField : Type u)).ordAt
      ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).fieldMap.hom f)
      (genericPlace C) = 0 :=
  (Classical.choose_spec (Work.CurveBasics.Curve.exists_place_genericPoint C)).2.1 f hf

theorem genericPlace_not_mem_image (C : Curve k) :
    ¬ IsClosed ({(C.baseChangeFst (C.functionField : Type u)) (genericPlace C).point} :
      Set C.left) :=
  (Classical.choose_spec (Work.CurveBasics.Curve.exists_place_genericPoint C)).2.2

end

end Curve

end Work.RiemannRoch
