/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The structure map and the pullback of sections of a base-changed curve (area SY)

For a curve `C` over a field `K` and a field extension `F/K`:

* `secConst C F W : F →+* Γ(C_F, W_F)` — the structure map, making the sections of the
  base-changed curve an `F`-algebra;
* `secAlpha C F W : Γ(C, W) →+* Γ(C_F, W_F)` — the pullback of sections along the projection
  `C_F ⟶ C`.

These are the two maps in terms of which the divisor ideal of a point of `Symⁿ C` is expressed.
They are separated from `DivOf/powMapAux.lean` (which uses them together with the chart data)
to keep the import graph acyclic: `DivOf` must be able to import `CharIdealGenDefs`.
-/
import Submission.Work.SymQuot.DivOf.CharIdeal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

variable {K : Type u} [Field K]

/-- The structure map `F →+* Γ(C_F, W_F)` of the base-changed curve, with the target written in
the form `Γ((C.baseChange F).left, C.bcOpens F W)`. -/
noncomputable def secConst (C : Curve K) (F : Type u) [Field F] [Algebra K F]
    (W : C.left.Opens) : F →+* Γ((C.baseChange F).left, C.bcOpens F W) :=
  sectionsAlgebraMap (C.baseChange F) (C.bcOpens F W)

/-- The pullback of sections along the projection `C_F ⟶ C`. -/
noncomputable def secAlpha (C : Curve K) (F : Type u) [Field F] [Algebra K F]
    (W : C.left.Opens) : Γ(C.left, W) →+* Γ((C.baseChange F).left, C.bcOpens F W) :=
  ((Curve.baseChangeFst C F).appLE W (C.bcOpens F W) le_rfl).hom

theorem secAlpha_apply (C : Curve K) (F : Type u) [Field F] [Algebra K F] (W : C.left.Opens)
    (b : Γ(C.left, W)) :
    secAlpha C F W b =
      ((Curve.baseChangeFst C F).appLE W ((Curve.baseChangeFst C F) ⁻¹ᵁ W) le_rfl).hom b := rfl

theorem secAlpha_eq_app (C : Curve K) (F : Type u) [Field F] [Algebra K F] (W : C.left.Opens)
    (b : Γ(C.left, W)) :
    secAlpha C F W b = ((Curve.baseChangeFst C F).app W).hom b := by
  rw [secAlpha_apply, ← Scheme.Hom.app_eq_appLE]

theorem secConst_apply (C : Curve K) (F : Type u) [Field F] [Algebra K F] (W : C.left.Opens)
    (c : F) :
    secConst C F W c = sectionsAlgebraMap (C.baseChange F) (C.bcOpens F W) c := rfl

end Work.SymQuot.DivOf
