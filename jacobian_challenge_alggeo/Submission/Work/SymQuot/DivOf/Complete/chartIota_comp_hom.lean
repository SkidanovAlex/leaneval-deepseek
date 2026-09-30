import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

universe u


namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
theorem chartIota_comp_hom {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] (U : (Work.SymQuot.symData C n).Chart) :
    (Work.SymQuot.symData C n).chartι U ≫ (Work.SymQuot.Sym C n).hom =
      Spec.map (CommRingCat.ofHom (chartConst C n U)) := by
  rw [Work.SymQuot.Sym.hom_def]
  have hconst : CommRingCat.ofHom (chartConst C n U) =
      (Scheme.ΓSpecIso ↧K).inv ≫
        Scheme.Hom.appTop ((Work.SymQuot.symData C n).chartι U ≫
          (Work.SymQuot.symData C n).quotientHom (Work.SymQuot.prod C.toOver n).hom
            (Work.SymQuot.sym_hom_invariant C n)) ≫
        (Scheme.ΓSpecIso (Work.SymQuot.GAction.chartRing
          (Work.SymQuot.symAction C n) U.1 U.2.2)).hom :=
    rfl
  rw [hconst, Spec.map_comp, Spec.map_comp]
  rw [← Scheme.isoSpec_Spec_hom, ← Scheme.isoSpec_Spec_inv]
  rw [Scheme.isoSpec_hom_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Work.SymQuot.DivOf.Complete
