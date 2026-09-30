import Mathlib
import Submission.Work.Charts.Core
import Submission.Work.SymQuot.Prod.isProper_prod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-
# `IsProper` for the quotient map `C^n ⟶ Sym^n C` (area CH)

The Brill–Noether chart of `ChartCg.lean` is the complement of the image of `C^n ∖ D(δ)` under
the quotient map `quotMap C n : C^n ⟶ Sym^n C`; that complement is open (`chartOpen`) exactly
because `quotMap` is a closed map, which follows from its being a proper morphism.

`quotMap` is the underlying morphism of a morphism in `Over (Spec K)` (namely area `SY`'s
addition map `powMap`), so it sits in a triangle

    C^n --quotMap--> Sym^n C
      \                 /
     (C^n).hom      (Sym^n C).hom
        \             /
         Spec K

over `Spec K`.  The source `C^n` is proper over `K` (`SymQuot.Prod.isProper_prod`) and the
target `Sym^n C` is separated over `K` (it is proper, area `SY`'s `SymGeom.isProper`), hence
`quotMap` is proper: this is the cancellation `IsProper.of_comp` applied to
`quotMap ≫ (Sym^n C).hom = (C^n).hom` and the separatedness of `(Sym^n C).hom`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

theorem isProper_quotMap {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (n : ℕ) [Work.SpecLin.SymGeom C n] :
    AlgebraicGeometry.IsProper (Work.Charts.quotMap C n).left := by
  have hSrc : IsProper (Cprod C n).hom :=
    Work.SymQuot.Prod.isProper_prod C.toOver n
  have hTgt : IsProper (Sym C n).hom :=
    Work.SpecLin.SymGeom.isProper
  have hcomp : IsProper ((quotMap C n).left ≫ (Sym C n).hom) := by
    rw [(quotMap C n).w]
    exact hSrc
  exact @IsProper.of_comp _ _ _ (quotMap C n).left (Sym C n).hom hcomp hTgt.toIsSeparated

end Work.Charts
