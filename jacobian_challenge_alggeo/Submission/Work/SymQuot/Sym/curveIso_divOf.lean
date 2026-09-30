import Mathlib
import Submission.Work.SymQuot.CurveIso
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivOf.divOf_powMapC1
import Submission.Work.SymQuot.Sym.sym_one
import Submission.Work.SpecLin.Points.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.Sym

/-! **`divOf` of the point `x ≫ curveIso C` of `Sym¹ C` is the point divisor `[x]`.**

Since `curveIso C = Sym.powMap C 1 (fun _ => 𝟙 C.toOver)` (definitionally) is the sum map of the
single point `𝟙 C.toOver`, naturality of `powMap` (`Sym.powMap_comp`) gives

`x ≫ curveIso C = Sym.powMap C 1 (fun _ : Fin 1 => x)`,

and then `DivOf.divOf_powMapC1` — the hub lemma C1′ of
`Submission/Work/NOTES_LEAD_jacobian_divof.md`, `divOf (powMap x) = ∑ m, ptDiv (x m)` for *any*
`n` — applied with `n = 1` and the `Fin 1`-sum collapsed by `Fin.sum_univ_one` yields the
claim. -/

open CategoryTheory Limits AlgebraicGeometry in
theorem curveIso_divOf {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (x : Work.SpecLin.CurveFPt C F) :
    Work.SymQuot.DivOf.divOf F (x ≫ Work.SymQuot.Sym.curveIso C) = Work.SpecLin.ptDiv x := by
  have h := Work.SymQuot.Sym.powMap_comp C 1 x (fun _ : Fin 1 => 𝟙 C.toOver)
  rw [show (fun m : Fin 1 => CategoryTheory.CategoryStruct.comp x (𝟙 C.toOver))
      = (fun _ : Fin 1 => x) from
    funext fun m => CategoryTheory.Category.comp_id x] at h
  have h' : x ≫ Work.SymQuot.Sym.curveIso C
      = Work.SymQuot.Sym.powMap C 1 (fun _ : Fin 1 => x) := h.symm
  rw [h', Work.SymQuot.DivOf.divOf_powMapC1 (C := C) (n := 1) (F := F)]
  exact Fin.sum_univ_one _

end Work.SymQuot.Sym
