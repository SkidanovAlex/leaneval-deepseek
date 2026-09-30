import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivOf.divMap_self
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SymQuot.DivOf.divMap_divOfChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

set_option linter.style.haveILetI false

namespace Work.SymQuot.DivOf

theorem divOf_powMapC1 {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (x : Fin n → Work.SpecLin.CurveFPt C F) :
    divOf F (Work.SymQuot.Sym.powMap C n x) = ∑ m, Work.SpecLin.ptDiv (x m) := by
  classical
  haveI : Nonempty (chartOf C n (Work.SymQuot.Sym.powMap C n x)).V :=
    chartOf_nonempty C n (Work.SymQuot.Sym.powMap C n x)
  have hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F)
        (Work.SymQuot.Sym.powMap C n x) := by
    rw [show IsScalarTower.toAlgHom K F F = AlgHom.id K F from
      AlgHom.ext (fun c => by simp [IsScalarTower.toAlgHom_apply]),
      Work.SpecLin.RPt.map_id]
  have h := divMap_divOfChart (C := C) (n := n) (F := F) (F' := F)
    (p := Work.SymQuot.Sym.powMap C n x)
    (d := chartOf C n (Work.SymQuot.Sym.powMap C n x)) x hx
  rw [show divOf F (Work.SymQuot.Sym.powMap C n x) =
      divOfChart F (chartOf C n (Work.SymQuot.Sym.powMap C n x)) from rfl,
    ← divMap_self (C := C) F (divOfChart F (chartOf C n (Work.SymQuot.Sym.powMap C n x)))]
  exact h

end Work.SymQuot.DivOf
