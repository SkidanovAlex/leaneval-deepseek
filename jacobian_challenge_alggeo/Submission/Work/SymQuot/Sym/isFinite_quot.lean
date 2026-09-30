import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Sym.FiniteChart
import Submission.Work.SymQuot.Prod.isProper_prod
import Submission.Work.SymQuot.Chart.isFinite_quotientMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Sym

/-- **The quotient map `Cⁿ ⟶ Symⁿ C` is finite.**  The symmetric power `Symⁿ C` of a curve is the
quotient of `Cⁿ` by the action of `S_n`, and the quotient of a scheme of finite type over a field
by a finite group is finite over it: on each chart `Vⁿ ⊆ Cⁿ` (with `V ⊆ C` affine) the quotient
map is the chart map `Vⁿ ⟶ Spec Γ(Vⁿ)^{S_n}`, whose ring map is finite by
`ringHom_finite_subtype_invariants` (`Sym/FiniteChart.lean`), and the quotient map is obtained
from these chart maps by the local-on-the-target argument of
`Work.SymQuot.Chart.isFinite_quotientMap`. -/
theorem isFinite_quot {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) :
    AlgebraicGeometry.IsFinite (Work.SymQuot.Sym.quot C n).left := by
  -- `Cⁿ` is proper, hence locally of finite type, over `K`
  haveI hproper : IsProper (Work.SymQuot.prod C.toOver n).hom :=
    Work.SymQuot.Prod.isProper_prod C.toOver n
  haveI hlof : LocallyOfFiniteType (Work.SymQuot.prod C.toOver n).hom := inferInstance
  -- the chart map of every chart of `symData C n` is finite
  have hchart : ∀ U : (symData C n).Chart,
      IsFinite ((symData C n).action.chartMap U.1 U.2.2) := by
    intro U
    exact isFinite_chartMap (K := K) (X := Work.SymQuot.prod C.toOver n)
      (G := ULift.{u} (Equiv.Perm (Fin n))) (A := symAction C n)
      (sym_hom_invariant C n) U.2.1 U.2.2
  -- hence so is the quotient map of `Cⁿ` onto `Symⁿ C`
  haveI hfin : IsFinite (symData C n).quotientMap :=
    Work.SymQuot.Chart.isFinite_quotientMap (symData C n) hchart
  exact hfin

end Work.SymQuot.Sym
