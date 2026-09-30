import Mathlib
import Submission.Work.RiemannRoch.Pole
import Submission.Work.RiemannRoch.RR.snake
import Submission.Work.RiemannRoch.Linear.finrank_Lquot
import Submission.Work.RiemannRoch.Aquot.finrank_Aquot
import Submission.Work.CurveBasics.Divisor.deg_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

namespace Work.RiemannRoch.RR

open Work.CurveBasics

/-- **`l(E) - l(D) ≤ deg E - deg D` for `D ≤ E`.**

The quotient `L(E)/L(D)` is a `k`-subquotient of `A(E)/A(D)`: the snake identity
`dim A(E)/A(D) = dim L(E)/L(D) + dim (A(E)+K)/(A(D)+K)` (module `RR.snake`) gives
`dim L(E)/L(D) ≤ dim A(E)/A(D)`, Riemann's theorem `dim A(E)/A(D) = deg (E - D)`
(module `Aquot.finrank_Aquot`) evaluates the right hand side, and
`dim L(E)/L(D) = l E - l D` is `Linear.finrank_Lquot`. -/
theorem l_sub_l_le {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) : (C.l E : ℤ) - C.l D ≤ C.deg E - C.deg D := by
  -- `l` is monotone
  have hle : C.l D ≤ C.l E := by
    haveI : FiniteDimensional k ↥(C.L E) := Work.CurveBasics.Linear.finiteDimensional_L C E
    exact Submodule.finrank_mono
      (C.L_mono (Work.CurveBasics.Curve.Div.le_iff.mpr h))
  -- `dim L(E)/L(D) = l E - l D`
  have hLquot : Module.finrank k (Work.RiemannRoch.Curve.Lquot C D E) = C.l E - C.l D :=
    Work.RiemannRoch.Linear.finrank_Lquot C h
  -- the snake identity
  have hsnake : Module.finrank k (Work.RiemannRoch.Curve.Aquot C D E)
      = Module.finrank k (Work.RiemannRoch.Curve.Lquot C D E)
        + Module.finrank k (Work.RiemannRoch.Curve.Kquot C D E) :=
    snake C h
  -- Riemann's theorem for the adelic quotient
  have hAquot : Module.finrank k (Work.RiemannRoch.Curve.Aquot C D E)
      = (C.deg (E - D)).toNat := Work.RiemannRoch.Aquot.finrank_Aquot C h
  have hineq : C.l E - C.l D ≤ (C.deg (E - D)).toNat := by
    rw [← hLquot, ← hAquot, hsnake]
    exact Nat.le_add_right _ _
  -- `deg (E - D) = deg E - deg D ≥ 0`
  have hdeg : ((C.deg (E - D)).toNat : ℤ) = C.deg E - C.deg D := by
    have hEff : (E - D).IsEffective :=
      Work.CurveBasics.Curve.Div.le_iff.mpr fun Q => (Finsupp.le_def.mp h) Q
    rw [Int.toNat_of_nonneg (Work.CurveBasics.Divisor.deg_nonneg hEff),
      Work.CurveBasics.Curve.deg_sub]
  rw [← Nat.cast_sub hle, ← hdeg]
  exact_mod_cast hineq

end Work.RiemannRoch.RR
