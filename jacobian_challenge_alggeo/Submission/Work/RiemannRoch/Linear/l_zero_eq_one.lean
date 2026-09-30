import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.RiemannRoch.Linear

open Work.CurveBasics

theorem l_zero_eq_one {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) : C.l 0 = 1 := by
  have hspan : C.L 0 = Submodule.span k ({1} : Set C.functionField) := by
    refine le_antisymm (Work.CurveBasics.Linear.L_zero_le_span_one C) ?_
    rw [Submodule.span_le]
    intro x hx
    have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
    rw [hx1]
    -- `1 ∈ C.L 0`, proved directly from `div 1 = 0` (avoids relying on the normal form of
    -- `algebraMap` at `1`).
    have hdiv : C.div (1 : C.functionField) = 0 := by
      have h := C.div_mul (one_ne_zero : (1 : C.functionField) ≠ 0)
        (one_ne_zero : (1 : C.functionField) ≠ 0)
      rw [mul_one] at h
      have h' : C.div (1 : C.functionField) + 0 = C.div (1 : C.functionField) + C.div 1 := by
        rw [add_zero]; exact h
      exact (add_left_cancel h').symm
    refine (Work.CurveBasics.Curve.mem_L_iff C).mpr (Or.inr ?_)
    rw [hdiv]
    simpa using Curve.Div.isEffective_zero (C := C)
  rw [Work.CurveBasics.Curve.l, hspan]
  exact finrank_span_singleton (one_ne_zero : (1 : C.functionField) ≠ 0)

end Work.RiemannRoch.Linear
