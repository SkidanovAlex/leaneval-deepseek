import Mathlib
import Submission.Work.GCBasics.DivApi
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GCBasics

open Work.CurveBasics

/-- A rational function `h` on a curve `C` has zero divisor if and only if it is constant:
`C.div h = 0 ↔ ∃ c : k, h = algebraMap k C.functionField c`.

`div h = 0` says that `h` has neither zeros nor poles, i.e. `h ∈ L 0`; a function in `L 0` is
algebraic over `k` (`Work.CurveBasics.Linear.isAlgebraic_of_mem_L_zero`) and `k` is relatively
algebraically closed in `K(C)` (`Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic`), so `h`
is a constant.  Conversely the divisor of a constant is zero
(`Work.CurveBasics.Order.div_algebraMap_eq_zero`). -/
theorem div_eq_zero_iff_isConstant {k : Type _} [Field k] (C : Work.CurveBasics.Curve k)
    {h : C.functionField} :
    C.div h = 0 ↔ ∃ c : k, h = algebraMap k C.functionField c := by
  constructor
  · intro hh
    -- `div h = 0` means `h ∈ L 0`.
    have hmem : h ∈ C.L (0 : C.Div) := by
      rw [Curve.mem_L_iff]
      by_cases h0 : h = 0
      · exact Or.inl h0
      · refine Or.inr fun Q => ?_
        rw [hh]
        simp
    -- functions in `L 0` are algebraic over `k`, and algebraic elements are constants.
    exact Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic C
      (Work.CurveBasics.Linear.isAlgebraic_of_mem_L_zero C hmem)
  · rintro ⟨c, rfl⟩
    exact Work.CurveBasics.Order.div_algebraMap_eq_zero C c

end Work.GCBasics
