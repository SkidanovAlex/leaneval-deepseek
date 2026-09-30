import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.RiemannRoch.Adeles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Alt

/-- At a place `Q` of a curve, adding `1` to a function with a zero at `Q` makes the order of
vanishing zero, while adding `1` to a function with a pole at `Q` does not change the order of
vanishing; in both cases `a + 1` is nonzero. -/
theorem ordAt_add_one {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) (Q : C.Place)
    (a : C.functionField) :
    ((0 < C.ordAt a Q → C.ordAt (a + 1) Q = 0 ∧ a + 1 ≠ 0) ∧
     (C.ordAt a Q < 0 → C.ordAt (a + 1) Q = C.ordAt a Q ∧ a + 1 ≠ 0)) := by
  -- The order of vanishing of `x` at `Q` is the negative of the logarithm of the valuation
  -- of `x` at `Q`, `Q.valuation : K(C) → ℤᵐ⁰`.
  have hord : ∀ x : C.functionField, C.ordAt x Q = -(Q.valuation x).log :=
    fun x => Work.CurveBasics.Curve.Place.ord_eq_neg_log_valuation C Q x
  constructor
  · -- `a` vanishes at `Q`: then `a` lies in the maximal ideal of the local ring, so `1 + a`
    -- is a unit there and does not vanish.
    intro ha
    have hlog : (Q.valuation a).log < 0 :=
      neg_pos.mp (by rw [← hord a]; exact ha)
    have hlt : Q.valuation a < 1 := by
      simpa using WithZero.lt_exp_of_log_lt hlog
    have hv1 : Q.valuation (a + 1) = 1 := by
      rw [add_comm]
      exact Valuation.map_one_add_of_lt Q.valuation hlt
    constructor
    · rw [hord (a + 1), hv1, WithZero.log_one, neg_zero]
    · intro h
      exact one_ne_zero (by rw [← hv1, h, Valuation.map_zero])
  · -- `a` has a pole at `Q`: then `Q.valuation a > 1`, so `1` is strictly dominated by `a` and
    -- the valuation of `a + 1` equals that of `a`.
    intro ha
    have hlog : 0 < (Q.valuation a).log :=
      neg_lt_zero.mp (by rw [← hord a]; exact ha)
    have hv0 : Q.valuation a ≠ 0 := by
      intro h
      rw [h, WithZero.log_zero] at hlog
      exact lt_irrefl 0 hlog
    have h1 : 1 < Q.valuation a := by
      simpa using (WithZero.lt_log_iff_exp_lt hv0).mp hlog
    have hveq : Q.valuation (a + 1) = Q.valuation a := by
      rw [add_comm]
      exact Valuation.map_add_eq_of_lt_right Q.valuation (by simpa using h1)
    constructor
    · rw [hord (a + 1), hveq, hord a]
    · intro h
      exact hv0 (by rw [← hveq, h, Valuation.map_zero])

end Work.SpecLin.Alt
