import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.LatticeModel.LhyAuxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

/-- Rationalisation identity: on the positive half-line the rationalised bracket
`c²/((r²+c)+r√(r²+2c)) − c²/(2r²)` coincides with the algebraic form
`r²+c−r√(r²+2c) − c²/(2r²)`.  The point is
`((r²+c) − r√(r²+2c))·((r²+c) + r√(r²+2c)) = (r²+c)² − r²(r²+2c) = c²`. -/
theorem lhyProfile_eq_lhyF (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    lhyProfile c r = lhyF c r := by
  have hs : Real.sqrt (r ^ 2 + 2 * c) ^ 2 = r ^ 2 + 2 * c :=
    Real.sq_sqrt (by nlinarith)
  have hprod : ((r ^ 2 + c) - r * Real.sqrt (r ^ 2 + 2 * c)) *
      ((r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c)) = c ^ 2 := by
    nlinarith [hs]
  have hD : (r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c) ≠ 0 := by
    have h1 : 0 ≤ Real.sqrt (r ^ 2 + 2 * c) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg r, hc, hr, h1, mul_nonneg (le_of_lt hr) h1]
  rw [lhyProfile, lhyF]
  have key : c ^ 2 / ((r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c))
      = (r ^ 2 + c) - r * Real.sqrt (r ^ 2 + 2 * c) := by
    rw [div_eq_iff hD]
    linarith [hprod]
  rw [key]

end Work.BoseBox.LatticeModel
