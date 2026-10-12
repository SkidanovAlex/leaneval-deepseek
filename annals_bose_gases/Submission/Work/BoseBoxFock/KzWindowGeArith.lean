import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem KzWindowGeArith {SA SB SC Cn M n : ℝ} (hSA : 0 ≤ SA) (hSB : 0 ≤ SB) (hSC : 0 ≤ SC)
    (hCn : 0 ≤ Cn) (hM : 0 ≤ M) (hn : 0 ≤ n) :
    -((SA + SB + 2 * SC) * (Cn * (M + 1) + Real.sqrt (Cn * (M + 1)) + 1) * n)
      ≤ -(1 / 2) * (SA * (2 * Cn * M * n) + SB * (2 * Cn * (M + 1) * n)
          + SC * (4 * Real.sqrt (Cn * (M + 1)) * n)) := by
  have hY : 0 ≤ Real.sqrt (Cn * (M + 1)) := Real.sqrt_nonneg _
  have hY2 : (Real.sqrt (Cn * (M + 1)))^2 = Cn * (M + 1) :=
    Real.sq_sqrt (by nlinarith)
  nlinarith [mul_nonneg hSA hn, mul_nonneg hSB hn, mul_nonneg hSC hn,
    mul_nonneg hCn hM, mul_nonneg (mul_nonneg hCn hM) hn]

end Work.BoseBoxFock
