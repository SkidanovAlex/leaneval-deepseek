import Mathlib

namespace Work.EKLC6Core

/-- Arithmetic estimate used in the injectivity/capacity bound: for `0 < I < 1/8`
and `0 < a ≤ I/8` the linear-in-`I` expression stays below `4 * I`. -/
theorem injCap_smul_arith {I a : ℝ} (hI : 0 < I) (hI8 : I < 1 / 8) (ha : 0 < a)
    (ha8 : a ≤ I / 8) :
    (1 + 33 * a + 90 * a ^ 2) * I + (11 * a + 30 * a ^ 2) < 4 * I := by
  nlinarith

end Work.EKLC6Core
