import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- Pure-real arithmetic row: the coefficient `A = (1/2)(BB²+BB)√ρ` of `log T` is
nonnegative and bounded by `2·BB` (`BB ≤ 1`, `√ρ ≤ 2`), while `log T ≤ 56 + L/1292`;
so the product is at most `BB·(112 + L/646)`, and `L ≥ 231 ≥ 71706/311` upgrades
`112 + L/646` to `1 + (156/323)·L`, which is paid by `eps`. -/
theorem row1Arith {c1 c2 epsT sqrtRho BB L T eps : ℝ} (hBB0 : 0 ≤ BB) (hBB1 : BB ≤ 1) (hL0 : 0 ≤ L) (hLbig : 231 ≤ L) (heps0 : 0 < eps) (hs0 : 0 ≤ sqrtRho) (hs2 : sqrtRho ≤ 2) (hval : c1 + epsT * c2 = (1 / 2) * (BB ^ 2 + BB) * sqrtRho) (hlog : Real.log T ≤ 56 + (1 / 1292) * L) (hE3 : BB * (1 + ((156 : ℝ) / 323) * L) ≤ eps) : (c1 + epsT * c2) * Real.log T ≤ eps := by
  -- The coefficient of `log T` is nonnegative.
  have hA0 : 0 ≤ (1 / 2) * (BB ^ 2 + BB) * sqrtRho := by
    nlinarith [hBB0, hs0, sq_nonneg BB]
  -- It is at most `2 · BB`.
  have hcoef : (1 / 2) * (BB + 1) * sqrtRho ≤ 2 := by
    have h1 : (1 / 2 : ℝ) * (BB + 1) ≤ 1 := by linarith
    calc (1 / 2 : ℝ) * (BB + 1) * sqrtRho ≤ 1 * sqrtRho := mul_le_mul_of_nonneg_right h1 hs0
      _ ≤ 2 := by linarith
  have hA2 : (1 / 2) * (BB ^ 2 + BB) * sqrtRho ≤ 2 * BB := by
    have hrw : (1 / 2) * (BB ^ 2 + BB) * sqrtRho = BB * ((1 / 2) * (BB + 1) * sqrtRho) := by ring
    rw [hrw]
    nlinarith [hcoef, hBB0]
  -- The linear-in-`L` comparison, from `L ≥ 231`.
  have hnum : 2 * (56 + (1 / 1292) * L) ≤ 1 + ((156 : ℝ) / 323) * L := by linarith
  have hkey : 2 * BB * (56 + (1 / 1292) * L) ≤ BB * (1 + ((156 : ℝ) / 323) * L) := by
    have := mul_le_mul_of_nonneg_right hnum hBB0
    linarith [this]
  calc
    (c1 + epsT * c2) * Real.log T = ((1 / 2) * (BB ^ 2 + BB) * sqrtRho) * Real.log T := by rw [hval]
    _ ≤ ((1 / 2) * (BB ^ 2 + BB) * sqrtRho) * (56 + (1 / 1292) * L) :=
        mul_le_mul_of_nonneg_left hlog hA0
    _ ≤ 2 * BB * (56 + (1 / 1292) * L) :=
        mul_le_mul_of_nonneg_right hA2 (by linarith)
    _ ≤ BB * (1 + ((156 : ℝ) / 323) * L) := hkey
    _ ≤ eps := hE3

end Work.BoseBogFS
