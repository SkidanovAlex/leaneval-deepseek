import Mathlib
import Submission.Work.GenShared.periods_defs

namespace Work.GenShared

open Complex Metric Work.GenShared
open Submission.CDT (dRat)

theorem adjoint_eq_sum {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (hp2 : p2 ≠ 0) (a b : RatFunc ℂ) (c : Fin k → RatFunc ℂ)
    (h1 : dRat a - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b
        + ∑ i, c i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) = 0)
    (h2 : a + dRat b - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b = 0) :
    dRat (dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2
            * (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹)))
        - dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            * (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹))
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            * (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹)
      = ∑ i, c i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) := by
  -- `algebraMap p2` is nonzero, so the factor `p2 * (b * p2⁻¹)` is just `b`.
  have hP2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 ≠ 0 :=
    fun h => hp2 (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa using h))
  have hkey : algebraMap (Polynomial ℂ) (RatFunc ℂ) p2
      * (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹) = b := by
    rw [mul_comm b (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hP2, one_mul]
  rw [hkey]
  -- From `h1`, `h2` and additivity/`dRat_sub` of `dRat`, the sum equals the adjoint expression.
  have hS : (∑ i, c i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)))
      = dRat (dRat b)
        - dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            * (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹))
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            * (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹) := by
    have ha : a = (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b - dRat b := by
      linear_combination h2
    have hd : dRat a = dRat ((algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b) - dRat (dRat b) := by
      rw [ha, Submission.CDT.dRat_sub]
    have hS0 : (∑ i, c i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)))
        = (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b - dRat a := by
      linear_combination h1
    have harg0 : (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            * (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹) := by ring
    have harg1 : (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            * (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹) := by ring
    rw [hS0, hd, harg0, harg1]
    ring
  rw [hS]

end Work.GenShared
