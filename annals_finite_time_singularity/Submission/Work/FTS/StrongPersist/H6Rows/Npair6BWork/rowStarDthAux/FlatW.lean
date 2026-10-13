import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `w²σ^{-q}·(α+σ)σ^{α/5} ≤ 2 w²σ^{-γ}` on the open quadrant, for `q ≤ γ` and `α ∈ (0,1]`:
the flat price of a coefficient slot against the canonical slot weights of the `γ`-leaf. -/
theorem canonWMulFlatAgm {α q z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hq : q ≤ Work.Spaces.gam α) (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.FTS.TransportS.SlotT2.canonW q z θ
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      ≤ 2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : Work.Spaces.gam α = 1 + α / 10 := rfl
  have hexp : (0 : ℝ) ≤ α / 5 + (Work.Spaces.gam α - q) := by
    have : 0 ≤ Work.Spaces.gam α - q := by rw [hgam]; linarith
    linarith
  have hrpow : (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q)) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 hexp
  have hkey : (α + Real.sin (2 * θ))
        * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q)) ≤ 2 := by
    have h2 : (α + Real.sin (2 * θ)) ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ α + Real.sin (2 * θ) := by linarith
    calc (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q))
        ≤ (α + Real.sin (2 * θ)) * 1 := mul_le_mul_of_nonneg_left hrpow h0
      _ ≤ 2 := by linarith
  have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hmul : (Real.sin (2 * θ)) ^ (-q) * (Real.sin (2 * θ)) ^ (α / 5)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q)) := by
    rw [← Real.rpow_add hs, ← Real.rpow_add hs]
    congr 1
    ring
  rw [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.SlotT2.canonW]
  calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q)
          * (Real.sin (2 * θ)) ^ (α / 5)) * (α + Real.sin (2 * θ)) := by ring
    _ = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q)))
          * (α + Real.sin (2 * θ)) := by rw [hmul]
    _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ((α + Real.sin (2 * θ))
              * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q))) := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * 2 :=
        mul_le_mul_of_nonneg_left hkey
          (mul_nonneg hw (Real.rpow_nonneg hs.le _))
    _ = 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
