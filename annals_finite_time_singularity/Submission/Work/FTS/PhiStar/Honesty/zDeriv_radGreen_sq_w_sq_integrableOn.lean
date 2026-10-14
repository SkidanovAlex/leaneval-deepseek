import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.EllExist

namespace Work.FTS.PhiStar.Honesty

set_option maxHeartbeats 3200000

/-- `(1+z)^4 ≤ 16` on `(0,1)`. -/
private lemma one_add_pow_four_le {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    (1 + z) ^ 4 ≤ 16 := by
  have h0 : (0 : ℝ) ≤ 1 + z := by linarith
  have h1 : 1 + z ≤ 2 := by linarith
  calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = 16 := by norm_num

/-- `(1+z)^4 ≤ 16·z^4` for `z ≥ 1`. -/
private lemma one_add_pow_four_le_mul {z : ℝ} (hz1 : 1 ≤ z) :
    (1 + z) ^ 4 ≤ 16 * z ^ 4 := by
  have h0 : (0 : ℝ) ≤ 1 + z := by linarith
  have h1 : 1 + z ≤ 2 * z := by linarith
  calc (1 + z) ^ 4 ≤ (2 * z) ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = 16 * z ^ 4 := by ring

/-- The weight identity `(w z)² = (1+z)⁴/z⁴`. -/
private lemma w_sq_eq (z : ℝ) : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  rw [show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring, show (z ^ 2) ^ 2 = z ^ 4 by ring]



end Work.FTS.PhiStar.Honesty
