import Mathlib
import Submission.Work.Mostow.disp_blk
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.cosh_hdist_fermi

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

open Submission.Mostow in
theorem blkDispFermi (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v : E j) (w : E m) :
    Real.sinh (hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2)
      = Real.sinh ‖w‖ * ‖R (‖w‖⁻¹ • w) - ‖w‖⁻¹ • w‖ / 2 := by
  -- the identity element fixes `v`
  have h1v : (1 : PO j 1) • v = v := hAj.2.2.2.1 v
  -- hence `hdist v ((1 : PO j 1) • v) = 0`
  have hd0 : hdist v ((1 : PO j 1) • v) = 0 := by
    rw [h1v]
    exact (hIj.2.2.1 v v).mpr rfl
  -- F7 (`disp_blk`) with `h = 1`: the stratum contribution vanishes
  have hsq : (Real.sinh (hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2)) ^ 2
      = Real.sinh ‖w‖ ^ 2 * ‖R (‖w‖⁻¹ • w) - ‖w‖⁻¹ • w‖ ^ 2 / 4 := by
    have h := disp_blk j m hAj hIj hA hI (1 : PO j 1) R v w
    rw [hd0] at h
    simpa using h
  -- both sides of the identity are nonnegative, so squaring is injective
  have ha : 0 ≤ Real.sinh (hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2) :=
    Real.sinh_nonneg_iff.mpr (div_nonneg (hI.1 _ _) (by norm_num))
  have hb : 0 ≤ Real.sinh ‖w‖ * ‖R (‖w‖⁻¹ • w) - ‖w‖⁻¹ • w‖ / 2 :=
    div_nonneg (mul_nonneg (Real.sinh_nonneg_iff.mpr (norm_nonneg w)) (norm_nonneg _))
      (by norm_num)
  have hsq2 : (Real.sinh (hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2)) ^ 2
      = (Real.sinh ‖w‖ * ‖R (‖w‖⁻¹ • w) - ‖w‖⁻¹ • w‖ / 2) ^ 2 := by
    rw [hsq]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
  · exact h
  · linarith

end Work.Mostow
