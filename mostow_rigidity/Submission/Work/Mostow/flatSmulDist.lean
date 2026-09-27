import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.flatActBasic

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

theorem flatSmulDist {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (hg : Submission.Mostow.bd g ξ = ξ)
    (y y' : Submission.Mostow.E n) (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0)
    (D : ℝ) (hD : 0 < D) :
    ‖Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y D) - Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y' D)‖
      = (Work.Mostow.lev ξ (g • (0 : Submission.Mostow.E n)))⁻¹ * ‖y - y'‖ := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  set L : ℝ := lev ξ (g • (0 : E n)) with hLdef
  have hL : 0 < L := by rw [hLdef]; exact lev_pos ξ hξ (g • (0 : E n))
  set z : E n := yc ξ (g • hptOf ξ y D) with hzdef
  set z' : E n := yc ξ (g • hptOf ξ y' D) with hz'def
  -- The images have level `D * L`.
  have hlevg : lev ξ (g • hptOf ξ y D) = D * L := by
    rw [lev_smul_self hI' hA' ξ hξ g (hptOf ξ y D) hg, (hptOf_level ξ hξ D hD y hy).1]
  have hlevg' : lev ξ (g • hptOf ξ y' D) = D * L := by
    rw [lev_smul_self hI' hA' ξ hξ g (hptOf ξ y' D) hg, (hptOf_level ξ hξ D hD y' hy').1]
  have hDL : 0 < D * L := mul_pos hD hL
  -- Re-express the images through `hptOf` at their flat coordinates.
  have hgz : g • hptOf ξ y D = hptOf ξ z (D * L) :=
    (hptOf_yc ξ hξ (D * L) hDL (g • hptOf ξ y D) hlevg).symm
  have hgz' : g • hptOf ξ y' D = hptOf ξ z' (D * L) :=
    (hptOf_yc ξ hξ (D * L) hDL (g • hptOf ξ y' D) hlevg').symm
  -- The hyperbolic distance of the images, computed in two ways.
  have hdist_g : hdist (g • hptOf ξ y D) (g • hptOf ξ y' D)
      = Real.arcosh (1 + (D * ‖y - y'‖) ^ 2 / 2) := by
    rw [hI'.isom_smul g (hptOf ξ y D) (hptOf ξ y' D)]
    exact hptOf_hdist ξ hξ D hD y y' hy hy'
  have hdist_g' : hdist (g • hptOf ξ y D) (g • hptOf ξ y' D)
      = Real.arcosh (1 + (D * L * ‖z - z'‖) ^ 2 / 2) := by
    rw [hgz, hgz']
    exact hptOf_hdist ξ hξ (D * L) hDL z z' (yc_inner_orth hξ) (yc_inner_orth hξ)
  -- Hence the arguments of `arcosh` agree.
  have hEq : Real.arcosh (1 + (D * L * ‖z - z'‖) ^ 2 / 2)
      = Real.arcosh (1 + (D * ‖y - y'‖) ^ 2 / 2) := hdist_g'.symm.trans hdist_g
  have hA1 : (0 : ℝ) < 1 + (D * L * ‖z - z'‖) ^ 2 / 2 := by positivity
  have hA2 : (0 : ℝ) < 1 + (D * ‖y - y'‖) ^ 2 / 2 := by positivity
  have hle1 : 1 + (D * L * ‖z - z'‖) ^ 2 / 2 ≤ 1 + (D * ‖y - y'‖) ^ 2 / 2 :=
    (Real.arcosh_le_arcosh hA1 hA2).mp (le_of_eq hEq)
  have hle2 : 1 + (D * ‖y - y'‖) ^ 2 / 2 ≤ 1 + (D * L * ‖z - z'‖) ^ 2 / 2 :=
    (Real.arcosh_le_arcosh hA2 hA1).mp (le_of_eq hEq.symm)
  have harg : (D * L * ‖z - z'‖) ^ 2 = (D * ‖y - y'‖) ^ 2 := by linarith
  -- Both sides are non-negative, so the squared equality gives the equality.
  have hnn1 : (0 : ℝ) ≤ D * L * ‖z - z'‖ := by positivity
  have hnn2 : (0 : ℝ) ≤ D * ‖y - y'‖ := by positivity
  have hlin : D * L * ‖z - z'‖ = D * ‖y - y'‖ := by nlinarith [harg, hnn1, hnn2]
  have hmain : L * ‖z - z'‖ = ‖y - y'‖ := by
    refine mul_left_cancel₀ (ne_of_gt hD) ?_
    rw [← mul_assoc]
    exact hlin
  have key : ‖z - z'‖ = L⁻¹ * ‖y - y'‖ := by
    rw [eq_comm]
    calc L⁻¹ * ‖y - y'‖ = L⁻¹ * (L * ‖z - z'‖) := by rw [← hmain]
      _ = ‖z - z'‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hL), one_mul]
  simpa only [hzdef, hz'def] using key

end Work.Mostow
