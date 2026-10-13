import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF
import Submission.Work.FTS.EllipticEst.I1Ae.RIFLimits
import Submission.Work.FTS.EllipticEst.I1Ae.RIFMain
import Submission.Work.FTS.EllipticEst.I1Ae.RIFCollar
import Submission.Work.FTS.EllipticEst.I1Ae.RIFPsi
import Submission.Work.FTS.EllipticEst.I1Ae.zibpChain
import Submission.Work.FTS.EllipticEst.I1Ae.thetaChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)

/-! ## Continuity and a.e. measurability helpers on the open quadrant -/

/-- a.e. strong measurability w.r.t. `nuQ` from continuity on the open quadrant. -/
theorem aesm_nuQ_of_continuousOn {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable F nuQ := by
  have h := Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hF
  rwa [nuFts_eq_nuQ] at h

theorem continuousOn_uncurry_U {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (fun p : ℝ × ℝ => U u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
  (AeI1Fts.smoothOpen_U hS).continuousOn

theorem continuousOn_uncurry_V {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (fun p : ℝ × ℝ => V u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
  (AeI1Fts.smoothOpen_V hS).continuousOn

theorem continuousOn_uncurry_AA {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (fun p : ℝ × ℝ => AA u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
  (AeI1Fts.smoothOpen_AA hS).continuousOn

theorem continuousOn_uncurry_BB {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (fun p : ℝ × ℝ => BB u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
  (AeI1Fts.smoothOpen_BB hS).continuousOn

theorem continuousOn_uncurry_sigE :
    ContinuousOn (fun p : ℝ × ℝ => sigE p.2) Work.FTS.EllipticEst.Q0 :=
  sigE_continuousOn_Iθo.comp continuous_snd.continuousOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)

theorem continuousOn_uncurry_sig1 :
    ContinuousOn (fun p : ℝ × ℝ => sig1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  refine (hsin.continuousOn.rpow_const (p := -(1 + Work.Spaces.eta)) (fun p hp => Or.inl
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by have := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1; linarith)
      (by have := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2; linarith [Real.pi_pos]))))).congr
    (fun p _ => rfl)

theorem continuousOn_uncurry_cos2 :
    ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn

theorem continuousOn_uncurry_chi (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => χ n p.1) Work.FTS.EllipticEst.Q0 :=
  ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn

theorem continuousOn_uncurry_dchi (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (χ n) p.1) Work.FTS.EllipticEst.Q0 :=
  (((Work.FTS.EllipticEst.cut_contDiff n).continuous_deriv (by norm_num)).comp
    continuous_fst).continuousOn

theorem continuousOn_uncurry_psi (ε : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ψ ε p.2) Work.FTS.EllipticEst.Q0 :=
  ((SliceMixedAux.cut_contDiff ε).continuous.comp continuous_snd).continuousOn

theorem continuousOn_uncurry_dpsi (ε : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (ψ ε) p.2) Work.FTS.EllipticEst.Q0 :=
  (((SliceMixedAux.cut_contDiff ε).continuous_deriv (by norm_num)).comp
    continuous_snd).continuousOn

theorem continuousOn_uncurry_Fd {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (fun p : ℝ × ℝ => Fd u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => p.1 * ((U u p.1 p.2) * BB u p.1 p.2)
      * (Work.Spaces.w p.1) ^ 2) Work.FTS.EllipticEst.Q0 :=
    (continuous_fst.continuousOn.mul
      ((continuousOn_uncurry_U hS).mul (continuousOn_uncurry_BB hS))).mul continuousOn_w_sq_fst
  refine h1.congr ?_
  intro p _
  simp only [Fd, U, BB]
  ring

end Work.FTS.EllipticEst.I1Ae
