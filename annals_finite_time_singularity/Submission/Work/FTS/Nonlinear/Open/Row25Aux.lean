import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row25
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.hkMem_prod_open_M
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.StrongEps.H5.Atoms.SinSqSlot5
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.AngProfAll
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.SolutionDelivery.DatumEuler
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row20 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row24 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row25Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-! ## Small `SmoothOpen` helpers on the open quadrant -/

/-! ## The smoothness/integrability helpers of row 25 -/

/-- The product of two angular `SmoothOpen` profiles is `SmoothOpen`. -/

theorem row25_smoothOpen_ang_mul {a b : ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hb : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => b θ)) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ * b θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 := (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun _ (θ : ℝ) => a θ)).mp ha n
  have h2 := (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun _ (θ : ℝ) => b θ)).mp hb n
  have hfun : Function.uncurry (fun (_ : ℝ) (θ : ℝ) => a θ * b θ)
      = fun p : ℝ × ℝ => a p.2 * b p.2 := rfl
  rw [hfun]
  exact h1.mul h2


/-- A constant angular profile is `SmoothOpen`. -/
theorem row25_smoothOpen_ang_const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => c) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun (_ : ℝ) (_ : ℝ) => c) = fun _ : ℝ × ℝ => c := rfl
  rw [hfun]
  exact contDiffOn_const

/-- `θ ↦ -sin²θ` is `SmoothOpen`. -/
theorem row25_smoothOpen_neg_sinSq :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => -((Real.sin θ) ^ 2)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun (_ : ℝ) (θ : ℝ) => -((Real.sin θ) ^ 2))
      = fun p : ℝ × ℝ => -((Real.sin p.2) ^ 2) := rfl
  rw [hfun]
  exact (((Real.contDiff_sin.comp contDiff_snd).pow 2).neg.contDiffOn).of_le le_top

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `SmoothOpen`. -/
theorem row25_smoothOpen_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.Gam α θ) := by
  have hG : (fun (_ : ℝ) (θ : ℝ) => Work.Spaces.Gam α θ)
      = fun (_ : ℝ) (θ : ℝ) => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
    funext z θ
    rw [Work.Spaces.Gam]
  rw [hG]
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hp'.2.1, Real.pi_pos]) (by linarith [hp'.2.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp'.2.1, Real.pi_pos], hp'.2.2⟩
    positivity
  have hfun : Function.uncurry (fun (_ : ℝ) (θ : ℝ) => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      = fun p : ℝ × ℝ => (Real.sin p.2 * Real.cos p.2 ^ 2) ^ (α / 3) := rfl
  rw [hfun]
  exact hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

/-- `z ↦ hKer z = z/(1+z)²` is `C^∞` on `(0,∞)`. -/
theorem row25_contDiffOn_hKer : ∀ n : ℕ,
    ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
  intro n
  simp only [Work.Spaces.hKer_apply]
  refine ContDiffOn.div (n := (n : WithTop ℕ∞)) (s := Set.Ioi 0)
    (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))
    (((contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add
      (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))).pow 2) ?_
  intro z hz
  have hz' : (0 : ℝ) < z := hz
  exact pow_ne_zero 2 (by linarith)



/-! ## The row -/


end Work.FTS.Nonlinear.Open
end
end
