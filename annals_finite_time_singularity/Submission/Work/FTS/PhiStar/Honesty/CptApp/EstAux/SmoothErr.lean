import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds
import Submission.Work.FTS_EllLimOK.Decay.DecayTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

set_option autoImplicit false

/-- `z ↦ lam n F z` is `C^∞` on `(0,∞)`, hence so is `z ↦ mu n F z = chiR n z * lam n F z`. -/
theorem contDiffOn_mu {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) {n : ℕ}
    (hn : 1 ≤ n) (m : ℕ) :
    ContDiffOn ℝ m (fun z : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z)
      (Set.Ioi 0) := by
  have hchi : ContDiffOn ℝ m (fun z : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z)
      (Set.Ioi 0) := (Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR n m).contDiffOn
  have hlam : ContDiffOn ℝ m (fun z : ℝ => Work.FTS.PhiStar.Honesty.CptApp.lam n F z)
      (Set.Ioi 0) := Work.FTS.PhiStar.Honesty.CptApp.LamEst.lamContDiffOn hsm hn m
  exact hchi.mul hlam

/-- The moment correction `(z,θ) ↦ mu n F z · rho θ` is smooth on the open quadrant. -/
theorem smoothOpen_muRho {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) {n : ℕ}
    (hn : 1 ≤ n) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
        * Work.FTS.PhiStar.Honesty.CptApp.rho θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun m => ?_
  have h1 : ContDiffOn ℝ m
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F p.1)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_mu hsm hn m).comp contDiffOn_fst (fun p hp => by
      rw [Work.FTS.EllipticEst.mem_Q0] at hp; exact hp.1)
  have h2 : ContDiffOn ℝ m (fun p : ℝ × ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.Honesty.CptApp.contDiff_rho m).contDiffOn.comp contDiffOn_snd
      (fun p _ => Set.mem_univ p.2)
  exact h1.mul h2

/-- The first piece of the error, `(z,θ) ↦ (chiR n z · zetaR n θ − 1)·F z θ`, is smooth on the
open quadrant. -/
theorem smoothOpen_chiZeta_sub_one {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun m => ?_
  have h1 : ContDiffOn ℝ m
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n p.1
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n p.2 - 1)
      Work.FTS.EllipticEst.Q0 := by
    refine ((Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR n m).contDiffOn.comp
      contDiffOn_fst (fun p _ => Set.mem_univ p.1)).mul ?_ |>.sub contDiffOn_const
    exact (Work.FTS.PhiStar.Honesty.CptApp.contDiff_zetaR n m).contDiffOn.comp contDiffOn_snd
      (fun p _ => Set.mem_univ p.2)
  exact h1.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hsm m)

/-- **`err n F` is smooth on the open quadrant.** -/
theorem smoothOpen_err {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) {n : ℕ}
    (hn : 1 ≤ n) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.Honesty.CptApp.err n F) := by
  have hfun : Work.FTS.PhiStar.Honesty.CptApp.err n F
      = fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ
          + -(Work.FTS.PhiStar.Honesty.CptApp.mu n F z
              * Work.FTS.PhiStar.Honesty.CptApp.rho θ) := by
    funext z θ
    rw [Work.FTS.PhiStar.Honesty.CptApp.err, Work.FTS.PhiStar.Honesty.CptApp.approx,
      Work.FTS.PhiStar.Honesty.CptApp.mu]
    ring
  rw [hfun]
  exact Work.FTS.EllipticEst.smoothOpen_add (smoothOpen_chiZeta_sub_one hsm n)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun m =>
      (smoothOpen_muRho hsm hn).forall m |>.neg)

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
