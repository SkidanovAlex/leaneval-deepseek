import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Levels._stub
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev15
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev16
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_psiField_merPsi_of_mem_Uax
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev17

open Filter Set MeasureTheory
open scoped Topology

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {C : Physical.PhysClock} {t : ℝ}
  {τ : ℝ}

theorem continuousAt_radial : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radial x) := by
  have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radial x)
      = fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by funext x; rfl
  rw [h]; fun_prop

theorem continuousAt_axial : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.axial x) := by
  have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.axial x) = fun x => x 2 := by funext x; rfl
  rw [h]; fun_prop

theorem continuous_radialVec : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radialVec x) := by
  have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radialVec x)
      = fun x => (!₂[x 0, x 1, 0] : Work.FTS.BSIdent.R3) := by funext x; rfl
  rw [h]; fun_prop

/-- `Cyl.psiField ψ` is continuous at every point off the axis. -/
theorem continuousAt_psiField_offaxis (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hB : 0 < B τ) {x : Work.FTS.BSIdent.R3}
    (hx : Work.Cyl.radial x ≠ 0) :
    ContinuousAt (fun y : Work.FTS.BSIdent.R3 =>
      Cyl.psiField (Cyl.merPsiT α A B Φ C t) y) x := by
  have hrx : 0 < Work.Cyl.radial x := lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hx)
  have hsmc : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ) := by
    rw [← hτ]
    exact hsm
  have hBc : 0 < B (Physical.clockInv C t) := by rwa [← hτ]
  have h0c : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0 := by
    rw [← hτ]
    exact h0
  by_cases hal : Work.Cyl.axial x = 0
  · -- the point is on the plane `θ = 0`
    have hpair : ContinuousAt (fun y : Work.FTS.BSIdent.R3 =>
        (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
      (continuousAt_radial.continuousAt).prodMk (continuousAt_axial.continuousAt)
    have hP : ContinuousAt (fun y : Work.FTS.BSIdent.R3 =>
        Cyl.pdZ (Cyl.merPsiT α A B Φ C t) (Work.Cyl.radial y) (Work.Cyl.axial y)
          / Work.Cyl.radial y) x := by
      refine ContinuousAt.comp (x := x)
        (f := fun y : Work.FTS.BSIdent.R3 => (Work.Cyl.radial y, Work.Cyl.axial y))
        (g := fun p : ℝ × ℝ =>
          Cyl.pdZ (Cyl.merPsiT α A B Φ C t) p.1 p.2 / p.1) ?_ hpair
      rw [hal]
      exact Dev15.continuousAt_pdZ_div_zero (α := α) (τ := Physical.clockInv C t) hrx rfl hsmc h0c hBc
    have hQ : ContinuousAt (fun y : Work.FTS.BSIdent.R3 =>
        -(Cyl.merPsiT α A B Φ C t (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
        - Cyl.pdR (Cyl.merPsiT α A B Φ C t) (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
      refine ContinuousAt.comp (x := x)
        (f := fun y : Work.FTS.BSIdent.R3 => (Work.Cyl.radial y, Work.Cyl.axial y))
        (g := fun p : ℝ × ℝ =>
          -(Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1) - Cyl.pdR (Cyl.merPsiT α A B Φ C t) p.1 p.2)
        ?_ hpair
      rw [hal]
      exact Dev16.continuousAt_Q_zero (α := α) (τ := Physical.clockInv C t) hrx rfl hsmc h0c hBc
    have hfun : (fun y : Work.FTS.BSIdent.R3 => Cyl.psiField (Cyl.merPsiT α A B Φ C t) y)
        = fun y => (Cyl.pdZ (Cyl.merPsiT α A B Φ C t) (Work.Cyl.radial y) (Work.Cyl.axial y)
              / Work.Cyl.radial y) • Work.Cyl.radialVec y
            + (-(Cyl.merPsiT α A B Φ C t (Work.Cyl.radial y) (Work.Cyl.axial y)
                  / Work.Cyl.radial y)
                - Cyl.pdR (Cyl.merPsiT α A B Φ C t) (Work.Cyl.radial y) (Work.Cyl.axial y))
              • Work.Cyl.eZ := rfl
    rw [hfun]
    exact (hP.smul continuous_radialVec.continuousAt).add (hQ.smul_const Work.Cyl.eZ)
  · -- `θ ≠ 0`: use the `C²`-regularity of the meridian slice
    have hsm2 : ∀ w θ : ℝ, 0 < w → 0 < θ → θ < Real.pi / 2 →
        ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ) := by
      intro w θ hw hθ hθ2
      exact hsmc w θ (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hslice : ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        Cyl.merPsiT α A B Φ C t p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x) := by
      have := Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice α A B Φ C t hBc hsm2 hrx hal
      simpa [Work.FTS.BSIdent.Cyl.merPsiT] using this
    exact ((Work.FTS.BSIdent.Defs.psiField_contDiffAt_one hrx hslice).continuousAt)

end Work.FTS.BSIdent.Weyl.Dev17
