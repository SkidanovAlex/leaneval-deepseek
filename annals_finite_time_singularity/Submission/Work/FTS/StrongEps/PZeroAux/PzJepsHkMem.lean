import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.PZeroAux.classC_Pz
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.PZeroAux

theorem PzJepsHkMem {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {f : ℝ → ℝ → ℝ} (k : ℕ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f)) := by
  -- `J_ε` preserves `ℋ^k`-membership (E1, `HkMem_Jeps`) ...
  have hJ : Work.Spaces.HkMem α k (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsm hmem
  -- ... and it is `C^∞` on the open quadrant.
  have hsJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsm
  -- The projection subtracts a constant multiple of the correction profile `bump`.
  set c : ℝ := -(Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0
      / Work.FTS.StrongEps.pzNorm) with hc
  have hb : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump :=
    Work.FTS.StrongEps.PZeroAux.classC_Pz_hkMem_bump α k
  have hcm : Work.Spaces.HkMem α k (fun z θ => c * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen c hb
  have hscm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen c Work.FTS.StrongEps.smoothOpen_bump
  have hPz : Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f)
      = fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ + c * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, hc]
    ring
  rw [hPz]
  exact Work.FTS.EllipticEst.HkMem_add_open hsJ hscm hJ hcm

end Work.FTS.StrongEps.PZeroAux
