import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- `Gam α 0 = 0` for `α ≠ 0`. -/
theorem Gam_zero_left {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  have h : (Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2) = 0 := by
    rw [Real.sin_zero, Real.cos_zero]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < α / 3))]

/-- `Gam α (π/2) = 0` for `α ≠ 0`. -/
theorem Gam_zero_pi {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α (π / 2) = 0 := by
  have h : (Real.sin (π / 2) * Real.cos (π / 2) ^ 2) = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < α / 3))]

/-- `F_*(·,0) = 0`. -/
theorem Fstar_zero_left {α : ℝ} (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z 0 = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_left hα]
  ring

/-- `F_*(·,π/2) = 0`. -/
theorem Fstar_zero_pi {α : ℝ} (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z (π / 2) = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_pi hα]
  ring


end Work.FTS_RegExport
