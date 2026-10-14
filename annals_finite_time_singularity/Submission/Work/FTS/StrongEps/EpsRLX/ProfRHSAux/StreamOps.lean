import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate
import Submission.Work.Stability.ZcutSmoothCompact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The operator identities for the total stream function -/

/-- **`ℛ(Φ̃_tot) = ℛ(Φ̃_*) + ℛ(Φ̃_ell)`** at every interior point (`z > 0`, `0 < θ < π/2`). -/
theorem Rop_PsiTot_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) (hWs : Work.FTS.EllipticEst.SmoothOpen W)
    (hWm : Work.Spaces.HkMem α 4 W) (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Construction.Rop α (PsiTot α Φs W Φg) z θ
      = Work.Construction.Rop α (PsiStar α Φs) z θ
        + Work.Construction.Rop α (PsiEll α W Φg) z θ := by
  have hadd := L12Ftot_add hα hα1 hWs hWm
  have hstar := PsiStar_diff hα hα1 hΦs hz hθ0 hθ1
  have hell := PsiEll_diff hα hα1 hWs hWm hΦg hz hθ0 hθ1
  have hv : PsiTot α Φs W Φg z θ = PsiStar α Φs z θ + PsiEll α W Φg z θ :=
    PsiTot_value_eq hadd (le_of_lt hz)
  have ht : (fun θ' => PsiTot α Φs W Φg z θ')
      = fun θ' => PsiStar α Φs z θ' + PsiEll α W Φg z θ' :=
    PsiTot_tslice_eq hadd (le_of_lt hz)
  have ht' : Work.Spaces.pth (PsiTot α Φs W Φg) z θ
      = Work.Spaces.pth (PsiStar α Φs) z θ + Work.Spaces.pth (PsiEll α W Φg) z θ := by
    simp only [Work.Spaces.pth, ht,
      show (fun θ' => PsiStar α Φs z θ' + PsiEll α W Φg z θ')
        = (fun θ' => PsiStar α Φs z θ') + (fun θ' => PsiEll α W Φg z θ') from rfl,
      deriv_add hstar.2 hell.2]
  have hz' : Work.Spaces.pz (PsiTot α Φs W Φg) z θ
      = Work.Spaces.pz (PsiStar α Φs) z θ + Work.Spaces.pz (PsiEll α W Φg) z θ := by
    have hev : (fun z' => PsiTot α Φs W Φg z' θ)
        =ᶠ[𝓝 z] fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ :=
      PsiTot_zslice_eventuallyEq hadd hz
    have hd : DifferentiableAt ℝ
        (fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ) z := hstar.1.add hell.1
    have h1 : deriv (fun z' => PsiTot α Φs W Φg z' θ) z
        = deriv (fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ) z :=
      deriv_eq_of_eventuallyEq hev hd
    have h2 : deriv (fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ) z
        = deriv (fun z' => PsiStar α Φs z' θ) z + deriv (fun z' => PsiEll α W Φg z' θ) z :=
      deriv_add hstar.1 hell.1
    simp only [Work.Spaces.pz]
    rw [h1, h2]
  simp only [Work.Construction.Rop, hv, hz', ht']
  ring

/-- **`U(Φ̃_tot) = U(Φ̃_*) + U(Φ̃_ell)`** at every interior point. -/
theorem Uop_PsiTot_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) (hWs : Work.FTS.EllipticEst.SmoothOpen W)
    (hWm : Work.Spaces.HkMem α 4 W) (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
      = Work.Construction.Uop α (PsiStar α Φs) z θ
        + Work.Construction.Uop α (PsiEll α W Φg) z θ := by
  have hadd := L12Ftot_add hα hα1 hWs hWm
  have hstar := PsiStar_diff hα hα1 hΦs hz hθ0 hθ1
  have hell := PsiEll_diff hα hα1 hWs hWm hΦg hz hθ0 hθ1
  have hv : PsiTot α Φs W Φg z θ = PsiStar α Φs z θ + PsiEll α W Φg z θ :=
    PsiTot_value_eq hadd (le_of_lt hz)
  have hz' : Work.Spaces.pz (PsiTot α Φs W Φg) z θ
      = Work.Spaces.pz (PsiStar α Φs) z θ + Work.Spaces.pz (PsiEll α W Φg) z θ := by
    have hev : (fun z' => PsiTot α Φs W Φg z' θ)
        =ᶠ[𝓝 z] fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ :=
      PsiTot_zslice_eventuallyEq hadd hz
    have hd : DifferentiableAt ℝ
        (fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ) z := hstar.1.add hell.1
    have h1 : deriv (fun z' => PsiTot α Φs W Φg z' θ) z
        = deriv (fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ) z :=
      deriv_eq_of_eventuallyEq hev hd
    have h2 : deriv (fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ) z
        = deriv (fun z' => PsiStar α Φs z' θ) z + deriv (fun z' => PsiEll α W Φg z' θ) z :=
      deriv_add hstar.1 hell.1
    simp only [Work.Spaces.pz]
    rw [h1, h2]
  simp only [Work.Construction.Uop, hv, hz']
  ring

/-- **`V(Φ̃_tot) = V(Φ̃_*) + V(Φ̃_ell)`** at every interior point. -/
theorem Vop_PsiTot_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) (hWs : Work.FTS.EllipticEst.SmoothOpen W)
    (hWm : Work.Spaces.HkMem α 4 W) (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Construction.Vop (PsiTot α Φs W Φg) z θ
      = Work.Construction.Vop (PsiStar α Φs) z θ
        + Work.Construction.Vop (PsiEll α W Φg) z θ := by
  have hadd := L12Ftot_add hα hα1 hWs hWm
  have hstar := PsiStar_diff hα hα1 hΦs hz hθ0 hθ1
  have hell := PsiEll_diff hα hα1 hWs hWm hΦg hz hθ0 hθ1
  have hv : PsiTot α Φs W Φg z θ = PsiStar α Φs z θ + PsiEll α W Φg z θ :=
    PsiTot_value_eq hadd (le_of_lt hz)
  have ht : (fun θ' => PsiTot α Φs W Φg z θ')
      = fun θ' => PsiStar α Φs z θ' + PsiEll α W Φg z θ' :=
    PsiTot_tslice_eq hadd (le_of_lt hz)
  have ht' : Work.Spaces.pth (PsiTot α Φs W Φg) z θ
      = Work.Spaces.pth (PsiStar α Φs) z θ + Work.Spaces.pth (PsiEll α W Φg) z θ := by
    simp only [Work.Spaces.pth, ht,
      show (fun θ' => PsiStar α Φs z θ' + PsiEll α W Φg z θ')
        = (fun θ' => PsiStar α Φs z θ') + (fun θ' => PsiEll α W Φg z θ') from rfl,
      deriv_add hstar.2 hell.2]
  simp only [Work.Construction.Vop, hv, ht']
  ring

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
