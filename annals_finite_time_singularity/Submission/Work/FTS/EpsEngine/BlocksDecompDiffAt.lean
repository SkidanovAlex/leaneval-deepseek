import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.StreamDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `θ`-slices of `Theta α (Fstar α)` are differentiable.**  `Theta α F z θ'` is
`((1/(4α))·L₁₂(F)(z))·sin(2θ')`, i.e. a constant multiple of `sin(2θ')`. -/
theorem differentiableAt_tslice_Theta_Fstar {α z θ : ℝ} :
    DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α) z θ') θ := by
  have hsin : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id θ).const_mul (2 : ℝ)).sin
    simpa only [Work.Construction.s2] using h.differentiableAt
  have h := hsin.const_mul
    ((1 / (4 * α)) * Work.Construction.L12 (Work.Construction.Fstar α) z)
  have heq : (fun θ' => ((1 / (4 * α)) * Work.Construction.L12 (Work.Construction.Fstar α) z)
        * Work.Construction.s2 θ')
      = fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α) z θ' := by
    funext θ'
    simp only [Work.Construction.Theta]
    ring
  rwa [heq] at h

/-- **The `z`-slices of `Theta α (Fstar α)` are differentiable.**  `Theta α F z' θ` is
`((1/(4α))·sin(2θ))·L₁₂(F)(z')`, and `L₁₂(F_*) = 2α/(1+z)` on `(0,∞)`. -/
theorem differentiableAt_zslice_Theta_Fstar {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hz : 0 < z) :
    DifferentiableAt ℝ
      (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α) z' θ) z := by
  have hL : DifferentiableAt ℝ
      (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSAux.differentiableAt_L12_Fstar hα hα1 hz
  have h := hL.const_mul ((1 / (4 * α)) * Work.Construction.s2 θ)
  have heq : (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) z')
      = fun z' => Work.Construction.Theta α (Work.Construction.Fstar α) z' θ := by
    funext z'
    simp only [Work.Construction.Theta]
  rwa [heq] at h

/-- **The differentiability hypotheses of the three block decompositions, from open-quadrant smoothness.**  At a point `(z,θ)` of the open quadrant, the eight slice-differentiability inputs of the block decompositions of `Work.FTS.EpsEngine.RopBlockDecomp` / `UopSlot` / `VopSlot` (the z-slices and θ-slices of `PhiTil α f (E f)`, `Φs`, `PhiTil α F_* Φs` and `Theta α F_*`) follow from `SmoothOpen f` + `HkMem α 4 f` (which give `C³`, hence differentiability, of `L₁₂ f` on `(0,∞)`), `SmoothOpen (E f)`, `SmoothOpen Φs` and the explicit `smoothOpen_Theta_Fstar`. -/
theorem BlocksDecompDiffAt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f Φs : ℝ → ℝ → ℝ} {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen (E f))
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    (DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α f (E f) z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Φs z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
       Φs z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α)
       z' θ) z ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α f (E f) z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Φs z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
       Φs z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α)
       z θ') θ) := by
  -- the `L₁₂` differentiability input for the datum `f`
  have hLf : DifferentiableAt ℝ (fun z' => Work.Construction.L12 f z') z :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSAux.differentiableAt_L12_of_smoothOpen hα hα1 hf hmem hz
  -- the `z`- and `θ`-slices of the elliptic stream function `E f`
  have hEz : DifferentiableAt ℝ (fun z' => E f z' θ) z :=
    Work.FTS.StrongEps.EComparison.differentiableAt_zslice hEf hz hθ0 hθ1
  have hEt : DifferentiableAt ℝ (fun θ' => E f z θ') θ :=
    Work.FTS.StrongEps.EComparison.differentiableAt_tslice hEf hz hθ0 hθ1
  -- conjuncts 1 and 5: the slices of `PhiTil α f (E f)`
  have h15 := Work.FTS.StrongEps.EpsRLX.ProfRHSAux.differentiableAt_PhiTil
    (α := α) (F := f) (Ψ := E f) hEz hEt hLf
  -- conjuncts 2 and 6: the slices of `Φs`
  have h2 : DifferentiableAt ℝ (fun z' => Φs z' θ) z :=
    Work.FTS.StrongEps.EComparison.differentiableAt_zslice hΦs hz hθ0 hθ1
  have h6 : DifferentiableAt ℝ (fun θ' => Φs z θ') θ :=
    Work.FTS.StrongEps.EComparison.differentiableAt_tslice hΦs hz hθ0 hθ1
  -- conjuncts 3 and 7: the slices of `PhiTil α F_* Φs`
  have h37 := Work.FTS.StrongEps.EpsRLX.ProfRHSAux.PsiStar_diff hα hα1 hΦs hz hθ0 hθ1
  -- conjuncts 4 and 8: the slices of `Theta α F_*`
  have h4 : DifferentiableAt ℝ
      (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α) z' θ) z :=
    differentiableAt_zslice_Theta_Fstar hα hα1 hz
  have h8 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α) z θ') θ :=
    differentiableAt_tslice_Theta_Fstar
  exact ⟨h15.1, h2, h37.1, h4, h15.2, h6, h37.2, h8⟩

end Work.FTS.EpsEngine
