/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ProfRHSAux/StreamDefs` — the three stream functions and their slices

The total stream function `Φ̃ = PhiTil α (Ftot α W) (Φs + Φg)`, its star part
`PhiTil α (Fstar α) Φs` and its elliptic part `PhiTil α W Φg`, together with the
differentiability of their slices (from `L₁₂(F_*) = 2α/(1+z)`, `L₁₂(W) ∈ C¹` via
`hasDerivAt_L12_C4`, and the smoothness of `Φs, Φg`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Extract
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.OpAdd
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.L12Add
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSliceAux
import Submission.Work.FTS_RegExport.RXT.STC.hasDerivAt_L12_C4
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd

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

/-! ## The three stream functions, and their slices -/

/-- The stream function `Φ̃ = PhiTil α (F_* + W) (Φs + Φg)` of the full profile. -/
abbrev PsiTot (α : ℝ) (Φs W Φg : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.PhiTil α (Work.Construction.Ftot α W) (fun z θ => Φs z θ + Φg z θ)

/-- The star stream function `Φ̃_* = PhiTil α F_* Φs`. -/
abbrev PsiStar (α : ℝ) (Φs : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs

/-- The elliptic stream function `Φ̃_ell = PhiTil α W Φg`. -/
abbrev PsiEll (α : ℝ) (W Φg : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.PhiTil α W Φg

/-- `deriv` only depends on a neighbourhood: if `g =ᶠ[𝓝 z] g'` and `g'` is differentiable at `z`,
then the derivatives agree. -/
theorem deriv_eq_of_eventuallyEq {g g' : ℝ → ℝ} {z : ℝ} (h : g =ᶠ[𝓝 z] g')
    (hg' : DifferentiableAt ℝ g' z) : deriv g z = deriv g' z :=
  ((h.hasDerivAt_iff).mpr hg'.hasDerivAt).deriv

/-- `L₁₂(F_*)` is differentiable on `(0,∞)` (it is `2α/(1+z)` there). -/
theorem differentiableAt_L12_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z := by
  have hev : (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z')
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * α / (1 + z') := by
    filter_upwards [Ici_mem_nhds_of_pos hz] with z' hz'
    exact Work.Construction.L12_Fstar_eq hα hα1 hz'
  have hd : DifferentiableAt ℝ (fun z' : ℝ => 2 * α / (1 + z')) z := by
    have h1 : (1 : ℝ) + z ≠ 0 := by linarith
    fun_prop
  exact (hev.hasDerivAt_iff.mpr hd.hasDerivAt).differentiableAt

/-- `L₁₂(W)` is differentiable on `(0,∞)` for `W ∈ C^4(Q0) ∩ ℋ⁴`
(`Work.FTS_RegExport.RXT.STC.hasDerivAt_L12_C4`). -/
theorem differentiableAt_L12_of_smoothOpen {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {W : ℝ → ℝ → ℝ} (hWs : Work.FTS.EllipticEst.SmoothOpen W)
    (hWm : Work.Spaces.HkMem α 4 W) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 W z') z :=
  (Work.FTS_RegExport.RXT.STC.hasDerivAt_L12_C4 hα hα1
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall W).mp hWs 4) hWm hz).differentiableAt

/-- `PhiTil α F Ψ` has differentiable slices as soon as `Ψ` does and `L₁₂(F)` is
differentiable in `z`. -/
theorem differentiableAt_PhiTil {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hΨz : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (hΨt : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ)
    (hF : DifferentiableAt ℝ (fun z' => Work.Construction.L12 F z') z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α F Ψ z' θ) z ∧
    DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α F Ψ z θ') θ := by
  constructor
  · have h2 : DifferentiableAt ℝ (fun z' : ℝ =>
        ((1 / (4 * α)) * Work.Construction.s2 θ) * Work.Construction.L12 F z') z :=
      hF.const_mul _
    have heq : (fun z' => Work.Construction.PhiTil α F Ψ z' θ)
        = fun z' : ℝ => Ψ z' θ
          - ((1 / (4 * α)) * Work.Construction.s2 θ) * Work.Construction.L12 F z' := by
      funext z'
      simp only [Work.Construction.PhiTil, Work.Construction.Theta] <;> ring
    rw [heq]
    exact hΨz.sub h2
  · have h2 : DifferentiableAt ℝ (fun θ' : ℝ =>
        ((1 / (4 * α)) * Work.Construction.L12 F z) * Work.Construction.s2 θ') θ :=
      (by have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
            simpa only [id_eq, mul_one] using ((hasDerivAt_id θ).const_mul (2 : ℝ)).sin
          simpa only [Work.Construction.s2] using h.differentiableAt :
        DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ).const_mul _
    have heq : (fun θ' => Work.Construction.PhiTil α F Ψ z θ')
        = fun θ' : ℝ => Ψ z θ'
          - ((1 / (4 * α)) * Work.Construction.L12 F z) * Work.Construction.s2 θ' := by
      funext θ'
      simp only [Work.Construction.PhiTil, Work.Construction.Theta] <;> ring
    rw [heq]
    exact hΨt.sub h2

/-- The `z`- and `θ`-slices of the star stream function are differentiable. -/
theorem PsiStar_diff {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => PsiStar α Φs z' θ) z ∧
    DifferentiableAt ℝ (fun θ' => PsiStar α Φs z θ') θ :=
  differentiableAt_PhiTil
    (Work.FTS.StrongEps.EComparison.differentiableAt_zslice hΦs hz hθ0 hθ1)
    (Work.FTS.StrongEps.EComparison.differentiableAt_tslice hΦs hz hθ0 hθ1)
    (differentiableAt_L12_Fstar hα hα1 hz)

/-- The `z`- and `θ`-slices of the elliptic stream function are differentiable. -/
theorem PsiEll_diff {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W Φg : ℝ → ℝ → ℝ}
    (hWs : Work.FTS.EllipticEst.SmoothOpen W) (hWm : Work.Spaces.HkMem α 4 W)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => PsiEll α W Φg z' θ) z ∧
    DifferentiableAt ℝ (fun θ' => PsiEll α W Φg z θ') θ :=
  differentiableAt_PhiTil
    (Work.FTS.StrongEps.EComparison.differentiableAt_zslice hΦg hz hθ0 hθ1)
    (Work.FTS.StrongEps.EComparison.differentiableAt_tslice hΦg hz hθ0 hθ1)
    (differentiableAt_L12_of_smoothOpen hα hα1 hWs hWm hz)

/-! ## The value and slice identities for the total stream function -/

/-- The value of the total stream function is the sum of the star and elliptic values. -/
theorem PsiTot_value_eq {α : ℝ} {Φs W Φg : ℝ → ℝ → ℝ}
    (hadd : ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z)
    {z θ : ℝ} (hz : 0 ≤ z) :
    PsiTot α Φs W Φg z θ = PsiStar α Φs z θ + PsiEll α W Φg z θ := by
  simp only [PsiTot, PsiStar, PsiEll, Work.Construction.PhiTil, Work.Construction.Theta]
  rw [hadd z hz]
  ring

/-- The `θ`-slices of the total stream function are the sums of the `θ`-slices (as functions,
for fixed `z ≥ 0`). -/
theorem PsiTot_tslice_eq {α : ℝ} {Φs W Φg : ℝ → ℝ → ℝ}
    (hadd : ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z)
    {z : ℝ} (hz : 0 ≤ z) :
    (fun θ => PsiTot α Φs W Φg z θ)
      = fun θ => PsiStar α Φs z θ + PsiEll α W Φg z θ := by
  funext θ
  exact PsiTot_value_eq hadd hz

/-- The `z`-slices of the total stream function agree, near `z`, with the sum of the star and
elliptic `z`-slices. -/
theorem PsiTot_zslice_eventuallyEq {α : ℝ} {Φs W Φg : ℝ → ℝ → ℝ}
    (hadd : ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z)
    {z θ : ℝ} (hz : 0 < z) :
    (fun z' => PsiTot α Φs W Φg z' θ)
      =ᶠ[𝓝 z] fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ := by
  filter_upwards [Ici_mem_nhds_of_pos hz] with z' hz'
  exact PsiTot_value_eq hadd hz'

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
