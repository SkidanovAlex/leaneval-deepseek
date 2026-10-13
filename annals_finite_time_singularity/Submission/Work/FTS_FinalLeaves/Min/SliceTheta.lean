import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Stability.PzFstarAdd
import Submission.Work.Stability.PthFstarAdd
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.Min

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Slice differentiability from `ContDiffOn ℝ 4` on the open quadrant -/

/-- A function whose uncurried form is `C⁴` on the open quadrant has `z`-differentiable slices
at every point of the open quadrant. -/
theorem differentiableAt_slice_z_of_contDiffOn {h : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun z' => h z' θ) z := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 4 (Function.uncurry h) (z, θ) :=
    hC.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
  have hfun : (fun z' : ℝ => h z' θ)
      = (Function.uncurry h ∘ fun z' : ℝ => (z', θ)) := by
    funext z'; rfl
  rw [hfun]
  exact (hcd.differentiableAt (by norm_num)).comp z (by fun_prop)

/-- A function whose uncurried form is `C⁴` on the open quadrant has `θ`-differentiable slices
at every point of the open quadrant. -/
theorem differentiableAt_slice_theta_of_contDiffOn {h : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun θ' => h z θ') θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 4 (Function.uncurry h) (z, θ) :=
    hC.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
  have hfun : (fun θ' : ℝ => h z θ')
      = (Function.uncurry h ∘ fun θ' : ℝ => (z, θ')) := by
    funext θ'; rfl
  rw [hfun]
  exact (hcd.differentiableAt (by norm_num)).comp θ (by fun_prop)

/-- `Ftau α g τ = F_* α + slice g τ`, as functions. -/
theorem Ftau_eq_Fstar_add_slice (α : ℝ) (g : Work.FTS.Galerkin.Fam) (τ : ℝ) :
    Work.Construction.Ftau α g τ
      = (fun z θ => Work.Construction.Fstar α z θ + Work.FTS.Galerkin.slice g τ z θ) := by
  funext z θ
  rfl

/-- **The `D_z`/`∂_θ` splitting of `F_τ = F_* + g(τ)` from `C⁴`-regularity of the slice.**

This is `Work.FTS.MeridianDyn.Bridge.Pieces.Dzg_pthg_split` with the strong hypothesis `RegPkg`
(joint `C^∞`) replaced by the slice's `C⁴`-regularity on the open quadrant, which is exactly the
spatial clause of `RegPkgMin`. -/
theorem Dzg_pthg_split_c4 {α : ℝ} {g : Work.FTS.Galerkin.Fam} {τ : ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ
          = Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            + Work.Spaces.Dz (Work.FTS.Galerkin.slice g τ) z θ) ∧
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
          = Work.Spaces.pth (Work.Construction.Fstar α) z θ
            + Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ) := by
  constructor
  · intro z θ hQd
    obtain ⟨hz, hθ⟩ := hQd
    have hz0 : 0 < z := hz
    have hF : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z :=
      Work.Stability.differentiableAt_Fstar_slice α θ z (by linarith)
    have hg : DifferentiableAt ℝ (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z :=
      differentiableAt_slice_z_of_contDiffOn hC hz hθ
    have hft : (fun z' => Work.Construction.Ftau α g τ z' θ)
        = (fun z' => Work.Construction.Fstar α z' θ)
          + (fun z' => Work.FTS.Galerkin.slice g τ z' θ) := by
      funext z'; rfl
    show z * deriv (fun z' => Work.Construction.Ftau α g τ z' θ) z
        = z * deriv (fun z' => Work.Construction.Fstar α z' θ) z
          + z * deriv (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z
    rw [hft, deriv_add hF hg]
    ring
  · intro z θ hQd
    obtain ⟨hz, hθ⟩ := hQd
    have hF : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
      Work.Stability.differentiableAt_Fstar_slice_theta α z θ hθ
    have hg : DifferentiableAt ℝ (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ :=
      differentiableAt_slice_theta_of_contDiffOn hC hz hθ
    have hft : (fun θ' => Work.Construction.Ftau α g τ z θ')
        = (fun θ' => Work.Construction.Fstar α z θ')
          + (fun θ' => Work.FTS.Galerkin.slice g τ z θ') := by
      funext θ'; rfl
    show deriv (fun θ' => Work.Construction.Ftau α g τ z θ') θ
        = deriv (fun θ' => Work.Construction.Fstar α z θ') θ
          + deriv (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ
    rw [hft, deriv_add hF hg]

/-! ## The derivatives of the singular part `Θ`, with no hypothesis on `α` -/

/-- `∂_θ Θ = (1/(2α))·cos(2θ)·L₁₂(F)`, for **every** real `α` (`α = 0`: both sides vanish).
This is `Work.Construction.pth_Theta_eq` without its `0 < α` hypothesis. -/
theorem pth_Theta_eq_any {α : ℝ} {F : ℝ → ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pth (Work.Construction.Theta α F) z θ
      = (1 / (2 * α)) * Real.cos (2 * θ) * Work.Construction.L12 F z := by
  rcases eq_or_ne α 0 with rfl | hα
  · have h0 : Work.Construction.Theta 0 F = fun _ _ => (0 : ℝ) := by
      funext z θ; simp [Work.Construction.Theta]
    rw [h0]
    simp [Work.Spaces.pth]
  · have hfun : Work.Construction.Theta α F
        = fun z θ => Work.Construction.L12 F z * ((1 / (4 * α)) * Real.sin (2 * θ)) := by
      funext z θ
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    rw [hfun, Work.Construction.pth_mul_radial]
    have hsin : deriv (fun t : ℝ => (1 / (4 * α)) * Real.sin (2 * t)) θ
        = (1 / (4 * α)) * (2 * Real.cos (2 * θ)) := by
      rw [deriv_const_mul_field (v := fun s : ℝ => Real.sin (2 * s)) (u := (1 / (4 * α))),
        Work.Construction.deriv_sin_two]
    rw [hsin]
    first | (field_simp; ring) | field_simp | ring

/-- `z∂_z Θ = -(1/(4α))·sin(2θ)·(F,K)`, for **every** real `α` (`α = 0`: both sides vanish).
This is `Work.Construction.Dz_Theta_eq` without its `0 < α` hypothesis. -/
theorem Dz_Theta_eq_any {α z θ : ℝ} {F : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens F) z) (hz : 0 < z) :
    Work.Spaces.Dz (Work.Construction.Theta α F) z θ
      = -(1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.FK F z := by
  rcases eq_or_ne α 0 with rfl | _hα
  · have h0 : Work.Construction.Theta 0 F = fun _ _ => (0 : ℝ) := by
      funext z θ; simp [Work.Construction.Theta]
    rw [h0]
    simp [Work.Spaces.Dz, Work.Spaces.pz]
  · have hder : HasDerivAt (fun r : ℝ => Work.Construction.L12 F r)
        (-(Work.Construction.L12dens F z)) z :=
      Work.FM.hasDerivAt_L12 hint hcont (by linarith)
    have hfun : Work.Construction.Theta α F
        = fun z θ => Work.Construction.L12 F z * ((1 / (4 * α)) * Work.Construction.s2 θ) := by
      funext z θ; rw [Work.Construction.Theta]; ring
    have hpz : Work.Spaces.pz (Work.Construction.Theta α F) z θ
        = -(Work.Construction.L12dens F z) * ((1 / (4 * α)) * Work.Construction.s2 θ) := by
      rw [hfun, Work.Construction.pz_mul_radial, hder.deriv]
    rw [Work.Spaces.Dz, hpz,
      show z * (-(Work.Construction.L12dens F z) * ((1 / (4 * α)) * Work.Construction.s2 θ))
        = -(1 / (4 * α)) * Work.Construction.s2 θ
            * (z * Work.Construction.L12dens F z) by ring,
      Work.Construction.mul_L12dens_eq_FK (ne_of_gt hz)]

/-- The `z`-slice of `Θ α F` is differentiable whenever `L₁₂ F` is, for every real `α`. -/
theorem differentiableAt_Theta_slice_z {α z θ : ℝ} {F : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens F) z) (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Theta α F z' θ) z := by
  rcases eq_or_ne α 0 with rfl | _hα
  · have h0 : Work.Construction.Theta 0 F = fun _ _ => (0 : ℝ) := by
      funext z θ; simp [Work.Construction.Theta]
    rw [h0]
    exact differentiableAt_const 0
  · have hder : HasDerivAt (fun r : ℝ => Work.Construction.L12 F r)
        (-(Work.Construction.L12dens F z)) z :=
      Work.FM.hasDerivAt_L12 hint hcont (by linarith)
    have hfun : Work.Construction.Theta α F
        = fun z θ => Work.Construction.L12 F z * ((1 / (4 * α)) * Work.Construction.s2 θ) := by
      funext z θ; rw [Work.Construction.Theta]; ring
    rw [hfun]
    exact (hder.mul_const ((1 / (4 * α)) * Work.Construction.s2 θ)).differentiableAt

/-- The `θ`-slice of `Θ α F` is differentiable everywhere, for every real `α`. -/
theorem differentiableAt_Theta_slice_theta {α z θ : ℝ} {F : ℝ → ℝ → ℝ} :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α F z θ') θ := by
  have hfun : (fun θ' => Work.Construction.Theta α F z θ')
      = fun θ' => ((1 / (4 * α)) * Work.Construction.L12 F z) * Work.Construction.s2 θ' := by
    funext θ'; rw [Work.Construction.Theta]; ring
  rw [hfun]
  have hs : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    show DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ
    fun_prop
  exact hs.const_mul _

end Work.FTS_FinalLeaves.Min
