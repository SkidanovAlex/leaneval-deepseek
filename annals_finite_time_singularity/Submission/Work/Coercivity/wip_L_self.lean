import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.sliceEtaAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Continuity of the angular slices -/

/-- The open neighbourhood of the closed quadrant on which `Spaces.SmoothNbhd` demands
smoothness. -/
theorem eta_box_open : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) :=
  isOpen_Ioi.prod isOpen_Ioo

/-- For `z > 0` the segment `{z} × Iθ` lies in the box of `Spaces.SmoothNbhd`. -/
theorem eta_box_mapsTo {z : ℝ} (hz : 0 < z) :
    Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
  intro θ hθ
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_Ioi]; linarith
  · simp only [Set.mem_Ioo]
    exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

/-- The angular slice `θ ↦ g z θ` of a `SmoothNbhd` function is continuous on `Iθ`. -/
theorem slice_continuousOn (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) : ContinuousOn (fun θ => g z θ) Work.Spaces.Iθ := by
  have h := hg.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) (eta_box_mapsTo hz)
  show ContinuousOn (fun θ => Function.uncurry g (z, θ)) Work.Spaces.Iθ
  exact h

/-- The angular slice `θ ↦ ∂_θ g z θ` of a `SmoothNbhd` function is continuous on `Iθ`. -/
theorem slice_pth_continuousOn (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) : ContinuousOn (fun θ => Work.Spaces.pth g z θ) Work.Spaces.Iθ := by
  have hpth : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pth g))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) :=
    Work.Spaces.contDiffOn_uncurry_pth eta_box_open hg
  have h := hpth.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) (eta_box_mapsTo hz)
  show ContinuousOn (fun θ => Function.uncurry (Work.Spaces.pth g) (z, θ)) Work.Spaces.Iθ
  exact h

/-! ## The primitive `ψ` of the `η`-weighted integration by parts -/

/-- The boundary term `ψ(θ) = sin(2θ)^{1-η} g(z,θ)²` of the weighted integration by parts. -/
def etaPsi (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) * (g z θ) ^ 2

/-- The left-hand integrand `D_θ g · g · sin(2θ)^{-η}` of `slice_ibp_eta`. -/
def etaPsiG (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  Work.Spaces.Dth g z θ * g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)

/-- The right-hand integrand `cos(2θ) · g² · sin(2θ)^{-η}` of `slice_ibp_eta`. -/
def etaPsiH (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  Real.cos (2 * θ) * (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)

/-- The derivative `ψ' = 2·etaPsiG - 2(η-1)·etaPsiH` of the boundary term `ψ`. -/
def etaPsi' (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  2 * etaPsiG g z θ - 2 * (Work.Spaces.eta - 1) * etaPsiH g z θ

/-- `ψ` vanishes at both endpoints of `Iθ`. -/
theorem etaPsi_zero (g : ℝ → ℝ → ℝ) (z : ℝ) :
    etaPsi g z 0 = 0 ∧ etaPsi g z (π / 2) = 0 := by
  have hexp : (1 : ℝ) - Work.Spaces.eta ≠ 0 := by
    have := Work.Spaces.eta_lt_one
    intro h; linarith
  constructor
  · simp only [etaPsi, mul_zero, Real.sin_zero]
    rw [Real.zero_rpow hexp]; ring
  · have hsin : Real.sin (2 * (π / 2)) = 0 := by
      rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    simp only [etaPsi, hsin]
    rw [Real.zero_rpow hexp]; ring

/-- `ψ` is continuous on `Iθ`. -/
theorem etaPsi_continuousOn (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) : ContinuousOn (fun θ => etaPsi g z θ) Work.Spaces.Iθ := by
  have hexp : (0 : ℝ) ≤ 1 - Work.Spaces.eta := by
    have := Work.Spaces.eta_lt_one
    linarith
  have hw : Continuous (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)) :=
    (Real.continuous_rpow_const hexp).comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hsq : ContinuousOn (fun θ => (g z θ) ^ 2) Work.Spaces.Iθ :=
    (slice_continuousOn g hg hz).pow 2
  have h := hw.continuousOn.mul hsq
  exact h

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.wip_L_self =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false






end Work.Coercivity
end
end
