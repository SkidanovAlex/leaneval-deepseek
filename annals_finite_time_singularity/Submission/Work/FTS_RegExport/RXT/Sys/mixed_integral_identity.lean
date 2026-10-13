import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Sys.miiSteps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.mixed_integral_identity` — S5a of the RX-St1 leaf plan

The integrated identity for the six components `w_k = D_z^{j}D_θ^{i}(slice g τ)`, `(j,i) = idx k`:

  `w_k(τ₂) − w_k(τ₁) = ∫_{τ₁}^{τ₂} (D^β ∂_τ g)(σ) dσ`

The base case `(0,0)` is the fundamental theorem of calculus in `τ` and each step differentiates
the identity for the lower slot in `z` (resp. `θ`) along a difference-quotient sequence, passing to
the limit with the dominated convergence theorem.  The six leaves are assembled from `mii_P_00`,
`mii_step_z` and `mii_step_theta` (`Submission/Work/FTS_RegExport/RXT/Sys/miiSteps.lean`) using the
index list `idx = ![(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mixed_integral_identity {S α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hG : Work.FTS.RegExportIface.RXT.GdotLoc S g) :
    ∀ k : Fin 6, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.slice g τ₂) z θ
        - Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.slice g τ₁) z θ
      = ∫ σ in τ₁..τ₂, Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ := by
  -- the three inputs read off the hypothesis bundle
  have hc4 : ∀ τ, 0 ≤ τ →
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0 :=
    fun τ hτ => hOK.1.1.c4 τ hτ
  have hcontτ : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => g z θ τ) (Set.Ici 0) :=
    fun z θ h => hOK.1.1.cont z θ h
  have hderivg : ∀ z θ σ, 0 < σ → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s) (Work.FTS.Galerkin.gdot g σ z θ) σ := by
    intro z θ σ hσ hQd
    exact (hSol.2 z θ σ (le_of_lt hσ) hQd).hasDerivAt (Ici_mem_nhds hσ)
      |>.differentiableAt.hasDerivAt
  -- the six leaves, by induction on the total order
  have h00 : mii_P S g 0 0 := mii_P_00 hcontτ hderivg (mii_R_00 hG)
  have h10 : mii_P S g 1 0 := mii_step_z hG hc4 (j := 0) (i := 0) (by omega) h00 (mii_R_00 hG)
  have h01 : mii_P S g 0 1 := mii_step_theta hG hc4 (i := 0) (by omega) h00 (mii_R_00 hG)
  have h20 : mii_P S g 2 0 := mii_step_z hG hc4 (j := 1) (i := 0) (by omega) h10 (mii_R_10 hG)
  have h11 : mii_P S g 1 1 := mii_step_z hG hc4 (j := 0) (i := 1) (by omega) h01 (mii_R_01 hG)
  have h02 : mii_P S g 0 2 := mii_step_theta hG hc4 (i := 1) (by omega) h01 (mii_R_01 hG)
  intro k
  fin_cases k
  · exact h00
  · exact h10
  · exact h01
  · exact h20
  · exact h11
  · exact h02

end Work.FTS_RegExport.RXT.Sys
