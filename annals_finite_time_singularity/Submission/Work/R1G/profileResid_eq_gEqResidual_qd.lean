import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.R1G.Defs
import Submission.Work.R1G.vorticity_psiField_bslOp
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Stability.L12Add
import Submission.Work.Stability.PthFstarAdd
import Submission.Work.Stability.PzFstarAdd
import Submission.Work.Stability.ThetaPzFtot
-- ===== merged: Submission.Work.R1G.Meridian =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G

variable {α : NNReal}


end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.gDerivDataQd_phi_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `GDerivDataQd` for the stationary zero-stream-function data of a `ProfileData`

The restricted derivation bundle `Work.R1G.GDerivDataQd` is *derivable from `ProfileData`*: at the
stationary perturbation `g = gOf3 P` and the *zero* stream function `φ = phiOf3 0` all seven fields
are theorems.  The two that carry analytic content are

* `h5` (`z ∂_z Θ = -(1/(4α)) sin(2θ)(F,K)`) — the Construction area's `Dz_Theta_eq`, whose
  hypotheses are integrability of the `L₁₂`-density of the *full* profile `F_* + P.g` on `(0,∞)`
  and its continuity at `z > 0`;
* `hL` (`L₁₂(F_* + g) = L₁₂(F_*) + L₁₂(g)` for `z ≥ 0`) — the additivity of the tail integral,
  which needs the integrability of both densities on `(z,∞)`.  This is precisely the place where
  the restriction `z ≥ 0` of `GDerivDataQd` (as opposed to `GDerivData`'s all-`z` version) is
  needed: for `z ≥ 0` the integration range misses the pole of `L12dens (F_*)` at `s = -1`, and
  `HkMem (profExp α) 2 P.g` makes the density of the perturbation integrable
  (`Work.Coercivity.L12dens_integrableOn`).

Everything else is bookkeeping: `h2`/`h3` are the *definitional* decomposition
`Φ = Φ̃ + Θ` at `Φ = 0` (`PhiTil α F 0 = -Theta α F`), `h6` is `pth_Theta_eq`, and `hDz`/`hpth` are
the additivity of `∂_z` resp. `∂_θ` over `F = F_* + g`, which holds on the open quadrant because
`P.g` is smooth on a neighbourhood of the closed quadrant.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.R1G

/-! ## Integrability of the angular slices -/

/-- The angular slice `θ ↦ K(θ)·P.g(s,θ)/s` of the perturbation is integrable on `Iθ` for `s > 0`:
it is continuous there by the `SmoothNbhd`-smoothness of `P.g` and the compactness of `Iθ`. -/
theorem integrableOn_slice_g {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * P.g s θ / s) Work.Spaces.Iθ := by
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.K; fun_prop
  have hslice : ContinuousOn (fun θ => P.g s θ) Work.Spaces.Iθ :=
    Work.Elliptic.continuousOn_slice_theta_Iθ P.g P.hsmooth
      (by simp only [Set.mem_Ioi]; linarith)
  exact ((hK.mul hslice).div_const s).integrableOn_compact isCompact_Icc


/-! ## The `L₁₂`-density of the full profile -/


/-! ## Additivity of `L₁₂` over `F = F_* + g` -/


/-! ## Differentiability of the slices of the perturbation on the quadrant -/


/-! ## The derivation bundle at the stationary data with zero stream function -/


end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.meridianResid_cut_ssVort_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.R1G

/-! ## Derivatives of `ρ^p/c` in the radial variable -/

/-- The radial counterpart of `Work.Cyl.hasDerivAt_rhoP_rpow_div_snd`:
`r' ↦ ρ(r',z)^p/c` has derivative `p·(ρ^p/c)·(r/ρ²)` at `r > 0`. -/
lemma hasDerivAt_rhoP_rpow_div_fst (r z p c : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / c)
      (p * (Work.Cyl.rhoP r z ^ p / c) * (r / Work.Cyl.rhoP r z ^ 2)) r := by
  have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  have hρp : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p)
      (p * Work.Cyl.rhoP r z ^ p * (r / Work.Cyl.rhoP r z ^ 2)) r := by
    have h := (Real.hasDerivAt_rpow_const (x := Work.Cyl.rhoP r z) (p := p) (Or.inl hne)).comp r
      (hasDerivAt_rhoP_fst' r z hr)
    have hfun : ((fun x : ℝ => x ^ p) ∘ fun r' => Work.Cyl.rhoP r' z)
        = fun r' => Work.Cyl.rhoP r' z ^ p := by funext x; rfl
    rw [hfun] at h
    convert h using 1
    rw [Real.rpow_sub_one hne]
    field_simp
  have h := hρp.div_const c
  convert h using 1
  ring

/-- The radial counterpart of `Work.Cyl.hasDerivAt_thetaP_snd`:
`r' ↦ θ(r',z) = arctan(z/r')` has derivative `-z/ρ²` at `r > 0`. -/
lemma hasDerivAt_thetaP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r := by
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => Work.Cyl.thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [Work.Cyl.thetaP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-! ## Differentiability of the self-similar vorticity -/




/-! ## The residual identity for the cut self-similar pair -/


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.profileResid_eq_gEqResidual_qd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

open Work.Construction Work.Coercivity Work.Spaces


end Work.R1G
end
