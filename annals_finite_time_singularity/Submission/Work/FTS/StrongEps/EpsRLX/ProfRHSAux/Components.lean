/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ProfRHSAux/Components` — the vanishing of the summands of `profRHS`

At a fixed `z > 0` and along one of the two angular endpoint filters (`θ → 0⁺` or
`θ → (π/2)⁻`) the profile right-hand side

  `profRHS α Φs E W = -𝓛_Γ^T W + gRHS α μ λ (F_* + W) (Φs + E W) W`

is a sum of terms each of which factors as (vanishing function)·(bounded function).  This module
proves the vanishing of each summand: the linear part `𝓛_Γ^T W`, the projector term `AK`, and the
three pieces `N₀`, `N`, `N_*` of `gRHS` (the last modulo the pointwise bounds of
`ProfRHSAux/Bounds`, and the first two through the additivity of `D_θ`, `D_z` over
`F = F_* + W`).

The endpoint data is bundled in `TraceCtx`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.GamTraces
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.BdryTracesMixedTendsto
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.FstarDerivs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.mixed_add
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongEps.gRHS_tendsto

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

/-- **The endpoint data** for the trace argument at a fixed `z > 0`: the filter is one of the
two endpoint filters (so that eventually `0 < θ < π/2`), `Γ → 0`, `D_θΓ → 0`, and all the mixed
derivatives `D_z^bD_θ^a W` (`a + b ≤ 6`) vanish at the endpoint (from `BdryTraces α 6 W`). -/
structure TraceCtx (α : ℝ) (W : Fn) (l : Filter ℝ) (z : ℝ) : Prop where
  hz : 0 < z
  hquad : ∀ᶠ θ in l, θ ∈ Set.Ioo 0 (Real.pi / 2)
  gam : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ) l (𝓝 0)
  dth_gam : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) l (𝓝 0)
  slot : ∀ a b : ℕ, a + b ≤ 6 → Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed b a W z θ) l (𝓝 0)

/-! ## The traces of the profile `F_*` and of `F = F_* + W` -/

/-- `F_* → 0`: it is `Γ(θ)·(α φ(z)/c)`. -/
theorem tendsto_Fstar {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.Fstar α z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Construction.Fstar α z θ)
      = fun θ => Work.Spaces.Gam α θ * (α * Work.FM.Fstar z / Work.Spaces.c α) := by
    funext θ
    exact (FstarDerivs α z θ).1
  rw [hfun]
  simpa using hc.gam.mul_const _

/-- `D_θF_* → 0`: it is `D_θΓ(θ)·(α φ(z)/c)`. -/
theorem tendsto_Dth_Fstar {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      = fun θ => (α * Work.FM.Fstar z / Work.Spaces.c α)
          * (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) := by
    funext θ
    exact (FstarDerivs α z θ).2.2
  rw [hfun]
  simpa using hc.dth_gam.const_mul _

/-- `D_zF_* → 0`: it is `Γ(θ)·(α z ∂_zφ(z)/c)`. -/
theorem tendsto_Dz_Fstar {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      = fun θ => Work.Spaces.Gam α θ * (α * (z * deriv Work.FM.Fstar z) / Work.Spaces.c α) := by
    funext θ
    exact (FstarDerivs α z θ).2.1
  rw [hfun]
  simpa using hc.gam.mul_const _

/-- `F = F_* + W → 0`. -/
theorem tendsto_Ftot {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.Ftot α W z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Construction.Ftot α W z θ)
      = fun θ => Work.Construction.Fstar α z θ + Work.Spaces.mixed 0 0 W z θ := rfl
  rw [hfun]
  simpa using (tendsto_Fstar hc).add (hc.slot 0 0 (by norm_num))

/-- `D_θF → 0`, by additivity of `D_θ` over `F = F_* + W`. -/
theorem tendsto_Dth_Ftot {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W)
    {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dth (Work.Construction.Ftot α W) z θ) l (𝓝 0) := by
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hev : (fun θ : ℝ => Work.Spaces.Dth (Work.Construction.Ftot α W) z θ)
      =ᶠ[l] fun θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        + Work.Spaces.mixed 0 1 W z θ := by
    filter_upwards [hc.hquad] with θ hθ
    have h := Work.FTS.EllipticEst.SmoothOpen.mixed_add hFso hW.reg 0 1 z θ hc.hz hθ.1 hθ.2
    have h2 : Work.Spaces.mixed 0 1 (fun z θ => Work.Construction.Fstar α z θ + W z θ) z θ
        = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.mixed 0 1 W z θ := by
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
        using h
    rw [← h2]
    rfl
  simpa using Filter.Tendsto.congr' hev.symm
    ((tendsto_Dth_Fstar hc).add (hc.slot 1 0 (by norm_num)))

/-- `D_zF → 0`, by additivity of `D_z` over `F = F_* + W`. -/
theorem tendsto_Dz_Ftot {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W)
    {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz (Work.Construction.Ftot α W) z θ) l (𝓝 0) := by
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hev : (fun θ : ℝ => Work.Spaces.Dz (Work.Construction.Ftot α W) z θ)
      =ᶠ[l] fun θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + Work.Spaces.mixed 1 0 W z θ := by
    filter_upwards [hc.hquad] with θ hθ
    have h := Work.FTS.EllipticEst.SmoothOpen.mixed_add hFso hW.reg 1 0 z θ hc.hz hθ.1 hθ.2
    have h2 : Work.Spaces.mixed 1 0 (fun z θ => Work.Construction.Fstar α z θ + W z θ) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.mixed 1 0 W z θ := by
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        using h
    rw [← h2]
    rfl
  simpa using Filter.Tendsto.congr' hev.symm
    ((tendsto_Dz_Fstar hc).add (hc.slot 0 1 (by norm_num)))

/-- `L₁₂(F_*)(z) = 2α/(1+z)` for `z ≥ 0`. -/
theorem L12_Fstar_val {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
  Work.Construction.L12_Fstar_eq hα hα1 hz

/-! ## The linear part `𝓛_Γ^T W` -/

/-- **`𝓛_Γ^T W → 0`.**  Expanding `𝓛_Γ^T W = W + D_zW - 2W/(1+z) - (2zΓ/(c(1+z)²))L₁₂(W)
- 3D_θW/(1+z) + (Γ/c)(2z²/(1+z)³)L₁₂(3D_θW/(1+z))`, every summand carries either a mixed
derivative of `W` (which vanishes by `BdryTraces`) or the factor `Γ` (which vanishes). -/
theorem tendsto_LGammaT {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Coercivity.LGammaT α W z θ) l (𝓝 0) := by
  have hW0 : Filter.Tendsto (fun θ : ℝ => W z θ) l (𝓝 0) := by
    simpa using hc.slot 0 0 (by norm_num)
  have hWz : Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed 1 0 W z θ) l (𝓝 0) :=
    hc.slot 0 1 (by norm_num)
  have hWth : Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed 0 1 W z θ) l (𝓝 0) :=
    hc.slot 1 0 (by norm_num)
  have p1 : Filter.Tendsto (fun θ : ℝ => (W z θ + Work.Spaces.mixed 1 0 W z θ)
      + (-(2 * W z θ / (1 + z)))) l (𝓝 0) := by
    have h3 : Filter.Tendsto (fun θ : ℝ => -(2 * W z θ / (1 + z))) l (𝓝 0) := by
      simpa using ((hW0.const_mul 2).div_const (1 + z)).neg
    simpa using (hW0.add hWz).add h3
  have p2 : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ
      * (-(2 * z * Work.Construction.L12 W z / (Work.Spaces.c α * (1 + z) ^ 2)))) l (𝓝 0) := by
    simpa using hc.gam.mul_const (-(2 * z * Work.Construction.L12 W z
      / (Work.Spaces.c α * (1 + z) ^ 2)))
  have p3 : Filter.Tendsto (fun θ : ℝ => -(3 * Work.Spaces.mixed 0 1 W z θ / (1 + z)))
      l (𝓝 0) := by
    simpa using ((hWth.const_mul 3).div_const (1 + z)).neg
  have p4 : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ
      * ((2 * z ^ 2 / (1 + z) ^ 3)
          * Work.Construction.L12 (Work.Coercivity.Transport W) 0 / Work.Spaces.c α)) l (𝓝 0) := by
    simpa using hc.gam.mul_const ((2 * z ^ 2 / (1 + z) ^ 3)
      * Work.Construction.L12 (Work.Coercivity.Transport W) 0 / Work.Spaces.c α)
  have hsum : Filter.Tendsto (fun θ : ℝ =>
      ((W z θ + Work.Spaces.mixed 1 0 W z θ) + (-(2 * W z θ / (1 + z))))
      + Work.Spaces.Gam α θ * (-(2 * z * Work.Construction.L12 W z
          / (Work.Spaces.c α * (1 + z) ^ 2)))
      + (-(3 * Work.Spaces.mixed 0 1 W z θ / (1 + z)))
      + Work.Spaces.Gam α θ * ((2 * z ^ 2 / (1 + z) ^ 3)
          * Work.Construction.L12 (Work.Coercivity.Transport W) 0 / Work.Spaces.c α)) l (𝓝 0) := by
    simpa using ((p1.add p2).add p3).add p4
  refine Filter.Tendsto.congr (fun θ => ?_) hsum
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Coercivity.L12f,
    Work.Construction.L12, Work.Spaces.Dth, Work.Spaces.Dz, Work.Spaces.pz,
    Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, div_eq_mul_inv]
  ring

/-! ## The projector term `AK` -/

/-- **`AK α z θ → 0`**: it is `(Γ(θ)/c)·2z²/(1+z)³`. -/
theorem tendsto_AK {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.AK α z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Construction.AK α z θ)
      = fun θ => Work.Spaces.Gam α θ * (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) := by
    funext θ
    simp only [Work.Construction.AK]
    ring
  rw [hfun]
  simpa using hc.gam.mul_const _

/-! ## The linear-in-`g` term `N_*` -/

/-- **`N_*(μ,λ)(W) → 0`** for any constants `μ, λ`: it is `-μW - (μ+λ+μλ)D_zW`. -/
theorem tendsto_Nstar {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z)
    (mu lam : ℝ) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.Nstar mu lam W z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Construction.Nstar mu lam W z θ)
      = fun θ => (-mu) * W z θ - (mu + lam + mu * lam) * Work.Spaces.mixed 1 0 W z θ := by
    funext θ
    simp only [Work.Construction.Nstar, Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero, Work.Spaces.mixed_zero_right,
      Work.Spaces.mixed_zero_left]
  rw [hfun]
  have h1 : Filter.Tendsto (fun θ : ℝ => (-mu) * W z θ) l (𝓝 0) := by
    simpa using (show Filter.Tendsto (fun θ : ℝ => W z θ) l (𝓝 0) from by
      simpa using hc.slot 0 0 (by norm_num)).const_mul (-mu)
  have h2 : Filter.Tendsto (fun θ : ℝ => (mu + lam + mu * lam) * Work.Spaces.mixed 1 0 W z θ)
      l (𝓝 0) := by
    simpa using (hc.slot 0 1 (by norm_num)).const_mul (mu + lam + mu * lam)
  simpa using h1.sub h2

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
