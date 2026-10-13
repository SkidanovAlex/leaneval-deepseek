import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.RXT.weighted_system
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.zhmod_of
import Submission.Work.FTS.RegPkgGal.R3d.jet_g
import Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1JetP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs` — B6 of the O1 plan

The producer-level wrapper of the two `C1Jet`-regularity statements of the O1 restatement

  `DzG α g z θ τ = D_z g̃(z,θ,τ)`,   `DthG α g z θ τ = D_θ g̃(z,θ,τ)`,   `g̃ = gS α (tauExt g)`

from the *input bundle* of the construction (`Sol`, `DynOK'`, the datum `hdat` and the clock bound
`hμ`), rather than from the Γ-weighted system `WSys` directly:

* `Work.FTS_RegExport.RXT.weighted_system` produces, for every `S > 0`, a constant `K` with
  `WSys α S K g` (the six Γ-weighted slots of `RXT.idx` bounded by `K·ω`,
  `ω α z θ = z²Γ(θ)/(1+z)²`);
* then the four leaves of `THL/L` close the two `C1Jet`s:

  - **B1** `DzG_theta_mod` / **B2** `DthG_theta_mod`: the `θ`-moduli, uniform in `z ≥ 0` and in
    `τ ∈ [0,S]`;
  - **B3** `DzDthG_bound_zderiv`: the uniform value bounds, the continuity at `z = 0` and the
    `z`-derivatives with their bound;
  - **B4** `DzDthG_tau_mod`: the `τ`-moduli;
  - the `z`-moduli are produced from B3 by the engine `RXR5.zhmod_of` (Lipschitz on the open
    half-line + continuity at `0` + sup bound, interpolated into an `α`-modulus);
  - the three one-variable moduli plus the sup bound are upgraded to a joint `Jet` by
    `R3d.jet_of_bounded_holder`, and the `z`-derivative half of `C1Jet` is B3.

The constant `K` of `weighted_system` need not be nonnegative, so the leaves are applied to
`max K 0` (monotonicity in the constant, `ω ≥ 0`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

open Work.FTS_RegExport.THL (WSys DzG DthG)

set_option autoImplicit false

/-! ## Elementary helper -/

/-- Monotonicity of `Jet` in its constant. -/
private theorem jet_mono {α S N M : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Work.FTS.Regularity.Jet α S N h)
    (hNM : N ≤ M) : Work.FTS.Regularity.Jet α S M h := by
  obtain ⟨h0, hsup, hhol⟩ := H
  refine ⟨le_trans h0 hNM, fun z θ τ hz hθ hτ => le_trans (hsup z θ τ hz hθ hτ) hNM, ?_⟩
  intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
  refine le_trans (hhol z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ') ?_
  exact mul_le_mul_of_nonneg_right hNM
    (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'|) α)

/-! ## The assembly (B5), from the Γ-weighted system -/

private theorem c1jet_of_wsys {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S K : ℝ} (hS : 0 < S) (hK0 : 0 ≤ K) (hw : WSys α S K g) :
    ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂ (DzG α g) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃ (DthG α g) := by
  have hα1 : α ≤ 1 := by linarith
  have hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g := hOK.1.regPkgMin
  -- the four leaves
  obtain ⟨Lz, hLz0, hLz⟩ := DzG_theta_mod (g := g) hα hα13 hmin hS hK0 hw
  obtain ⟨Lt, hLt0, hLt⟩ := DthG_theta_mod (g := g) hα hα13 hmin hS hK0 hw
  obtain ⟨N, hN0, hB3⟩ := DzDthG_bound_zderiv (g := g) hα hα13 hmin hS hK0 hw
  obtain ⟨Lτ, hLτ0, hLτ⟩ := DzDthG_tau_mod (Φs := Φs) (E := E) (g := g) hα hα13 hOK hS
  have h2N0 : 0 ≤ max N (2 * N) := le_trans hN0 (le_max_left _ _)
  -- the two `z`-moduli, from B3 through the engine `zhmod_of`
  have hzdz : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |DzG α g z θ τ - DzG α g z' θ τ| ≤ max N (2 * N) * |z - z'| ^ α := by
    refine Work.FTS_RegExport.RXR5.zhmod_of (h := DzG α g) hα hα1 hN0 hN0 ?_ ?_ ?_ ?_
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, -⟩ := (hB3 τ hτ θ hθ).2.2.2 x hx |>.1
      exact hd.differentiableAt
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, hdb⟩ := (hB3 τ hτ θ hθ).2.2.2 x hx |>.1
      rw [hd.deriv]
      exact hdb
    · intro τ hτ θ hθ
      exact (hB3 τ hτ θ hθ).2.1
    · intro τ hτ θ hθ z hz
      exact ((hB3 τ hτ θ hθ).1 z hz).1
  have hzdth : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |DthG α g z θ τ - DthG α g z' θ τ| ≤ max N (2 * N) * |z - z'| ^ α := by
    refine Work.FTS_RegExport.RXR5.zhmod_of (h := DthG α g) hα hα1 hN0 hN0 ?_ ?_ ?_ ?_
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, -⟩ := (hB3 τ hτ θ hθ).2.2.2 x hx |>.2
      exact hd.differentiableAt
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, hdb⟩ := (hB3 τ hτ θ hθ).2.2.2 x hx |>.2
      rw [hd.deriv]
      exact hdb
    · intro τ hτ θ hθ
      exact (hB3 τ hτ θ hθ).2.2.1
    · intro τ hτ θ hθ z hz
      exact ((hB3 τ hτ θ hθ).1 z hz).2
  -- the joint `Jet`s
  obtain ⟨Nz, hNz⟩ := Work.FTS.RegPkgGal.R3d.jet_of_bounded_holder (h := DzG α g)
    hα hN0 h2N0 hLz0 hLτ0
    (fun τ hτ z θ hz hθ => ((hB3 τ hτ θ hθ).1 z hz).1)
    (fun τ hτ z z' hz hz' θ hθ => hzdz τ hτ θ hθ z z' hz hz')
    hLz
    (fun τ hτ τ' hτ' z hz θ hθ => (hLτ τ hτ τ' hτ' z hz θ hθ).1)
  obtain ⟨Nt, hNt⟩ := Work.FTS.RegPkgGal.R3d.jet_of_bounded_holder (h := DthG α g)
    hα hN0 h2N0 hLt0 hLτ0
    (fun τ hτ z θ hz hθ => ((hB3 τ hτ θ hθ).1 z hz).2)
    (fun τ hτ z z' hz hz' θ hθ => hzdth τ hτ θ hθ z z' hz hz')
    hLt
    (fun τ hτ τ' hτ' z hz θ hθ => (hLτ τ hτ τ' hτ' z hz θ hθ).2)
  -- the two `C1Jet`s, with the derivative half from B3
  refine ⟨max Nz N, max Nt N, le_trans hN0 (le_max_right _ _), le_trans hN0 (le_max_right _ _),
    ?_, ?_⟩
  · refine ⟨jet_mono hNz (le_max_left _ _), ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hdb⟩ := (hB3 τ hτ θ hθ).2.2.2 z hz |>.1
    exact ⟨d, hd, le_trans hdb (le_max_right _ _)⟩
  · refine ⟨jet_mono hNt (le_max_left _ _), ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hdb⟩ := (hB3 τ hτ θ hθ).2.2.2 z hz |>.2
    exact ⟨d, hd, le_trans hdb (le_max_right _ _)⟩

/-! ## The target (B6) -/

theorem DzDthSG_C1Jet_of_inputs {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂ (Work.FTS_RegExport.THL.DzG α g) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃ (Work.FTS_RegExport.THL.DthG α g) := by
  intro S hS
  obtain ⟨K, hK⟩ :=
    Work.FTS_RegExport.RXT.weighted_system (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar
      hSol hOK hdat hμ S hS
  refine c1jet_of_wsys (Φs := Φs) (E := E) (g := g) hα hα13 hOK hS (le_max_right K 0) ?_
  intro k τ hτ z θ hz hθ0 hθ1
  refine le_trans (hK k τ hτ z θ hz hθ0 hθ1) ?_
  exact mul_le_mul_of_nonneg_right (le_max_left K 0)
    (Work.FTS_RegExport.RXT.omega_nonneg_of α z θ hz.le ⟨hθ0.le, hθ1.le⟩)

end Work.FTS_RegExport.THL.L
