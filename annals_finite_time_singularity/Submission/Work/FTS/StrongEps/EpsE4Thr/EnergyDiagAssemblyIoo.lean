/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/EnergyDiagAssemblyIoo.lean` — the `L²`-route bundle with
*interior* continuity

`EnergyDiagAssembly.DiagCurve` carries `cont : ∀ᵐ p, ContinuousOn (fun s => u s p.1 p.2) (Icc 0 T)`.
That is **not** a consequence of the interior differentiability `deriv`: nothing controls the
*values* `u 0`, `u T` (take `u s := if s = 0 then 1 else 0`, `v := 0` — see the review of
`ae_continuousOn_of_hasDerivAt_Ioo`), and the sibling `VolterraBoundIoo.abs_le_of_hasDerivAt_Ioo`
also carries `ContinuousOn φ (Icc 0 T)` as a hypothesis for exactly this reason.

What *is* a consequence of interior differentiability is continuity on the open interval
(`continuousOn_Ioo_of_hasDerivAt_Ioo` below), and that is all the difference-quotient argument of
`hasDerivAt_integral_diag_var` uses (it works on a window `(τ−δ, τ+δ) ⊆ (0,T)`).  This module
therefore re-states the bundle with `Ioo`-continuity, which makes that field **free**, and records
the resulting assembly.  `DiagCurve.toIoo` embeds the old bundle into the new one, so nothing proved
against `DiagCurve` is lost.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivAt_integral_diag_var_ioo
import Submission.Work.FTS.StrongEps.EpsE4Thr.AesmRestrict

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- Differentiability at every interior point gives continuity on the open interval. -/
theorem continuousOn_Ioo_of_hasDerivAt_Ioo {φ ψ : ℝ → ℝ} {T : ℝ}
    (h : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt φ (ψ s) s) :
    ContinuousOn φ (Set.Ioo (0 : ℝ) T) :=
  fun s hs => (h s hs).continuousAt.continuousWithinAt

/-- **The `L²`-route data of a curve and its derivative family with *interior* continuity.** -/
structure DiagCurveI (ρ : ℝ → ℝ → ℝ) (u udot : ℝ → Fn) (τ T : ℝ) : Prop where
  ρmeas : AEMeasurable (Function.uncurry ρ) mup
  ρnn : ∀ᵐ p ∂mup, 0 ≤ ρ p.1 p.2
  int_diag : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2) mup
  int_diagd : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) mup
  aesm : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup)
  aesmd : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup)
  deriv : ∀ᵐ p ∂mup, ∀ s ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s
  bdd : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
    ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup ≤ K
  contU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
    (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup) (nhds τ) (nhds 0)
  int_cross : MeasureTheory.Integrable
    (fun p : ℝ × ℝ => udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) mup

/-- The `Icc`-bundle is an `Ioo`-bundle (drop the (stronger, non-derivable) `cont` field). -/
theorem DiagCurve.toIoo {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (h : DiagCurve ρ u udot τ T) : DiagCurveI ρ u udot τ T :=
  ⟨h.ρmeas, h.ρnn, h.int_diag, h.int_diagd, h.aesm, h.aesmd, h.deriv, h.bdd, h.contU,
    h.int_cross⟩

/-- The `Ioo`-continuity is *free* from `deriv`. -/
theorem DiagCurveI.cont {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (h : DiagCurveI ρ u udot τ T) :
    ∀ᵐ p ∂mup, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Ioo (0 : ℝ) T) :=
  h.deriv.mono fun _ hp => continuousOn_Ioo_of_hasDerivAt_Ioo hp

/-- The `L²`-route derivative of the weighted square, straight from the `Ioo`-bundle. -/
theorem DiagCurveI.hasDerivAt_integral {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (h : DiagCurveI ρ u udot τ T) (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivAt (fun s : ℝ => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2 ∂mup)
      (2 * ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂mup) τ :=
  hasDerivAt_integral_diag_var_ioo_restricted hT hτ h.ρmeas h.ρnn h.int_diag h.int_diagd h.aesm h.aesmd
    h.deriv h.cont h.bdd h.contU

/-- **The `wip`-pairing derivative from the `Ioo`-bundle.** -/
theorem DiagCurveI.hasDerivAt_wip {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (h : DiagCurveI ρ u udot τ T) (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivAt (fun s => Work.Coercivity.wip ρ (u s) (u s))
      (2 * Work.Coercivity.wip ρ (udot τ) (u τ)) τ := by
  have hmain := h.hasDerivAt_integral hT hτ
  have hfun : (fun s : ℝ => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2 ∂mup)
      =ᶠ[nhds τ] fun s => Work.Coercivity.wip ρ (u s) (u s) := by
    filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with s hs
    have hinter : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2) mup :=
      (h.int_diag s hs).congr (Filter.Eventually.of_forall fun p => by ring)
    exact (wip_self_eq_integral_prod hinter).symm
  have hval : 2 * (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂mup)
      = 2 * Work.Coercivity.wip ρ (udot τ) (u τ) := by
    rw [wip_eq_integral_prod h.int_cross]
  rw [hval] at hmain
  exact hmain.congr_of_eventuallyEq hfun.symm

/-- **The `H1IP`-energy derivative of a family from the four `Ioo`-bundles.** -/
theorem EnergyDeriv_H1IP_of_diag_data_I {α : ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T)
    (hη : DiagCurveI Work.FTS.StrongPersist.rhoEta u udot τ T)
    (hW : DiagCurveI Work.FTS.StrongPersist.rhoW u udot τ T)
    (hηz : DiagCurveI Work.FTS.StrongPersist.rhoEta
      (fun s => Work.Spaces.Dz (u s)) (fun s => Work.Spaces.Dz (udot s)) τ T)
    (hγt : DiagCurveI (Work.FTS.StrongPersist.rhoGam α)
      (fun s => Work.Spaces.Dth (u s)) (fun s => Work.Spaces.Dth (udot s)) τ T) :
    Work.FTS.StrongPersist.EnergyDeriv (Work.Coercivity.H1IP α) u (udot τ) τ :=
  Work.FTS.StrongPersist.energyDeriv_H1IP α
    (hη.hasDerivAt_wip hT hτ) (hηz.hasDerivAt_wip hT hτ)
    (hW.hasDerivAt_wip hT hτ) (hγt.hasDerivAt_wip hT hτ)

end Work.FTS.StrongEps.EpsE4Thr
