/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/EnergyDiagAssembly.lean` — the `H1IP`-energy derivative
from the `L²`-data of the slot families

This is the assembly that turns the `L²`-route derivative of the weighted square,
`hasDerivAt_integral_diag_var`, into the energy identity consumed by the recursion
(`WordEnergy`/`WordTransfer`):

  `EnergyDeriv (H1IP α) u u̇ τ`   for `u̇ = u̇ τ` the (time-dependent) slot derivative family.

The data needed per (weight, slot family) is bundled as `DiagCurve`: the two diagonal
integrabilities, the joint a.e. strong measurability of the family and of its derivative, the
pointwise Newton–Leibniz derivative, the a.e. continuity in the fake time, the uniform `L²` bound on
the derivative family, its **`L²`-continuity at `τ`** (the honest substitute for the pointwise
envelope that the constant-`udot` product rule needs and which `ℋ`-bounds cannot supply — see
`NOTES_EpsE4Thr_session4.md` §0.4), and the crossed integrability at `τ`.

`H1IP` is the sum of four weighted pairings (`H1IP_unfold`): `ρ_η` on `D_z u`, `ρ_η` on `u`,
`ρ_W` on `u` and `ρ_γ` on `D_θ u`; accordingly four `DiagCurve`s are consumed.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivAt_integral_diag_var
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

/-- **The `L²`-route data of a curve and its derivative family**, for a fixed weight `ρ` and a fixed
fake time `τ ∈ (0,T)`. -/
structure DiagCurve (ρ : ℝ → ℝ → ℝ) (u udot : ℝ → Fn) (τ T : ℝ) : Prop where
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
  cont : ∀ᵐ p ∂mup, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Icc 0 T)
  bdd : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
    ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup ≤ K
  contU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
    (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup) (nhds τ) (nhds 0)
  int_cross : MeasureTheory.Integrable
    (fun p : ℝ × ℝ => udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) mup

/-- The `L²`-route derivative of the weighted square, straight from the bundle. -/
theorem DiagCurve.hasDerivAt_integral {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (h : DiagCurve ρ u udot τ T) (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivAt (fun s : ℝ => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2 ∂mup)
      (2 * ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂mup) τ :=
  hasDerivAt_integral_diag_var_restricted hT hτ h.ρmeas h.ρnn h.int_diag h.int_diagd h.aesm h.aesmd
    h.deriv h.cont h.bdd h.contU

/-- **The `wip`-pairing derivative from the `L²`-data bundle.**  This is the shape of the
conclusion of `hasDerivAt_wip_of_slot_var`, obtained *without* the pointwise envelope. -/
theorem DiagCurve.hasDerivAt_wip {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (h : DiagCurve ρ u udot τ T) (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T) :
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

/-- **The `H1IP`-energy derivative of a family from the four `L²`-data bundles.**  With `u̇` the
value at `τ` of the derivative family (`EnergyDeriv`'s `udot` is the derivative at `τ` only), the
four weighted pairings of `H1IP_unfold` are handled at the slots `u`, `D_z u`, `D_θ u`. -/
theorem EnergyDeriv_H1IP_of_diag_data {α : ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T)
    (hη : DiagCurve Work.FTS.StrongPersist.rhoEta u udot τ T)
    (hW : DiagCurve Work.FTS.StrongPersist.rhoW u udot τ T)
    (hηz : DiagCurve Work.FTS.StrongPersist.rhoEta
      (fun s => Work.Spaces.Dz (u s)) (fun s => Work.Spaces.Dz (udot s)) τ T)
    (hγt : DiagCurve (Work.FTS.StrongPersist.rhoGam α)
      (fun s => Work.Spaces.Dth (u s)) (fun s => Work.Spaces.Dth (udot s)) τ T) :
    Work.FTS.StrongPersist.EnergyDeriv (Work.Coercivity.H1IP α) u (udot τ) τ :=
  Work.FTS.StrongPersist.energyDeriv_H1IP α
    (hη.hasDerivAt_wip hT hτ) (hηz.hasDerivAt_wip hT hτ)
    (hW.hasDerivAt_wip hT hτ) (hγt.hasDerivAt_wip hT hτ)

end Work.FTS.StrongEps.EpsE4Thr
