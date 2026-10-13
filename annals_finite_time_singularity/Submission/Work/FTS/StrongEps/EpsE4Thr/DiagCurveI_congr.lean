/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/DiagCurveI_congr.lean` — `DiagCurveI` depends only on the
values on the horizon and on the open quadrant

`DiagCurveI ρ u udot τ T` (`EnergyDiagAssemblyIoo.lean`) is a bundle of *a.e.* statements with
respect to

  `μ = (volume.restrict (Icc 0 T)).prod mup`,  `mup = (volume.restrict Iz).prod (volume.restrict Iθ)`,

plus `ρ`-weighted `L²` statements (integrability, uniform bounds, continuity at `τ`), all of which
are integrals over `mup` as well, restricted to the fake-time horizon `Icc 0 T` — the family is
*only known there* (`AesmRestrict.lean`).

`mup` is carried by the open quadrant `Q0 = (0,∞) × (0,π/2)` (`ae_mem_openQuadrant_fts`): the
complement inside `Iz × Iθ` is the union of the null segments `{0} × Iθ`, `Iz × {0}`,
`Iz × {π/2}`.  Consequently two families which agree pointwise on `Q0` **for every time in the
horizon** give the same `DiagCurveI` data.  (The time is *not* quantified over all of `ℝ`: the
`aesm` field is an a.e. statement for `μ`, whose time-projection is the restriction to `Icc 0 T`.)

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssemblyIoo
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipSlotIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem DiagCurveI_congr {ρ : ℝ → ℝ → ℝ} {u u' udot udot' : ℝ → Work.FTS.Galerkin.Fn}
    {τ T : ℝ}
    (h : Work.FTS.StrongEps.EpsE4Thr.DiagCurveI ρ u udot τ T)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hu : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      u s p.1 p.2 = u' s p.1 p.2)
    (hud : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      udot s p.1 p.2 = udot' s p.1 p.2) :
    Work.FTS.StrongEps.EpsE4Thr.DiagCurveI ρ u' udot' τ T := by
  have hτIcc : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  -- `mup` is σ-finite (needed to speak about a.e. statements for a product measure)
  have hSFin : SFinite mup := by rw [mup]; infer_instance
  -- the open quadrant carries `mup`
  have hQ0 : ∀ᵐ p ∂mup, p ∈ Work.FTS.EllipticEst.Q0 := by
    rw [mup, Work.FTS.EllipticEst.Q0]
    exact ae_mem_openQuadrant_fts
  -- ... and hence the time-horizon slab carries the product measure
  have hQ0' : ∀ᵐ q ∂((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup),
      q.1 ∈ Set.Icc (0 : ℝ) T ∧ q.2 ∈ Work.FTS.EllipticEst.Q0 := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      (p := fun q : ℝ × (ℝ × ℝ) => q.1 ∈ Set.Icc (0 : ℝ) T ∧ q.2 ∈ Work.FTS.EllipticEst.Q0)
      ((measurableSet_Icc.preimage measurable_fst).inter
        (Work.FTS.EllipticEst.isOpen_Q0.measurableSet.preimage measurable_snd))]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    filter_upwards [hQ0] with p hp
    exact ⟨hs, hp⟩
  refine ⟨h.ρmeas, h.ρnn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `int_diag`
    intro s hs
    exact (h.int_diag s hs).congr (hQ0.mono fun p hp => by simp only [hu s hs p hp])
  · -- `int_diagd`
    intro s hs
    exact (h.int_diagd s hs).congr (hQ0.mono fun p hp => by simp only [hud s hs p hp])
  · -- `aesm`
    exact h.aesm.congr (hQ0'.mono fun q hq => hu q.1 hq.1 q.2 hq.2)
  · -- `aesmd`
    exact h.aesmd.congr (hQ0'.mono fun q hq => hud q.1 hq.1 q.2 hq.2)
  · -- `deriv`
    filter_upwards [hQ0, h.deriv] with p hp hd
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    rw [show udot' s p.1 p.2 = udot s p.1 p.2 from (hud s hsIcc p hp).symm]
    refine (hd s hs).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with t ht
    exact (hu t ht p hp).symm
  · -- `bdd`
    obtain ⟨K, hK0, hK⟩ := h.bdd
    refine ⟨K, hK0, fun σ hσ => ?_⟩
    have hi : (fun p : ℝ × ℝ => (udot' σ p.1 p.2) ^ 2 * ρ p.1 p.2)
        =ᵐ[mup] (fun p : ℝ × ℝ => (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2) :=
      hQ0.mono fun p hp => by simp only [← hud σ hσ p hp]
    rw [MeasureTheory.integral_congr_ae hi]
    exact hK σ hσ
  · -- `contU`
    refine h.contU.congr' ?_
    filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with σ hσ
    exact (MeasureTheory.integral_congr_ae
      (hQ0.mono fun p hp => by simp only [← hud σ hσ p hp, ← hud τ hτIcc p hp])).symm
  · -- `int_cross`
    exact (MeasureTheory.integrable_congr (hQ0.mono fun p hp => by
      simp only [← hud τ hτIcc p hp, ← hu τ hτIcc p hp])).mpr h.int_cross

end Work.FTS.StrongEps.EpsE4Thr
