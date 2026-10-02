import Mathlib
import Submission.Work.GATE.Defs
import Submission.Work.PARIMPL.All
import Submission.Work.GATE.Bridge.transitData_of_PARIMPL

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE.Bridge

/-- **The fields of `Work.GATE.TransitData` from `Work.PARIMPL.TransitData`, at a radius which
is also `≤ T.ρ₁`.**  This is the field-by-field form of `transitData_of_PARIMPL`: the transit
coordinate `transU P M.nIn`, its continuity, its height bound at the leak radius `L.r₀/8`
(`TransitData.height`), its phase blow-up on the whole frontier of `Nm` (`TransitData.blowup`,
consumed for a neighbourhood small enough that the blow-up points stay inside the normal-form
ball) and the escape property of the two leak lattices `xLeak + ℤ` (`LeakData.escape`) and
`xLeak + 1/2 + ℤ` (the hypothesis `hescape_iota`).

The only new point with respect to `transitData_of_PARIMPL` is the extra bound `ρ ≤ T.ρ₁`; the
radius is the same minimum of the five relevant radii. -/
theorem transitData_fields_of_PARIMPL {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {G : ℂ → ℂ} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P G Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P G Pa φa Ψ M} {L : Work.PARIMPL.LeakData d P G Pa φa Ψ M T}
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hescape_iota : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      Work.PARIMPL.distZ (Work.PARIMPL.transU P M.nIn c)
        (((L.xstar - (L.j₀ : ℝ) + 1 / 2 : ℝ)) : ℂ) < L.r₀ / 2 →
        c ∉ LeanEval.ComplexAnalysis.Mandelbar) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ T.ρ₁ ∧
      ContinuousOn (fun c => Work.PARIMPL.transU P M.nIn c) (P.Nm ∩ Metric.ball c₀ ρ) ∧
      (∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, |(Work.PARIMPL.transU P M.nIn c).im| ≤ L.r₀ / 8) ∧
      (∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρ,
        Filter.Tendsto (fun c => (Work.PARIMPL.transU P M.nIn c).re) (nhdsWithin p P.Nm)
          Filter.atBot) ∧
      (∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
        Work.GATE.bTongue (fun c => Work.PARIMPL.transU P M.nIn c)
          (L.xstar - (L.j₀ : ℝ)) L.r₀ c → c ∉ LeanEval.ComplexAnalysis.Mandelbar) ∧
      (∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
        Work.GATE.iotaTongue (fun c => Work.PARIMPL.transU P M.nIn c)
          (L.xstar - (L.j₀ : ℝ)) L.r₀ c → c ∉ LeanEval.ComplexAnalysis.Mandelbar) := by
  obtain ⟨ρe, hρe, hesc⟩ := L.escape
  obtain ⟨ρι, hρι, hι⟩ := hescape_iota
  obtain ⟨ρh, hρh, _, hheight⟩ :=
    T.height hPa hφa hentry₀ hcrit (L.r₀ / 8) (by linarith [L.hr₀])
  refine ⟨min (min (min ρh ρe) (min ρι T.ρ₁)) P.ρ₀,
    lt_min (lt_min (lt_min hρh hρe) (lt_min hρι T.hρ₁)) P.hρ₀,
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity, on the smaller neighbourhood
    refine T.cont.mono (Set.inter_subset_inter_right _
      (Metric.ball_subset_ball ?_))
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  · -- the height bound at the fixed radius `r₀/8`
    intro c hc
    refine hheight c ⟨hc.1, Metric.ball_subset_ball ?_ hc.2⟩
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  · -- the phase blow-up on the frontier, through `TransitData.blowup` at `a₂ = 0`
    intro p hp
    rw [frontier_eq_closure_inter_closure] at hp
    have hballρ : p ∈ Metric.ball c₀ (min (min (min ρh ρe) (min ρι T.ρ₁)) P.ρ₀) := hp.2
    have hball₀ : p ∈ Metric.ball c₀ P.ρ₀ := by
      rw [Metric.mem_ball] at hballρ ⊢
      exact lt_of_lt_of_le hballρ (min_le_right _ _)
    have hnot : p ∉ P.Nm := by
      intro hmem
      have hn : P.Nm ∈ 𝓝 p := P.isOpen_Nm.mem_nhds hmem
      obtain ⟨y, hyn, hyc⟩ := (mem_closure_iff_nhds.mp hp.1.2) P.Nm hn
      exact hyc hyn
    exact T.blowup p (P.a2_zero_of_closure_notMem hp.1.1 hball₀ hnot) hball₀
  · -- the `b`-tongue, from `LeakData.escape`
    intro c hc hb
    obtain ⟨k, hk⟩ := hb
    refine hesc c ⟨hc.1, Metric.ball_subset_ball ?_ hc.2⟩ ?_
    · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    · exact distZ_lt_of_dist_shift (z := Work.PARIMPL.transU P M.nIn c)
        (x := L.xstar - (L.j₀ : ℝ)) hk
  · -- the `ι b`-tongue, from the hypothesis
    intro c hc hb
    obtain ⟨k, hk⟩ := hb
    refine hι c ⟨hc.1, Metric.ball_subset_ball ?_ hc.2⟩ ?_
    · exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact distZ_lt_of_dist_shift (z := Work.PARIMPL.transU P M.nIn c)
        (x := L.xstar - (L.j₀ : ℝ) + 1 / 2) hk

end Work.GATE.Bridge

end
