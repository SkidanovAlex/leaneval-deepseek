/-
# `Submission/Work/GATE/Bridge/` — PARIMPL's transit coordinate as GATE's `TransitData`

The bridge between the two formalisations of the **transit coordinate** of the imploded
parabolic germ:

* `Work.PARIMPL.TransitData` (`Submission/Work/PARIMPL/Transit.lean`) is the *provenance* form:
  it is stated in terms of the normal form `P`, the match `M`, the leak `L` (the leak level
  `L.xstar - L.j₀` and the leak radius `L.r₀` are *inside* `L`), it carries the *continuity*
  of the transit coordinate and the *exit matching*, and — crucially — its height bound
  `Work.PARIMPL.TransitData.height` and its phase blow-up
  `Work.PARIMPL.TransitData.blowup` are *derived*, not assumed.  Its escape statement
  `Work.PARIMPL.LeakData.escape` is stated for the *unshifted* leak lattice only.
* `Work.GATE.TransitData` (`Submission/Work/GATE/Defs.lean`) is the *consumer* form: the two
  leak lattices `xLeak + ℤ` and `xLeak + 1/2 + ℤ` (the `b`-tongue and the `ι b`-tongue) are
  exposed as *separate fields* `bTongue`/`iotaTongue`, the height bound is stated at the fixed
  radius `r₀/8`, and the blow-up is required on the whole frontier of `Nm`.

This file converts the first into the second, exactly as stated, so that
`Work.GATE.twoSided` (§2.1 of the design) can be fed from the PARIMPL chapter.

The conversion is a pure bookkeeping of radii and of the two lattices:

* `trans := transU P M.nIn`, `xLeak := L.xstar - L.j₀`, `r₀ := L.r₀`;
* the neighbourhood radius is `min (min (min ρ_h ρ_esc) (min ρ_ι T.ρ₁)) P.ρ₀`, where
  `ρ_h` is a radius supplied by `TransitData.height` for the bound `r₀/8`, `ρ_esc` by
  `LeakData.escape` and `ρ_ι` by the shifted-leak hypothesis `hescape_iota`; the last term
  `P.ρ₀` keeps the blow-up points inside the normal-form ball;
* `bTongue trans xLeak r₀ c` is `dist (trans c) (xLeak + k) < r₀/2` for some `k : ℤ`, hence
  `distZ (trans c) xLeak < r₀/2` (the `ℤ`-orbit distance, `Work.PARIMPL.distZ_le` with the
  shift `-k`), which is the form `LeakData.escape` consumes; and likewise for
  `iotaTongue` with `xLeak + 1/2` and the hypothesis `hescape_iota`.
-/
import Mathlib
import Submission.Work.GATE.Defs
import Submission.Work.PARIMPL.All

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

/-- If `z` is within `r` of a point of the `ℤ`-orbit `x + ℤ`, then it is within `r` of the orbit
in the sense of `Work.PARIMPL.distZ`: `distZ z x ≤ dist z (x + k)` for `k = -k₀` (the distance to
a point of the orbit is an upper bound for the distance to the orbit). -/
theorem distZ_lt_of_dist_shift {z : ℂ} {x r : ℝ} {k : ℤ}
    (h : dist z (((x + (k : ℝ)) : ℝ) : ℂ) < r) : Work.PARIMPL.distZ z ((x : ℝ) : ℂ) < r := by
  refine lt_of_le_of_lt (Work.PARIMPL.distZ_le z ((x : ℝ) : ℂ) (-k)) ?_
  have hsub : (z + ((-k : ℤ) : ℂ)) - ((x : ℝ) : ℂ) = z - (((x + (k : ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rwa [dist_eq_norm, hsub, ← dist_eq_norm]

/-- **`Work.GATE.TransitData` from `Work.PARIMPL.TransitData`.**  The transit coordinate
`transU P M.nIn` of the imploded parabolic germ, its continuity, its height bound at the leak
radius `L.r₀/8` (`TransitData.height`), its phase blow-up at the parabolic locus on the whole
frontier of `Nm` (`TransitData.blowup`, consumed here for a neighbourhood small enough that the
blow-up points stay inside the normal-form ball) and the escape property of the two leak lattices
`xLeak + ℤ` (from `LeakData.escape`) and `xLeak + 1/2 + ℤ` (the hypothesis `hescape_iota`).

The escape fields are stated for a radius that is the minimum of the five relevant radii; the
only nontrivial point is that a point of a tongue is at `distZ`-distance `< r₀/2` from the leak
lattice (`distZ_lt_of_dist_shift`), which is the form in which the escape statements are
available. -/
theorem transitData_of_PARIMPL {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
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
    Nonempty (Work.GATE.TransitData c₀ P.Nm) := by
  obtain ⟨ρe, hρe, hesc⟩ := L.escape
  obtain ⟨ρι, hρι, hι⟩ := hescape_iota
  obtain ⟨ρh, hρh, _, hheight⟩ :=
    T.height hPa hφa hentry₀ hcrit (L.r₀ / 8) (by linarith [L.hr₀])
  refine ⟨{ xLeak := L.xstar - (L.j₀ : ℝ)
            r₀ := L.r₀
            hr₀ := L.hr₀
            ρ := min (min (min ρh ρe) (min ρι T.ρ₁)) P.ρ₀
            hρ := lt_min (lt_min (lt_min hρh hρe) (lt_min hρι T.hρ₁)) P.hρ₀
            trans := fun c => Work.PARIMPL.transU P M.nIn c
            cont := ?_
            height := ?_
            blowup := ?_
            escape_b := ?_
            escape_iota := ?_ }⟩
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
