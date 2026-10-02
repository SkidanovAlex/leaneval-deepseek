/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Data` — the three data bundles of the implosion endgame

Chain A of the area: from the sibling exports `Work.PARIMPL2.MatchExport`,
`Work.PARIMPL2.TransitExport`, `Work.PARIMPL2.LeakExport`, build the *delivered* holder structures
`Work.PARIMPL.MatchData`, `Work.PARIMPL.TransitData`, `Work.PARIMPL.LeakData`.

What is *derived* here (as opposed to taken from the sibling):

* `MatchData` — the data choices (`nIn := Work.PARIMPL.nEnter d fl`, `ρin`, `R`) and the packaging;
* `TransitData.cont` — the continuity of `transU` on `Nm ∩ ball c₀ ρ₁`, proved from the two
  slit-plane (branch) conditions by the delivered `Work.PARIMPL.continuousOn_transU`;
* `LeakData.deep` — the depth of the leak disc, from `Ψ y₀ ∉ K c₀` (the equator leak at the
  ρ-maximising centre) by the closedness of `K c₀` and the continuity of `Ψ`; the centre is `y₀`
  itself (`j₀ := 0`), i.e. GATE2's `xLeak`;
* `LeakData.robust` — the family robustness (I2), from `Work.PARIMPL.robust_of_greenOpen` and the
  **proved** NAKANE input `Work.NAKANE.greenEscapeOpen`;
* `LeakData.escape` — the tongue escape at the *chosen* radius `r := min r_{escape} r_{deep}`, by
  the monotonicity of `distZ · < r/2 → c ∉ Mb` in the radius.

See `Work.PARIMPL2.Fix` for chain B, the same three bundles against the **corrected** MATCH
orientation of `NOTES_FALSE_match_in.md`.
-/
import Submission.Work.PARIMPL2.Inputs
import Submission.Work.PARIMPL.continuousOn_transU
import Submission.Work.PARIMPL.robust_of_greenOpen
import Submission.Work.PARIMPL.Nm_mem_closure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.PARIMPL (ParNormal MatchData TransitData LeakData Win Wout transU approxU approxUin
  entryPt chartZeta ecalUin Ft gtc)

variable {c₀ : ℂ}

/-! ## MATCH -/

/-- **The MATCH bundle**: the delivered `Work.PARIMPL.MatchData` (with the corrected comparisons,
`Submission/Work/PARIMPL/NOTES.md` §0.0), assembled from the **coordinate identity**
`Work.PARIMPL2.MatchCore` by `Work.PARIMPL2.matchData_of_core` (the two height comparisons are
*derived* there). -/
def matchData {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {nIn : ℕ} (E : MatchCore d P Pa φa Ψ nIn) :
    MatchData d P Pa φa Ψ :=
  matchData_of_core E

/-- The MATCH bundle, in `Nonempty` form. -/
theorem exists_matchData {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {nIn : ℕ} (E : MatchExport d P Pa φa Ψ nIn) :
    Nonempty (MatchData d P Pa φa Ψ) :=
  ⟨matchData E⟩

/-! ## TRANS -/

/-- **The TRANS bundle**: the delivered `Work.PARIMPL.TransitData`, from the sibling export
`Work.PARIMPL2.TransitExport` (the uniform lock-step transit `UT` and the two branch conditions)
and the MATCH bundle.

The field `cont` is *derived*: this is the field that the delivered chapter had reduced to a
named hypothesis, discharged here by `Work.PARIMPL.continuousOn_transU`. -/
def transitData {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} (M : MatchData d P Pa φa Ψ)
    (E : TransitExport d P Pa φa Ψ M.nIn) : TransitData d P Pa φa Ψ M where
  ρ₁ := E.ρ₁
  hρ₁ := E.hρ₁
  le_ρ₀ := E.le_ρ₀
  cont := Work.PARIMPL.continuousOn_transU P M.nIn E.hρ₁ E.slit₁ E.slit₂
  UT := transitLockstep_of_lockstepAll E.UT

/-- The TRANS bundle, in `Nonempty` form. -/
theorem exists_transitData {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} (M : MatchData d P Pa φa Ψ)
    (E : TransitExport d P Pa φa Ψ M.nIn) :
    Nonempty (TransitData d P Pa φa Ψ M) :=
  ⟨transitData M E⟩

/-! ## LEAK -/

/-- The escaping region is open around the leak centre: with `Ψ` continuous and `K c₀` closed, a
whole disc around `y₀` is mapped off the filled Julia set, hence carries positive Green function. -/
theorem exists_deepDisc {Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) {y₀ : ℝ}
    (hleak : Ψ ((y₀ : ℝ) : ℂ) ∉ Work.EL.K c₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ closedBall (((y₀ : ℝ)) : ℂ) r,
      0 < Work.Bottcher.green c₀ (Ψ y) := by
  have hopen : IsOpen (Ψ ⁻¹' (Work.EL.K c₀)ᶜ) :=
    (Work.ParamRays.isClosed_filledJulia c₀).isOpen_compl.preimage hΨ
  have hmem : ((y₀ : ℝ) : ℂ) ∈ Ψ ⁻¹' (Work.EL.K c₀)ᶜ := hleak
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro y hy
  refine Work.PARIMPL.green_pos_of_notMem_K (hrsub ?_)
  rw [Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  linarith

/-- **The LEAK bundle**: the delivered `Work.PARIMPL.LeakData`, from the sibling export
`Work.PARIMPL2.LeakExport` (GATE2's ρ-maximising leak centre `y₀ = xLeak` and the tongue escape,
ELAssembly's equator leak at it).

The centre is `L.yLeak = xstar − j₀ = y₀` (`j₀ := 0`), i.e. exactly GATE2's `xLeak`; the radius is
`min r_{escape} r_{deep}`, the escape being monotone in the radius. -/
def leakData {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (M : MatchData d P Pa φa Ψ)
    (T : TransitData d P Pa φa Ψ M) (E : LeakExport d P Pa φa Ψ M.nIn) :
    LeakData d P Pa φa Ψ M T :=
  let rdeep : ℝ := Classical.choose (exists_deepDisc hΨ E.leak₀)
  let hdeep : ∀ y ∈ closedBall (((E.y₀ : ℝ)) : ℂ) rdeep,
      0 < Work.Bottcher.green c₀ (Ψ y) :=
    (Classical.choose_spec (exists_deepDisc hΨ E.leak₀)).2
  let hrdeep : 0 < rdeep := (Classical.choose_spec (exists_deepDisc hΨ E.leak₀)).1
  let ρe : ℝ := Classical.choose E.escape
  let hρe : 0 < ρe := (Classical.choose_spec E.escape).1
  let hesc : ∀ c ∈ P.Nm ∩ ball c₀ ρe, ∀ y : ℝ, (y = E.y₀ ∨ y = E.y₀ + 1 / 2) →
      Work.PARIMPL.distZ (transU P M.nIn c) ((y : ℝ) : ℂ) < E.r₀ / 2 → c ∉ Mandelbar :=
    (Classical.choose_spec E.escape).2
  { xstar := E.y₀
    j₀ := 0
    r₀ := min E.r₀ rdeep
    hr₀ := lt_min E.hr₀ hrdeep
    leak := by simpa using E.leak₀
    deep := by
      intro y hy
      refine hdeep y ?_
      have h' : dist y (((E.y₀ : ℝ)) : ℂ) ≤ min E.r₀ rdeep := by
        simpa [Metric.mem_closedBall] using hy
      simpa [Metric.mem_closedBall] using le_trans h' (min_le_right _ _)
    robust := Work.PARIMPL.robust_of_greenOpen hΨ Work.NAKANE.greenEscapeOpen
      (lt_min E.hr₀ hrdeep)
      (fun y hy => hdeep y (by
        have h' : dist y (((E.y₀ : ℝ)) : ℂ) ≤ min E.r₀ rdeep := by
          simpa [Metric.mem_closedBall] using hy
        simpa [Metric.mem_closedBall] using le_trans h' (min_le_right _ _)))
    escape := by
      refine ⟨ρe, hρe, fun c hc y hy hlt => hesc c hc y ?_ ?_⟩
      · rcases hy with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa using h)
      · exact lt_of_lt_of_le hlt (by linarith [min_le_left E.r₀ rdeep]) }

/-- **The leak centre is GATE2's `xLeak`.**  The centre `xstar − j₀` of the constructed leak disc
is exactly the `y₀` of the sibling export (GATE2's ρ-maximiser), which is what the coordination
`TD.xLeak = H.L.yLeak` of `NOTES_LEAD_mandelbar_gaps2.md` §4 requires. -/
theorem leakData_yLeak {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (M : MatchData d P Pa φa Ψ)
    (T : TransitData d P Pa φa Ψ M) (E : LeakExport d P Pa φa Ψ M.nIn) :
    (leakData hΨ M T E).yLeak = E.y₀ := by
  simp [leakData, Work.PARIMPL.LeakData.yLeak]

/-- The LEAK bundle, in `Nonempty` form. -/
theorem exists_leakData {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (M : MatchData d P Pa φa Ψ)
    (T : TransitData d P Pa φa Ψ M) (E : LeakExport d P Pa φa Ψ M.nIn) :
    Nonempty (LeakData d P Pa φa Ψ M T) :=
  ⟨leakData hΨ M T E⟩

end Work.PARIMPL2

end
