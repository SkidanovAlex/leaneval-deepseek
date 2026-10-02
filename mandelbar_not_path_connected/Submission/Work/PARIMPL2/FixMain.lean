/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.FixMain` — the corrected bundles, constructed from the sibling exports

Chain B of the area: from the sibling exports of `Work.PARIMPL2.SiblingInputs`,
* `Work.PARIMPL2.MatchExport` — MATCH in the **corrected** orientation
  (`NOTES_FALSE_match_in.md`, `NOTES_FALSE_match_out.md`), the satisfiable one;
* `Work.PARIMPL2.LockstepAll` — the uniform lock-step transit in the design's form (every bounded
  box; `NOTES_FALSE_ExitTrackedLoc.md`), plus the branch conditions of `transU`;
* `Work.PARIMPL2.LeakExport` — GATE2's ρ-maximising leak centre `xLeak = y₀`, ELAssembly's equator
  leak at it, and the tongue escape;

build the corrected holder structures `Work.PARIMPL2.MatchData`, `TransitData`, `LeakData`,
`ParImplInputs` (`Submission/Work/PARIMPL2/DefsFix.lean`), and with them

* `Work.PARIMPL2.implFix` — `Work.PARIMPL.ImplSide c₀ z₁ P.Nm`;
* `Work.PARIMPL2.noPathFix` — the path form of `hLB` (`Submission/Work/PARIMPL2/PathFix.lean`).

`cont` is derived (`Work.PARIMPL.continuousOn_transU`), `deep`/`robust` are derived
(`exists_deepDisc`, `Work.PARIMPL.robust_of_greenOpen`, `Work.NAKANE.greenEscapeOpen`), and the
escape is taken at the radius `min r_{escape} r_{deep}` (monotone in the radius).
-/
import Submission.Work.PARIMPL2.PathFix
import Submission.Work.PARIMPL2.Data
import Submission.Work.PARIMPL2.Inputs
import Submission.Work.FlowerGlue.ParImplGlue

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
open Work.PARIMPL (ParNormal MatchData TransitData LeakData transU entryPt Ft gtc)

variable {c₀ : ℂ}

/-! ## The three bundles (corrected) -/

/-- **The corrected MATCH bundle**, from the coordinate identity `Work.PARIMPL2.MatchCore`. -/
def matchDataFix {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {nIn : ℕ} (E : MatchCore d P Pa φa Ψ nIn) :
    Work.PARIMPL2.MatchData d P Pa φa Ψ where
  nIn := nIn
  R := E.R
  hR := E.hR
  ρin := E.ρin
  hρin := E.hρin
  le_ρ₀ := E.le_ρ₀
  match_in := match_in_of_coord E
  match_out := match_out_of_coord E
  te := E.te
  entering := E.entering

/-- **The corrected TRANS bundle**: `cont` derived from `Work.PARIMPL.continuousOn_transU`
(via the two branch conditions) and `UT` from the design's `LockstepAll`. -/
def transitDataFix {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} (M : Work.PARIMPL2.MatchData d P Pa φa Ψ)
    (UT : LockstepAll c₀ P.Nm (transU P M.nIn) M.nIn (fun c z => Ft c z) Pa φa Ψ
      ((φa (entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (ρ₁ : ℝ) (hρ₁ : 0 < ρ₁) (le_ρ₀ : ρ₁ ≤ P.ρ₀)
    (slit₁ : ∀ c ∈ P.Nm ∩ ball c₀ ρ₁,
      Work.Implosion.mobius (P.a c) (Work.PARIMPL.chartZeta P c (entryPt P M.nIn c))
        ∈ Complex.slitPlane)
    (slit₂ : ∀ c ∈ P.Nm ∩ ball c₀ ρ₁,
      Complex.sinh (P.a c * Work.PARIMPL.ecalUin P c (entryPt P M.nIn c)) / P.a c
        ∈ Complex.slitPlane) :
    Work.PARIMPL2.TransitData d P Pa φa Ψ M where
  ρ₁ := ρ₁
  hρ₁ := hρ₁
  le_ρ₀ := le_ρ₀
  cont := Work.PARIMPL.continuousOn_transU P M.nIn hρ₁ slit₁ slit₂
  UT := transitLockstep_of_lockstepAll UT

/-- **The corrected LEAK bundle**, from `Work.PARIMPL2.LeakExport`: the centre is GATE2's `xLeak`
(`j₀ := 0`), `deep` and `robust` are derived, and the escape is used at
`min r_{escape} r_{deep}`. -/
def leakDataFix {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (M : Work.PARIMPL2.MatchData d P Pa φa Ψ)
    (T : Work.PARIMPL2.TransitData d P Pa φa Ψ M) (E : LeakExport d P Pa φa Ψ M.nIn) :
    Work.PARIMPL2.LeakData d P Pa φa Ψ M T :=
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

/-- **The leak centre is GATE2's `xLeak`** (chain B). -/
theorem leakDataFix_yLeak {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (M : Work.PARIMPL2.MatchData d P Pa φa Ψ)
    (T : Work.PARIMPL2.TransitData d P Pa φa Ψ M) (E : LeakExport d P Pa φa Ψ M.nIn) :
    (leakDataFix hΨ M T E).yLeak = E.y₀ := by
  simp [leakDataFix, Work.PARIMPL2.LeakData.yLeak]

/-! ## The assembly -/

/-- **The corrected `ParImplInputs`**, assembled from `Work.PARIMPL2.SiblingInputs`: every
field is a sibling export or is derived (see `NOTES.md` §2). -/
def parImplInputsFix (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (h : SiblingInputs d P fl.Pa fl.φa fl.Ψ (Work.PARIMPL.nEnter d fl)) :
    Work.PARIMPL2.ParImplInputs where
  c₀ := c₀
  d := d
  P := P
  Pa := fl.Pa
  φa := fl.φa
  Ψ := fl.Ψ
  M := matchDataFix h.M
  T := transitDataFix (matchDataFix h.M) h.T.UT h.T.ρ₁ h.T.hρ₁ h.T.le_ρ₀ h.T.slit₁ h.T.slit₂
  L := leakDataFix fl.Ψ_diff.continuous (matchDataFix h.M)
        (transitDataFix (matchDataFix h.M) h.T.UT h.T.ρ₁ h.T.hρ₁ h.T.le_ρ₀ h.T.slit₁ h.T.slit₂) h.L
  c_mem_closure := Work.PARIMPL.Nm_mem_closure d P
  fix := Work.FlowerGlue.flowerFixOfFix d fl
  zdecay := h.zdecay
  greenOpen := Work.NAKANE.greenEscapeOpen
  isOpen_Pa := fl.isOpen_Pa
  diff_φa := fl.φa_fatou.1.2.1
  entry_mem := Work.PARIMPL.nEnter_spec d fl
  critHeight_zero := h.critHeight_zero

/-- **`impl`** for the corrected bundles. -/
theorem implFix (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (h : SiblingInputs d P fl.Pa fl.φa fl.Ψ (Work.PARIMPL.nEnter d fl)) :
    Work.PARIMPL.ImplSide c₀ d.z₁ P.Nm :=
  (parImplInputsFix d P fl h).impl

/-- **`noPath`** for the corrected bundles: the `hLB` of the endgame in path form. -/
theorem noPathFix (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (h : SiblingInputs d P fl.Pa fl.φa fl.Ψ (Work.PARIMPL.nEnter d fl)) :
    ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ P.Nm) :=
  Work.PARIMPL2.noPath d P (matchDataFix h.M)
    (transitDataFix (matchDataFix h.M) h.T.UT h.T.ρ₁ h.T.hρ₁ h.T.le_ρ₀ h.T.slit₁ h.T.slit₂)
    (leakDataFix fl.Ψ_diff.continuous (matchDataFix h.M)
      (transitDataFix (matchDataFix h.M) h.T.UT h.T.ρ₁ h.T.hρ₁ h.T.le_ρ₀ h.T.slit₁ h.T.slit₂) h.L)
    fl.isOpen_Pa fl.φa_fatou.1.2.1 (Work.PARIMPL.nEnter_spec d fl) h.critHeight_zero

end Work.PARIMPL2

end
