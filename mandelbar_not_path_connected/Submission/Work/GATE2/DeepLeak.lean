/-
# GATE2 — the drive with the leak centre **chosen by GATE2**, and the escape derived

`Work.GATE2.twoSided_trans_of_lockstepAllAt` (`LockstepAt.lean`) takes the leak centre `xLeak`,
its radius `r₀` and the escape `hesc` as hypotheses.  This module removes the escape:

* **`Work.GATE2.escapeAt_one`** — for a real point `x` and a radius `r` with `x + r/2 < -1`, if the
  leak disc `Ψ '' closedBall x r` is **robust** for parameters near `c₀` (nothing within `ρ` of
  `Ψ '' closedBall x r` is in `K c`), then a transit coordinate `trans c` landing on `x` modulo `ℤ`
  forces `c ∉ Mandelbar`.  The proof is the PARIMPL2 chain `exitTrackedWindow_of_lockstep` (the
  uniform lock-step transit `LockstepAll` gives the bounded-window exit) followed by
  `escape_of_exitTrackedWindow`.
* **`Work.GATE2.DeepLeak c₀ Ψ x`** — the single datum that the chosen centre `x` is a **deep real
  leak point**: some radius `r > 0` with `x + r/2 < -3/2` whose two discs
  `closedBall x r`, `closedBall (x + 1/2) r` map off `K c₀`.  Robustness then follows from NAKANE's
  joint Green continuity (`Work.PARIMPL.robust_of_greenOpen` + `greenEscapeOpen`), and `DeepLeak`
  itself follows from `Ψ x ∉ K c₀` and `x < -3/2` (`deepLeak_of_leak`; the `+1/2` condition is the
  `g`-total-invariance of `K`, `fl.Ψ_anti` + `Work.PARIMPL.mem_K_tantibar_iterate_iff`).
* **`Work.GATE2.twoSided_of_deepLeak`** — the drive: `Work.GATE.TwoSided c₀ P.Nm` from PARIMPL's
  data, the flower + `hSat`, the transit facts, PARIMPL2's `LockstepAll`, NAKANE's
  `greenEscapeOpen`, `DeepLeak c₀ fl.Ψ xLeak`, and the two **exit-loop families**
  `∃ R > 0, ∀ r₀ ∈ Ioc 0 R, ∀ v, Nonempty (ExitLoop …)`.  No `LeakData`, no `hv`, no `hK`/`hHalf`
  and no escape hypothesis.
-/
import Submission.Work.GATE2.LockstepAt
import Submission.Work.PARIMPL.leak_shift_int
import Submission.Work.PARIMPL.robust_of_greenOpen
import Submission.Work.PARIMPL2.Data
import Submission.Work.PARIMPL2.escape_of_exitTrackedWindow
import Submission.Work.PARIMPL2.exitTrackedWindow_of_lockstep
import Submission.Work.NAKANE.GreenEscapeOpen
import Submission.Work.GATE2.EXL.MinCrossing

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
set_option maxHeartbeats 800000

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The deep-leak datum at the chosen centre `x`**: a radius `r > 0` deep enough that
`x + r/2 < -3/2` (so that the escape applies to *both* lattices `x + ℤ` and `x + 1/2 + ℤ`), with
both discs `closedBall x r` and `closedBall (x + 1/2) r` mapped **off** `K c₀` by `Ψ`. -/
def DeepLeak (c₀ : ℂ) (Ψ : ℂ → ℂ) (x : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ x + r / 2 < -(3 / 2 : ℝ) ∧
    (∀ z ∈ Metric.closedBall ((x : ℝ) : ℂ) r, Ψ z ∉ Work.EL.K c₀) ∧
    (∀ z ∈ Metric.closedBall (((x + 1 / 2 : ℝ)) : ℂ) r, Ψ z ∉ Work.EL.K c₀)

/-- **A deep real leak point is a `DeepLeak`.**  From `Ψ x ∉ K c₀` and `x < -3/2`: the `Ψ`-image of
a small disc around `x` is off the closed set `K c₀`, and the same holds for `x + 1/2` because
`Ψ (x + 1/2) = g (Ψ x)` with `g = (T c₀)^[5]` (`fl.Ψ_anti`) and `K c₀` totally invariant under the
iterates of `T c₀` (`Work.PARIMPL.mem_K_tantibar_iterate_iff`). -/
theorem deepLeak_of_leak {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    {x : ℝ} (hx : x < -(3 / 2 : ℝ))
    (hleak : fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c₀) :
    DeepLeak c₀ fl.Ψ x := by
  have hleak₂ : fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ) ∉ Work.EL.K c₀ := by
    have hanti := fl.Ψ_anti ((x : ℝ) : ℂ)
    have hstar : star ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by simp
    rw [hstar] at hanti
    have h1 : ((x + 1 / 2 : ℝ) : ℂ) = ((x : ℝ) : ℂ) + 1 / 2 := by push_cast; ring
    have hanti' : fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ) = ((Tantibar c₀)^[5]) (fl.Ψ ((x : ℝ) : ℂ)) := by
      rw [h1]; simpa using hanti
    rw [hanti']
    intro hmem
    exact hleak ((Work.PARIMPL.mem_K_tantibar_iterate_iff c₀ (fl.Ψ ((x : ℝ) : ℂ)) 5).mp hmem)
  obtain ⟨r₁, hr₁, hd₁⟩ :=
    Work.PARIMPL2.exists_deepDisc (c₀ := c₀) fl.Ψ_diff.continuous hleak
  obtain ⟨r₂, hr₂, hd₂⟩ :=
    Work.PARIMPL2.exists_deepDisc (c₀ := c₀) fl.Ψ_diff.continuous hleak₂
  have hpos : (0 : ℝ) < (-3 - 2 * x) / 4 := by linarith
  refine ⟨min r₁ (min r₂ ((-3 - 2 * x) / 4)), lt_min hr₁ (lt_min hr₂ hpos), ?_, ?_, ?_⟩
  · have h : min r₁ (min r₂ ((-3 - 2 * x) / 4)) ≤ min r₂ ((-3 - 2 * x) / 4) := min_le_right _ _
    have h2 : min r₂ ((-3 - 2 * x) / 4) ≤ (-3 - 2 * x) / 4 := min_le_right _ _
    linarith
  · intro z hz
    refine Work.PARIMPL.notMem_K_of_green_pos (hd₁ z ?_)
    rw [Metric.mem_closedBall] at hz ⊢
    exact le_trans hz (min_le_left _ _)
  · intro z hz
    refine Work.PARIMPL.notMem_K_of_green_pos (hd₂ z ?_)
    rw [Metric.mem_closedBall] at hz ⊢
    exact le_trans hz (le_trans (min_le_right _ _) (min_le_left _ _))

/-- **The escape at one leak centre, from the uniform lock-step transit.**  PARIMPL2's
`exitTrackedWindow_of_lockstep` turns `LockstepAll` (plus the flower facts and the blow-up
`hblow`) into the bounded-window exit tracking, and `escape_of_exitTrackedWindow` turns that plus
the robustness `hrob` of the leak disc into the escape. -/
theorem escapeAt_one {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    (trans : ℂ → ℂ)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    {x r : ℝ} (hr : 0 < r) (hx : x + r / 2 < -1)
    (hrob : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall ((x : ℝ) : ℂ) r, dist y (Ψ z) ≤ ρ) → y ∉ Work.EL.K c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      Work.PARIMPL.distZ (trans c) ((x : ℝ) : ℂ) < r / 2 → c ∉ Mandelbar := by
  have hmapsTo : Set.MapsTo (fun z => Work.PARIMPL.Ft c₀ z) Pa Pa := by
    rw [hPaeq]
    exact fl.mapsTo_Pa
  have hshift : ∀ z ∈ Pa, φa (Work.PARIMPL.Ft c₀ z) = φa z + 1 := by
    intro z hz
    rw [hPaeq] at hz
    have h := FF.shift z hz
    simpa [hφa_eq] using h
  have hv : ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ))
      = (φa (((fun c z => Work.PARIMPL.Ft c z) c₀)^[M.nIn] c₀)).re - (M.nIn : ℝ) := rfl
  have hcontN : ∀ N : ℕ, ContinuousAt (fun c : ℂ => ((fun c z => Work.PARIMPL.Ft c z) c)^[N] c) c₀ :=
    fun N => (Work.PARIMPL.continuous_orbit_diag N).continuousAt
  have hw := Work.PARIMPL2.exitTrackedWindow_of_lockstep (c₀ := c₀) (Nm := P.Nm)
    (trans := trans) (nIn := M.nIn) (Ft := fun c z => Work.PARIMPL.Ft c z) (Pa := Pa)
    (φa := φa) (Ψ := Ψ) (v := (φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ))
    hLS hmapsTo hshift hentry₀ hcrit hv (fun R => hblow (-R)) hcontN
  exact Work.PARIMPL2.escape_of_exitTrackedWindow (c₀ := c₀) (Nm := P.Nm) (trans := trans)
    (Ft := fun c z => Work.PARIMPL.Ft c z) (Ψ := Ψ) (x := x) (r := r) hw hr
    (hΨeq.symm ▸ fl.Ψ_diff.continuous) (fun c => rfl) hx hrob

/-- **The drive with the leak centre chosen by GATE2.**  The escape is derived
(`escapeAt_one` + `Work.PARIMPL.robust_of_greenOpen` + NAKANE's `greenEscapeOpen`), so the only
inputs beyond PARIMPL's data, the flower facts, `hSat`, the transit facts and PARIMPL2's
`LockstepAll` are `DeepLeak c₀ fl.Ψ xLeak` and the two exit-loop families at `xLeak` and
`xLeak + 1/2`. -/
theorem twoSided_of_deepLeak {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    (trans : ℂ → ℂ) {xLeak : ℝ}
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (him : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, (trans c).im = 0)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hG : Work.PARIMPL.GreenEscapeOpen)
    (hDL : DeepLeak c₀ fl.Ψ xLeak)
    (hE₁ : ∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (ExitLoop c₀ fl.Ψ xLeak r₀ v Work.EL.alpha1))
    (hE₂ : ∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (ExitLoop c₀ fl.Ψ (xLeak + 1 / 2) r₀ v Work.EL.alpha2)) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨rd, hrd, hdeepD, hdisc₁, hdisc₂⟩ := hDL
  obtain ⟨R₁, hR₁, hgen₁⟩ := hE₁
  obtain ⟨R₂, hR₂, hgen₂⟩ := hE₂
  set r : ℝ := min R₁ (min R₂ rd) with hrdef
  have hrpos : 0 < r := lt_min hR₁ (lt_min hR₂ hrd)
  have hrR₁ : r ≤ R₁ := min_le_left _ _
  have hrR₂ : r ≤ R₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrrd : r ≤ rd := le_trans (min_le_right _ _) (min_le_right _ _)
  have hdeep : xLeak + r / 2 < -(3 / 2 : ℝ) := by linarith
  have hdisc1 : ∀ z ∈ Metric.closedBall ((xLeak : ℝ) : ℂ) r, fl.Ψ z ∉ Work.EL.K c₀ := by
    intro z hz
    refine hdisc₁ z ?_
    rw [Metric.mem_closedBall] at hz ⊢
    exact le_trans hz hrrd
  have hdisc2 : ∀ z ∈ Metric.closedBall (((xLeak + 1 / 2 : ℝ)) : ℂ) r, fl.Ψ z ∉ Work.EL.K c₀ := by
    intro z hz
    refine hdisc₂ z ?_
    rw [Metric.mem_closedBall] at hz ⊢
    exact le_trans hz hrrd
  have hrob1 : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall ((xLeak : ℝ) : ℂ) r, dist y (Ψ z) ≤ ρ) →
        y ∉ Work.EL.K c := by
    have h := Work.PARIMPL.robust_of_greenOpen (Ψ := Ψ) (hΨeq.symm ▸ fl.Ψ_diff.continuous) hG (xstar := xLeak)
      (j₀ := 0) (r₀ := r) hrpos (fun z hz => Work.PARIMPL.green_pos_of_notMem_K (by
        rw [hΨeq]
        exact hdisc1 z (by rw [Metric.mem_closedBall] at hz ⊢; simpa using hz)))
    simpa using h
  have hrob2 : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall (((xLeak + 1 / 2 : ℝ)) : ℂ) r, dist y (Ψ z) ≤ ρ) →
        y ∉ Work.EL.K c := by
    have h := Work.PARIMPL.robust_of_greenOpen (Ψ := Ψ) (hΨeq.symm ▸ fl.Ψ_diff.continuous) hG
      (xstar := xLeak + 1 / 2) (j₀ := 0) (r₀ := r) hrpos (fun z hz =>
        Work.PARIMPL.green_pos_of_notMem_K (by
          rw [hΨeq]
          exact hdisc2 z (by rw [Metric.mem_closedBall] at hz ⊢; simpa using hz)))
    simpa using h
  obtain ⟨ρ₁, hρ₁, hesc₁⟩ := escapeAt_one (fl := fl) FF trans hPaeq hφa_eq hΨeq hentry₀ hcrit hLS
    (fun b => hblow b) (x := xLeak) (r := r) hrpos (by linarith) hrob1
  obtain ⟨ρ₂, hρ₂, hesc₂⟩ := escapeAt_one (fl := fl) FF trans hPaeq hφa_eq hΨeq hentry₀ hcrit hLS
    (fun b => hblow b) (x := xLeak + 1 / 2) (r := r) hrpos (by linarith) hrob2
  have hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ (min ρ₁ ρ₂), ∀ y : ℝ,
      (y = xLeak ∨ y = xLeak + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < r / 2 → c ∉ Mandelbar := by
    intro c hc y hy hd
    rcases hy with rfl | rfl
    · exact hesc₁ c ⟨hc.1, Metric.ball_subset_ball (min_le_left _ _) hc.2⟩ hd
    · exact hesc₂ c ⟨hc.1, Metric.ball_subset_ball (min_le_right _ _) hc.2⟩ hd
  exact twoSided_trans_of_lockstepAllAt (d := d) (T := T) FF xLeak r hrpos trans hOpen hfront hPaeq hφa_eq
    hΨeq hentry₀ hcrit hSat hρc hcont hρh
    (fun c hc => by rw [him c hc]; simp [abs_zero]; positivity)
    hblowup (lt_min hρ₁ hρ₂) hesc hblow hLS
    (hgen₁ r ⟨hrpos, hrR₁⟩ _).some (hgen₂ r ⟨hrpos, hrR₂⟩ _).some

end Work.GATE2
