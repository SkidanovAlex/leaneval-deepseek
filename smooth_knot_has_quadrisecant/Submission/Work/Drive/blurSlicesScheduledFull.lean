import Mathlib
import Submission.Work.Drive.blurSlicesScheduled
import Submission.Work.Drive.chamferJunctionDefs

/-!
# The **complete** slices clause of the scheduled blur

`NOTES_LEAD_scheduledBlur.md` §3 asks for the final statement of the blur layer: for a compact window
`[a,b] ⊂ (0,1)` there are scheduling parameters and a width budget `L ≤ a/2`, `L ≤ (1-b)/2` such that
every slice of the double blur of the scheduled loop is injective on one period with nowhere-vanishing
velocity.

This module states it as the composition of the two layers:

* the **geometric** layer, packaged here as `Work.Drive.SchedSlot` — the scheduling parameters
  `(lay, ρ₀, cQ)` together with the **injectivity of the raw scheduled loop** and the
  **junction non-degeneracy** `Work.Drive.ChamferJunctionOK` on the **clamped** window
  `[a/2, (1+b)/2]`.  Producer: `Work.Drive.chamferLoopGenInjOnScheduledC` (PROVED,
  `chamferLoopGenInjOnScheduledC.lean`) applied with the window `(a/2, (1+b)/2)`, whose conclusion is
  exactly this statement save for the `(a,b) → (a/2,(1+b)/2)` substitution;
* the **analytic** layer, `Work.Drive.chamferLoopGen_blurSlices_of_localCone'`
  (`blurSlicesScheduled.lean`, this lane), which turns the local cone — produced from
  `ChamferJunctionOK` by `Work.Drive.chamferLoopGen_localCone` (the note's §2) — and the raw
  injectivity into the blurred-slices clause (via the blur package
  `Work.Drive.sweepFamOf_slices_of_localCone_window`).

**Dependency note.**  The cone producer *is not imported*: it is taken as the hypothesis `hcone` of
`Work.Drive.blurSlices_of_schedSlot` (in the schedule-generic form), so that this file is
`sorry`-free and axiom-clean.  The pin `Work.Drive.chamferLoopGen_localCone`
(`chamferLoopGen_localCone.lean`) instantiates `hcone` in one line; the docstring of
`blurSlices_of_schedSlot` spells the instantiation out (`ContinuousAt` of the schedules comes from
`Work.Drive.continuousAt_schedAlpha` / `continuousAt_schedBeta`).
-/

noncomputable section

set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The scheduling slot.**  The scheduling parameters of the scheduled chamfer loop, together with
the two *geometric* clauses on the **clamped** window `[a/2, (1+b)/2]` that the analytic blur layer
consumes: the injectivity on one period of the *raw* scheduled loop, and the junction
non-degeneracy `Work.Drive.ChamferJunctionOK`.

Producer: `Work.Drive.chamferLoopGenInjOnScheduledC` with the window `(a/2, (1+b)/2)` (the shift is
what makes the `σ`-blur window of a slice `σ ∈ [a,b]` stay in the clamped range). -/
def SchedSlot (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (δs Lmax a b : ℝ) : Prop :=
  ∃ lay ρ₀ cQ : ℝ, 0 < lay ∧ lay ≤ Lmax ∧ lay ≤ 1 / 4 ∧ 0 < ρ₀ ∧ 0 < cQ ∧ cQ ≤ 1 ∧
    ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2),
      Set.InjOn (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
          (schedBeta r lay ρ₀ δs cQ D) σ) (Set.Ico (0 : ℝ) period) ∧
      ChamferJunctionOK r D (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) σ

/-- **The complete slices clause of the scheduled blur.**  From a scheduling slot on the clamped
window, the double blur `Work.Drive.sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ` of the scheduled
loop is injective on one period with nowhere-vanishing velocity for all small widths, uniformly over
the window `[a,b]`, with the width budget `L ≤ a/2`, `L ≤ (1-b)/2`. -/
theorem blurSlices_of_schedSlot {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {δs Lmax a b : ℝ} (hδs : 0 < δs) (hLmax : 0 < Lmax)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (h : SchedSlot r D δs Lmax a b)
    (hcone : ∀ (lay ρ₀ cQ : ℝ), 0 < lay → lay ≤ 1 / 4 → 0 < ρ₀ → 0 < cQ →
      (∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2),
        ChamferJunctionOK r D (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) σ) →
      ∀ σ₀ ∈ Set.Icc (a / 2) ((1 + b) / 2), ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
        ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
          ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
            c * (t₂ - t₁) ≤ inner ℝ n
              (schedLoop r D lay ρ₀ δs cQ s t₂ - schedLoop r D lay ρ₀ δs cQ s t₁)) :
    ∃ lay ρ₀ cQ : ℝ, 0 < lay ∧ lay ≤ Lmax ∧ lay ≤ 1 / 4 ∧ 0 < ρ₀ ∧ 0 < cQ ∧ cQ ≤ 1 ∧
      ∃ L : ℝ, 0 < L ∧ L ≤ a / 2 ∧ L ≤ (1 - b) / 2 ∧
        ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
          Set.InjOn (fun t : ℝ => sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ t)
            (Set.Ico (0 : ℝ) period) ∧
          ∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ t)
            t ≠ 0 := by
  obtain ⟨lay, ρ₀, cQ, hlay0, hlayL, hlay, hρ₀, hcQ0, hcQ1, hIJ⟩ := h
  have hLne : ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2), ‖r (tbR D σ) - r (taR D σ)‖ ≠ 0 := by
    obtain ⟨δ, hδpos, hδ⟩ := sweepFamChord_lower_bound hr D (a := a / 2) (b := (1 + b) / 2)
      (by linarith) (by linarith) (by linarith)
    exact fun σ hσ => ne_of_gt (lt_of_lt_of_le hδpos (hδ σ hσ))
  have hWne : ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2), sweepW' D σ ≠ 0 := fun σ hσ =>
    ne_of_gt (sweepW'_pos_lt D (by linarith [ha, hσ.1]) (by linarith [hb, hσ.2])).1
  obtain ⟨L, hL, hLa, hLb, hmain⟩ :=
    chamferLoopGen_blurSlices_of_localCone' hr D hlay0 hlay hδs ha hab hb
      (fun σ₀ hσ₀ t₀ ht₀ => hcone lay ρ₀ cQ hlay0 hlay hρ₀ hcQ0 (fun σ hσ => (hIJ σ hσ).2)
        σ₀ hσ₀ t₀ ht₀)
      (fun s hs => (hIJ s hs).1)
  exact ⟨lay, ρ₀, cQ, hlay0, hlayL, hlay, hρ₀, hcQ0, hcQ1, L, hL, hLa, hLb, hmain⟩

/-- **The per-layout form of the blurred-slices clause.**  For a consumer that chooses the layout
`lay` (and the schedules' other parameters `ρ₀, δs, cQ`) *before* the widths — the order of
`Work.Drive.sweepToNeedleEpsOfSlices_gen`, whose slices hypothesis is used at a single, previously
chosen `lay` — the blur layer gives its **own**, `lay`-dependent width budget `L = L(lay)`.  No
uniformity of `L` in `lay` is claimed (and none is available: the junction `J2` of the truncated loop
degenerates as `lay → 0`, so `L(lay) ≲ lay`; see `NOTES_blurPackage_SESSION.md` §9).

The hypotheses are the schedule-generic raw facts at each `lay`: the injectivity on one period of the
raw scheduled loop, the junction non-degeneracy `ChamferJunctionOK`, and the pointwise local cone. -/
theorem chamferLoopGen_blurSlices_perLay {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {ρ₀ δs cQ Lmax a b : ℝ} (hδs : 0 < δs)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hslot : ∀ lay ∈ Set.Ioc (0 : ℝ) Lmax, lay ≤ 1 / 4 →
      ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2),
        Set.InjOn (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
            (schedBeta r lay ρ₀ δs cQ D) σ) (Set.Ico (0 : ℝ) period) ∧
        ChamferJunctionOK r D (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) σ)
    (hcone : ∀ lay ∈ Set.Ioc (0 : ℝ) Lmax, lay ≤ 1 / 4 →
      ∀ σ₀ ∈ Set.Icc (a / 2) ((1 + b) / 2), ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
        ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
          ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
            c * (t₂ - t₁) ≤ inner ℝ n
              (schedLoop r D lay ρ₀ δs cQ s t₂ - schedLoop r D lay ρ₀ δs cQ s t₁)) :
    ∀ lay ∈ Set.Ioc (0 : ℝ) Lmax, lay ≤ 1 / 4 →
      ∃ L : ℝ, 0 < L ∧ L ≤ a / 2 ∧ L ≤ (1 - b) / 2 ∧
        ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
          Set.InjOn (fun t : ℝ => sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ t)
            (Set.Ico (0 : ℝ) period) ∧
          ∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ t)
            t ≠ 0 :=
  fun lay hlay hlay4 => chamferLoopGen_blurSlices_of_localCone' hr D hlay.1 hlay4 hδs ha hab hb
    (hcone lay hlay hlay4) (fun s hs => (hslot lay hlay hlay4 s hs).1)

end Work.Drive
