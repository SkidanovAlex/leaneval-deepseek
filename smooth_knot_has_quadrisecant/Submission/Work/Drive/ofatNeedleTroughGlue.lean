import Mathlib
import Submission.Work.Drive.ofatNeedleEnd

/-!
# The endgame glue with the needle slice *prescribed*

`Work.Drive.unknotted_of_needleEndEps_noHav` (`Drive/ofatNeedleEnd.lean`) consumes its top end in the
form `htop : ∀ δ, ∀ ε ∈ (0,1/2), ∀ Δ, ∃ …` — the needle slice `ε` is chosen *inside* that theorem (as
`ε₁/2` of the needle-end constant).  The `OFat` endgame, however, must run the top end at a slice
`ε` **in the bottom trough of the schedule** (`4 * schedC D σ ≤ δs` on the blur window of `ε`), so
that the blurred scheduled slice *is* the standard needle
(`Work.Drive.sweepFamOf_schedLoop_eq_needle`).  That slice is a small number of its own, not
necessarily `ε₁/2`.

This module records the same glue with `ε` a **prescribed** parameter: it is the body of
`unknotted_of_needleEndEps_noHav` with `ε₁/2` replaced by the given `ε` (which only has to satisfy
`0 < ε`, `ε < 1/2` and `ε ≤ ε₁`, the needle end's own cap).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The endgame glue at a prescribed needle slice.**  `htop` is the top end *at the fixed slice
`ε`* (ending at `sweepNeedleFam r D lam δ₁ δ₂ ε`), `hneedle` the needle end (valid for every slice
`ε' ≤ ε₁`), and `hεε₁ : ε ≤ ε₁` places the prescribed slice inside the needle end's range. -/
theorem unknotted_of_needleTrough {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d)
    (hV : ∀ sg : ℝ, 0 < sg → sg < 1 → r (Work.Drive.taR D sg) ≠ r (Work.Drive.tbR D sg))
    (hntB : ∀ sg : ℝ, 0 < sg → sg < 1 →
      cross3 (r (Work.Drive.tbR D sg) - r (Work.Drive.taR D sg))
        (velocity r (Work.Drive.tbR D sg)) ≠ 0)
    (hntA : ∀ sg : ℝ, 0 < sg → sg < 1 →
      cross3 (r (Work.Drive.tbR D sg) - r (Work.Drive.taR D sg))
        (velocity r (Work.Drive.taR D sg)) ≠ 0)
    {ε : ℝ} (hεpos : 0 < ε) (hεhalf : ε < 1 / 2)
    (htop : ∀ δ : ℝ, 0 < δ → ∀ Δ : ℝ, 0 < Δ →
      ∃ (lam δ₁ δ₂ : ℝ) (r0 : ℝ → Space) (H : ℝ → ℝ → Space),
        (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ δ₂ ≤ ε / 2 ∧
          lam ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ) ∧
        IsSmoothKnot r0 ∧
        (∀ t : ℝ, ‖r0 t - r t‖ < δ ∧ ‖velocity r0 t - velocity r t‖ < δ) ∧
        ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧
        (∀ s t : ℝ, H (t + period) s = H t s) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => H t s)) ∧
        (∀ t : ℝ, H t 0 = r0 t) ∧
        (∀ t : ℝ, H t 1 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε t))
    (hneedle : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 / 2 ∧ ε ≤ ε₁ ∧
      ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₁ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε' / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε' t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0) :
    IsUnknotted r := by
  obtain ⟨δ, hδpos, hδcl⟩ := Work.Drive.isUnknotted_of_close hr
  obtain ⟨ε₁, hε₁0, hε₁1, hεε₁', hneedle'⟩ := hneedle
  obtain ⟨Λ, hΛpos, htail⟩ := hneedle' ε hεpos hεε₁'
  obtain ⟨lam, δ₁, δ₂, r0, H, hpar, hr0, hclose, hHsm, hHper, hHsl, hH0, hH1⟩ :=
    htop δ hδpos Λ hΛpos
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpar
  obtain ⟨c, f1, f2, R, F, hFsm, hFper, hFsl, hF0, hF1, hR, hf1, hf2, hperp⟩ :=
    htail lam δ₁ δ₂ h1 h6 h2 h3 h7 h4 h8 h5
  have hjun : ∀ t : ℝ, H t 1 = F t 0 := fun t => by rw [hH1 t, hF0 t]
  have hglue := Work.Drive.sweepGlue_clauses hHsm hFsm hjun hHsl hFsl hHper hFper
  have hcircU : IsUnknotted (fun t : ℝ => c + R • (Real.cos t • f1 + Real.sin t • f2)) :=
    Work.Drive.framedStarShapedPolarGraph c f1 f2 hf1 hf2 hperp contDiff_const (fun _ => rfl)
      (fun _ => hR) contDiff_id (fun _ => rfl) (fun t => by simpa using deriv_id'' (x := t))
  have hcircS : IsSmoothKnot (fun t : ℝ => c + R • (Real.cos t • f1 + Real.sin t • f2)) :=
    Work.Drive.polarCircle_isSmoothKnot hR hf1 hf2 hperp
  have hU : IsUnknotted r0 :=
    Work.Drive.cInfKnotPath_to_unknotted hr0 hcircS hcircU
      (F := fun t s : ℝ => Work.Drive.sweepGlue H F s t) hglue.1 hglue.2.1
      (fun t => by rw [hglue.2.2.2.1 t, hH0 t])
      (fun t => by rw [hglue.2.2.2.2 t, hF1 t]) hglue.2.2.1
  exact hδcl r0 hr0 hclose hU

end Work.Drive
