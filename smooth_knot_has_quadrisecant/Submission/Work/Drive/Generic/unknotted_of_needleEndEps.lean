import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.sweepGlue_clauses
import Submission.Work.Drive.cInfKnotPath_to_unknotted
import Submission.Work.Drive.framedStarShapedPolarGraph
import Submission.Work.Drive.polarCircle_isSmoothKnot
import Submission.Work.Drive.isUnknotted_of_close
import Submission.CollinearityMap

/-!
# The endgame of the chord sweep with a **prescribed** needle parameter and a per-`ε` budget

`Work.Generic.unknotted_of_hnt_arc` glues

* the top end `Work.Generic.sweepToNeedleBoundedNT` (a family from a `C¹`-close `r0` to the needle at
  the *produced* parameters `(lam, δ₁, δ₂, ε)`), and
* the needle end (`hneedle : ∃ ε₀ L, ∀ box …`),

and concludes `IsUnknotted r`.  Its quantifier order, however, fixes the width budget before the
needle size appears, which is not enough for the angular-velocity estimate of the needle (whose
margin is of size `~ ε³` against a blur mismatch of size `~(ε δ₁ + δ₂)²`).

This module records the same endgame with the corrected quantifiers:

* `htop` is `Work.Drive.sweepToNeedleEps` (the top end with the needle size `ε` **prescribed** by the
  caller, and the widths then freely chosen below any `Δ`), and
* `hneedle` is the needle end **for a prescribed `ε`, with an `ε`-dependent budget**:
  `∀ ε ∈ (0, 1/2), ∃ Λ > 0, ∀ lam δ₁ δ₂ ≤ Λ with δ₂ ≤ ε/2, …`.

Both are stated for a *concrete* band arc `D`, so the module uses only the top-end vocabulary
(`Work.Drive.sweepNeedleFam`) and not the needle-chart one.

The proof is the proof of `Work.Generic.unknotted_of_hnt_arc` with the needle size fixed at `1/4`
(any value in `(0, 1/2)` works) and the width budget taken after it.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant

open LeanEval.KnotTheory.Quadrisecant in
/-- **The endgame with a prescribed needle parameter and an `ε`-dependent width budget.** -/
theorem unknotted_of_needleEndEps {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    (hV : ∀ sg : ℝ, 0 < sg → sg < 1 → r (Work.Drive.taR D sg) ≠ r (Work.Drive.tbR D sg))
    (hntB : ∀ sg : ℝ, 0 < sg → sg < 1 →
      cross3 (r (Work.Drive.tbR D sg) - r (Work.Drive.taR D sg))
        (velocity r (Work.Drive.tbR D sg)) ≠ 0)
    (hntA : ∀ sg : ℝ, 0 < sg → sg < 1 →
      cross3 (r (Work.Drive.tbR D sg) - r (Work.Drive.taR D sg))
        (velocity r (Work.Drive.taR D sg)) ≠ 0)
    (htop : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ Δ : ℝ, 0 < Δ →
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
    (hneedle : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 / 2 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0) :
    IsUnknotted r := by
  -- the `C¹`-openness radius of unknottedness at `r`
  obtain ⟨δ, hδpos, hδcl⟩ := Work.Drive.isUnknotted_of_close hr
  -- the prescribed needle size and the width budget that the needle end allows for it
  obtain ⟨ε₁, hε₁0, hε₁1, hneedle'⟩ := hneedle
  have hε0 : (0 : ℝ) < ε₁ / 2 := by linarith
  have hε1 : ε₁ / 2 < 1 / 2 := by linarith
  have hε1' : ε₁ / 2 ≤ ε₁ := by linarith
  obtain ⟨Λ, hΛpos, htail⟩ := hneedle' (ε₁ / 2) hε0 hε1'
  -- the sweep down from `r` to a needle of exactly this size, with widths `≤ Λ`
  obtain ⟨lam, δ₁, δ₂, r0, H, hpar, hr0, hclose, hHsm, hHper, hHsl, hH0, hH1⟩ :=
    htop δ hδpos (ε₁ / 2) hε0 hε1 Λ hΛpos
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpar
  -- the needle end, at exactly these widths
  obtain ⟨c, f1, f2, R, F, hFsm, hFper, hFsl, hF0, hF1, hR, hf1, hf2, hperp⟩ :=
    htail lam δ₁ δ₂ h1 h6 h2 h3 h7 h4 h8 h5
  -- the two families agree at their junction (both are the needle)
  have hjun : ∀ t : ℝ, H t 1 = F t 0 := fun t => by rw [hH1 t, hF0 t]
  have hglue := Work.Drive.sweepGlue_clauses hHsm hFsm hjun hHsl hFsl hHper hFper
  -- the round circle is an analytic knot and is unknotted
  have hcircU : IsUnknotted (fun t : ℝ => c + R • (Real.cos t • f1 + Real.sin t • f2)) :=
    Work.Drive.framedStarShapedPolarGraph c f1 f2 hf1 hf2 hperp contDiff_const (fun _ => rfl)
      (fun _ => hR) contDiff_id (fun _ => rfl) (fun t => by simpa using deriv_id'' (x := t))
  have hcircS : IsSmoothKnot (fun t : ℝ => c + R • (Real.cos t • f1 + Real.sin t • f2)) :=
    Work.Drive.polarCircle_isSmoothKnot hR hf1 hf2 hperp
  -- propagate unknottedness along the glued family, then across `C¹`-closeness
  have hU : IsUnknotted r0 :=
    Work.Drive.cInfKnotPath_to_unknotted hr0 hcircS hcircU
      (F := fun t s : ℝ => Work.Drive.sweepGlue H F s t) hglue.1 hglue.2.1
      (fun t => by rw [hglue.2.2.2.1 t, hH0 t])
      (fun t => by rw [hglue.2.2.2.2 t, hF1 t]) hglue.2.2.1
  exact hδcl r0 hr0 hclose hU

end Work.Drive.Generic
