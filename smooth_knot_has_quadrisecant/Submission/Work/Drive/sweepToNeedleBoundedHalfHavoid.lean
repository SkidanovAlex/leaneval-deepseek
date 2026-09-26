import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.cInfKnot
import Submission.Work.Drive.sweepFam_contDiff_periodic
import Submission.Work.Drive.sweepToNeedleStrict
import Submission.Work.Drive.sweepFam_wideEnd_estimate_tol

namespace Work.Drive

/-!
# The top end of the chord sweep, from the *slices clause* or from the parameter selection

Two forms of the "(T)" pin of `Work.Drive.unknotted_of_avoidingArc`, both obtained from the
colleague's `Submission/Work/Drive/sweepToNeedleBoundedHalf.lean` (whose one broken import,
`Submission.Work.Drive.sweepFam_slices_knots_window`, is replaced here):

* `Work.Drive.sweepToNeedleBoundedHalf_of_hcomb` — the **general** form: the hypothesis is the whole
  parameter-selection clause `hcomb` that `Work.Drive.sweepToNeedleStrict` consumes (the widths, the
  reparametrisation `Θ`, the wide-end closeness *and* the slices clause on `[ε, σ₀]`).  This form is
  robust: it does not commit to any particular shape (coupled or not) of the slices clause, so it
  stays usable whatever the eventual proof of the slices clause provides.
* `Work.Drive.sweepToNeedleBoundedHalf_of_slices` — the specialisation in which the parameter
  selection is the proved wide-end estimate `Work.Drive.sweepFam_wideEnd_estimate_tol` and the
  hypothesis is the (uncoupled) **slices clause**
  `∃ L > 0, ∀ lam δ₁ δ₂ ≤ L, ∀ σ ∈ [ε,σ₀], InjOn (sweepFam … σ) (Ico 0 period) ∧ velocity · ≠ 0`.

Both conclusions are arranged to match *exactly* the `htop` bundle of
`Work.Drive.unknotted_of_avoidingArc_of_pins` (including `lam ≤ Δ` and `ε ≤ ε₀`, which the
colleague's statement drops but the wide-end estimate provides), and both are `sorry`-free and
axiom-clean.

**Why the `havoid` (rather than NT) form is the one needed here.**  The sibling
`Work.Generic.sweepToNeedleBoundedNT` / `Work.Drive.sweepToNeedleEps` obtain the slices clause from
the non-tangency hypotheses `hV`/`hntB`/`hntA`, which are **not** implied by the target's hypothesis
`NonSeparatingArcAvoidingO r`: a chord can be tangent at an endpoint without carrying a third knot
point (`y = x² - x³/2` on `[0,1]` has the tangent chord at `(1, 1/2)`, and the tangent-chord locus
is even a curve in the strip).

**Import class.**  This module imports `sweepFam_wideEnd_estimate_tol`, whose closure contains
`sweepFam_slices_knots` (class A, because of the duplicated `sweepLoopChamfer_continuous_t`), so it
cannot be imported by `Submission/Work/Drive/unknotted_of_avoidingArc.lean` (class B).  The final
glue needs either the removal of that clash (a rename in a colleague's file — see
`H2/NOTES_chamferZones_topEnd_SESSION.md` §5) or an AB/merged-universe copy; the statements here are
class-free.
-/

theorem sweepToNeedleBoundedHalf_of_slices {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      LeanEval.KnotTheory.Quadrisecant.mobiusCover
        ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉
        LeanEval.KnotTheory.Quadrisecant.trisecantSet r)
    (hsl : ∀ ε σ₀ : ℝ, 0 < ε → ε < σ₀ → σ₀ < 1 →
      ∃ L : ℝ, 0 < L ∧
        ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
          ∀ σ : ℝ, ε ≤ σ → σ ≤ σ₀ →
            Set.InjOn (fun t : ℝ => sweepFam r D lam δ₁ δ₂ σ t)
              (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) ∧
            (∀ t : ℝ, LeanEval.KnotTheory.Quadrisecant.velocity
              (fun t : ℝ => sweepFam r D lam δ₁ δ₂ σ t) t ≠ 0))
    {δ ε₀ Δ : ℝ} (hδ : 0 < δ) (hε₀ : 0 < ε₀) (hΔ : 0 < Δ) :
    ∃ (lam δ₁ δ₂ ε ε' : ℝ) (r0 : ℝ → LeanEval.KnotTheory.Quadrisecant.Space)
      (H : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space),
      (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ 0 < ε ∧ ε < ε' ∧ ε' < 1 ∧ ε < ε₀ ∧
        lam ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ ∧ ε ≤ ε₀ ∧ δ₂ ≤ ε / 2) ∧
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r0 ∧
      (∀ t : ℝ, ‖r0 t - r t‖ < δ ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r0 t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < δ) ∧
      ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧
      (∀ s t : ℝ, H (t + LeanEval.KnotTheory.Quadrisecant.period) s = H t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => H t s)) ∧
      (∀ t : ℝ, H t 0 = r0 t) ∧
      (∀ t : ℝ, H t 1 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε t) := by
  -- the structural clauses of the smoothed sweep (`Work.Drive.sweepFam_contDiff_periodic`)
  have hsm := fun (lam δ₁ δ₂ : ℝ) (h₁ : δ₁ ≠ 0) (h₂ : δ₂ ≠ 0) =>
    sweepFam_contDiff_periodic hr.continuous D lam δ₁ δ₂ h₁ h₂
  -- the parameter bundle required by `Work.Drive.sweepToNeedleStrict`
  have hcombGen : ∀ (εN LN ε₀ : ℝ), 0 < εN → 0 < LN → 0 < ε₀ →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∃ (lam δ₁ δ₂ ε ε' σ₀ c : ℝ) (Θ : ℝ → ℝ),
        (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ 0 < ε ∧ ε < ε' ∧ ε' < 1 ∧
          ε < ε₀ ∧ ε < σ₀ ∧ σ₀ < 1 ∧
          lam ≤ LN ∧ δ₁ ≤ LN ∧ δ₂ ≤ LN ∧ ε ≤ εN ∧ δ₂ ≤ ε / 2) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
        (∀ t : ℝ, Θ (t + LeanEval.KnotTheory.Quadrisecant.period)
          = Θ t + LeanEval.KnotTheory.Quadrisecant.period) ∧
        (∀ t : ℝ, 0 < deriv Θ t) ∧
        (∀ t : ℝ, ‖Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
        (∀ t : ℝ, ‖deriv (fun u : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) t
          - LeanEval.KnotTheory.Quadrisecant.velocity r (t + c)‖ < ε₁) ∧
        (∀ σ ∈ Set.Icc ε σ₀,
          Set.InjOn (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t)
            (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) ∧
          (∀ t : ℝ, LeanEval.KnotTheory.Quadrisecant.velocity
            (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t) t ≠ 0)) := by
    intro εN LN ε₀ hεN hLN hε₀ ε₁ hε₁
    obtain ⟨tol, _htolpos, htoldots, htolmain⟩ := sweepFam_wideEnd_estimate_tol hr D
    -- the sweep parameter, in `(1/2, 1)`, chosen so that `tol σ₀ < ε₁`
    obtain ⟨σ₀, _hσ₀half, hσ₀lt, hσ₀tol⟩ := htoldots ε₁ hε₁
    have hσ₀pos : (0 : ℝ) < σ₀ := by linarith
    -- the needle parameter, below both thresholds and below `σ₀`
    set ε : ℝ := min (min εN ε₀) σ₀ / 2 with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]
      have h : 0 < min (min εN ε₀) σ₀ := lt_min (lt_min hεN hε₀) hσ₀pos
      linarith
    have hεNle : ε ≤ εN := by
      rw [hεdef]
      have h1 : min (min εN ε₀) σ₀ ≤ min εN ε₀ := min_le_left _ _
      have h2 : min εN ε₀ ≤ εN := min_le_left _ _
      linarith
    have hε₀le : ε ≤ ε₀ := by
      rw [hεdef]
      have h1 : min (min εN ε₀) σ₀ ≤ min εN ε₀ := min_le_left _ _
      have h2 : min εN ε₀ ≤ ε₀ := min_le_right _ _
      linarith
    have hε₀half : ε ≤ ε₀ / 2 := by
      rw [hεdef]
      have h1 : min (min εN ε₀) σ₀ ≤ min εN ε₀ := min_le_left _ _
      have h2 : min εN ε₀ ≤ ε₀ := min_le_right _ _
      linarith
    have hεσ₀ : ε < σ₀ := by
      rw [hεdef]
      have h1 : min (min εN ε₀) σ₀ ≤ σ₀ := min_le_right _ _
      linarith
    -- the slices threshold on the window `[ε, σ₀]`
    obtain ⟨L, hLpos, hL⟩ := hsl ε σ₀ hεpos hεσ₀ hσ₀lt
    -- the wide-end estimate, with the parameters forced below `min L LN (ε/4)`
    set Lc : ℝ := min (min L LN) (min (ε / 4) (1 / 4)) with hLcdef
    have hLcpos : 0 < Lc := by
      rw [hLcdef]
      exact lt_min (lt_min hLpos hLN) (lt_min (by linarith) (by norm_num))
    obtain ⟨lam, δ₁, δ₂, c, Θ, hlam0, hlamL, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hΘsm, hΘshift,
      hΘderiv, hΘ1, hΘ2⟩ := htolmain σ₀ hσ₀lt ε₁ hσ₀tol Lc hLcpos
    have hlam_half : lam < 1 / 2 := by
      have h1 : lam ≤ 1 / 4 := (hlamL.trans (min_le_right _ _)).trans (min_le_right _ _)
      linarith
    have hlam_le : lam ≤ L := ((hlamL.trans (min_le_left _ _)).trans (min_le_left _ _))
    have hδ₁_le : δ₁ ≤ L := ((hδ₁L.trans (min_le_left _ _)).trans (min_le_left _ _))
    have hδ₂_le : δ₂ ≤ L := ((hδ₂L.trans (min_le_left _ _)).trans (min_le_left _ _))
    have hlam_LN : lam ≤ LN := (hlamL.trans (min_le_left _ _)).trans (min_le_right _ _)
    have hδ₁_LN : δ₁ ≤ LN := (hδ₁L.trans (min_le_left _ _)).trans (min_le_right _ _)
    have hδ₂_LN : δ₂ ≤ LN := (hδ₂L.trans (min_le_left _ _)).trans (min_le_right _ _)
    have hδ₂_eps : δ₂ ≤ ε / 4 :=
      (hδ₂L.trans (min_le_right _ _)).trans (min_le_left _ _)
    set ε' : ℝ := (1 + ε) / 2 with hε'def
    refine ⟨lam, δ₁, δ₂, ε, ε', σ₀, c, Θ, ⟨hlam0, hlam_half, hδ₁0, hδ₂0, hεpos, ?_, ?_, ?_,
      hεσ₀, hσ₀lt, hlam_LN, hδ₁_LN, hδ₂_LN, hεNle, by linarith⟩, hΘsm, hΘshift, hΘderiv,
      hΘ1, hΘ2, ?_⟩
    · rw [hε'def]; linarith
    · rw [hε'def]; linarith
    · linarith
    · intro σ hσ
      exact hL lam δ₁ δ₂ hlam0 hlam_le hδ₁0 hδ₁_le hδ₂0 hδ₂_le σ hσ.1 hσ.2
  have hcomb := hcombGen 1 Δ ε₀ (by norm_num) hΔ hε₀
  obtain ⟨lam, δ₁, δ₂, ε, ε', r0, H, hb, hr0, hclose, hj, hper, hslc, h0, h1⟩ :=
    sweepToNeedleStrict (r := r) hr (D := D) havoid (δ := δ) (ε₀ := ε₀) (εN := 1) (LN := Δ)
      hδ hε₀ (by norm_num) hΔ hsm hcomb
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, _l12, l13⟩ := hb
  exact ⟨lam, δ₁, δ₂, ε, ε', r0, H,
    ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, le_of_lt l8, l13⟩,
    hr0, hclose, hj, hper, hslc, h0, h1⟩


/-- **The top end from the parameter-selection clause itself.**  `hcomb` is exactly the clause
consumed by `Work.Drive.sweepToNeedleStrict` (widths, reparametrisation `Θ` and the slices clause on
`[ε,σ₀]`); no shape of the slices clause is assumed, so this form stays usable for any (coupled or
uncoupled) proof of it. -/
theorem sweepToNeedleBoundedHalf_of_hcomb {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      LeanEval.KnotTheory.Quadrisecant.mobiusCover
        ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉
        LeanEval.KnotTheory.Quadrisecant.trisecantSet r)
    (hcomb : ∀ (εN LN ε₀ : ℝ), 0 < εN → 0 < LN → 0 < ε₀ →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∃ (lam δ₁ δ₂ ε ε' σ₀ c : ℝ) (Θ : ℝ → ℝ),
        (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ 0 < ε ∧ ε < ε' ∧ ε' < 1 ∧
          ε < ε₀ ∧ ε < σ₀ ∧ σ₀ < 1 ∧
          lam ≤ LN ∧ δ₁ ≤ LN ∧ δ₂ ≤ LN ∧ ε ≤ εN ∧ δ₂ ≤ ε / 2) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
        (∀ t : ℝ, Θ (t + LeanEval.KnotTheory.Quadrisecant.period)
          = Θ t + LeanEval.KnotTheory.Quadrisecant.period) ∧
        (∀ t : ℝ, 0 < deriv Θ t) ∧
        (∀ t : ℝ, ‖Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
        (∀ t : ℝ, ‖deriv (fun u : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) t
          - LeanEval.KnotTheory.Quadrisecant.velocity r (t + c)‖ < ε₁) ∧
        (∀ σ ∈ Set.Icc ε σ₀,
          Set.InjOn (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t)
            (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) ∧
          (∀ t : ℝ, LeanEval.KnotTheory.Quadrisecant.velocity
            (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t) t ≠ 0)))
    {δ ε₀ Δ : ℝ} (hδ : 0 < δ) (hε₀ : 0 < ε₀) (hΔ : 0 < Δ) :
    ∃ (lam δ₁ δ₂ ε ε' : ℝ) (r0 : ℝ → LeanEval.KnotTheory.Quadrisecant.Space)
      (H : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space),
      (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ 0 < ε ∧ ε < ε' ∧ ε' < 1 ∧ ε < ε₀ ∧
        lam ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ ∧ ε ≤ ε₀ ∧ δ₂ ≤ ε / 2) ∧
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r0 ∧
      (∀ t : ℝ, ‖r0 t - r t‖ < δ ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r0 t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < δ) ∧
      ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧
      (∀ s t : ℝ, H (t + LeanEval.KnotTheory.Quadrisecant.period) s = H t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => H t s)) ∧
      (∀ t : ℝ, H t 0 = r0 t) ∧
      (∀ t : ℝ, H t 1 = Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε t) := by
  have hsm := fun (lam δ₁ δ₂ : ℝ) (h₁ : δ₁ ≠ 0) (h₂ : δ₂ ≠ 0) =>
    sweepFam_contDiff_periodic hr.continuous D lam δ₁ δ₂ h₁ h₂
  have hcomb' := hcomb 1 Δ ε₀ (by norm_num) hΔ hε₀
  obtain ⟨lam, δ₁, δ₂, ε, ε', r0, H, hb, hr0, hclose, hj, hper, hslc, h0, h1⟩ :=
    sweepToNeedleStrict (r := r) hr (D := D) havoid (δ := δ) (ε₀ := ε₀) (εN := 1) (LN := Δ)
      hδ hε₀ (by norm_num) hΔ hsm hcomb'
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, _l12, l13⟩ := hb
  exact ⟨lam, δ₁, δ₂, ε, ε', r0, H,
    ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, le_of_lt l8, l13⟩,
    hr0, hclose, hj, hper, hslc, h0, h1⟩


end Work.Drive
