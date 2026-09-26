import Mathlib
import Submission.Work.Drive.shiftedNeedleChart
import Submission.Work.Drive.exists_needleChartFrame
import Submission.Work.Drive.shiftedNeedle_singleRay

/-!
# The chart pin from its parts: two obligations left

`Work.Drive.NeedleShiftedChartPin` (the geometric pin of the needle end of the low end) is, box by
box, the conjunction of

* the **frame**: a unit `(e, v)` with `e ⊥ v`, `v` the chord direction (`V = ‖V‖ • v`, `0 < ‖V‖`) and
  a strictly positive base height `0 < nHeight … e 0` — `Work.Drive.exists_needleChartFrame`
  (PROVED, given the base point is not on the chord's *line*),
* the **single-ray** condition — `Work.Drive.shiftedNeedle_singleRay` (PROVED),
* the **angular-velocity** condition — still open.

This module names the two hypotheses that the two proved bricks consume, and assembles the pin:

* `Work.Drive.NeedleShiftedNotOnLine r D` — `∀ s, needleFam … (period/4) ≠ (1−s)•chordEndA +
  s•chordEndB`.  This is `Work.Drive.needleArcChordSep_generic` at `t = period/4`; the module
  `Submission.Work.Drive.needleArcChordSep_generic` is currently unbuildable (another lane is
  rewriting `needleInjOn.lean`), hence the hypothesis.
* `Work.Drive.NeedleShiftedAngVel r D` — the angular-velocity condition in chart form: see
  `Submission/Work/Drive/NOTES_needleChartPin_SESSION.md` §1 item 3 (explicit on the chord zone, a
  cancellation on the chamfers, and the chart-coordinate concavity of the blurred profile on the arc
  zone — with the two warnings of §2).
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The base point is not on the chord's line.**  (`Work.Drive.needleArcChordSep_generic` at the
base parameter `period/4`, uniformly in the box.) -/
def NeedleShiftedNotOnLine (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
    ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
      0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
      ∀ s : ℝ, needleFam r D lam δ₁ δ₂ ε (period / 4) ≠
        (1 - s) • chordEndA r D δ₂ ε + s • chordEndB r D δ₂ ε

/-- **The angular-velocity obligation of the chart pin**, uniformly in the box.

The frame direction is *not* quantified over: the chart clause is stated for the **canonical** up
direction `e = ‖chartUp‖⁻¹ • chartUp` (the direction of the base point's offset from the chord's
line), because the `∀ e` form is **false** — `e` ranges over the half-circle of unit vectors `⊥ v`
with positive base height, and requiring the clause for all of them forces the component of
`X̃'(·)(N · − N 0) − X̃(·)N'` in the direction perpendicular to both `v` and the base offset to vanish
(two mathematicians, reviewing exactly that statement, showed it fails for any knot with nonzero
torsion at the base parameter).  See `NOTES_needleChartPin_SESSION.md` §6. -/
def NeedleShiftedAngVel (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
    ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
      0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
          = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v →
        ∀ y₀ : ℝ, 0 < y₀ → y₀ < ‖chartUp r D lam δ₁ δ₂ ε v‖ →
        ∀ t : ℝ,
          0 < (nHeight r D lam δ₁ δ₂ ε ((‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ •
                  chartUp r D lam δ₁ δ₂ ε v) t
                - nHeight r D lam δ₁ δ₂ ε ((‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ •
                  chartUp r D lam δ₁ δ₂ ε v) 0 + y₀) *
              deriv (nCoord r D lam δ₁ δ₂ ε v) t
            - (nCoord r D lam δ₁ δ₂ ε v t - nCoord r D lam δ₁ δ₂ ε v 0) *
              deriv (nHeight r D lam δ₁ δ₂ ε ((‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ •
                chartUp r D lam δ₁ δ₂ ε v)) t

/-- **The chart pin from the frame, the single ray and the angular velocity.** -/
theorem needleShiftedChartPin_of_parts {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    (hnotseg : NeedleShiftedNotOnLine r D) (hang : NeedleShiftedAngVel r D) :
    NeedleShiftedChartPin r D havoid := by
  obtain ⟨ε₁, L₁, hε₁, hL₁, hframe⟩ := exists_needleChartFrame hr D
  obtain ⟨ε₂, L₂, hε₂, hL₂, hray⟩ := shiftedNeedle_singleRay hr D
  obtain ⟨ε₃, L₃, hε₃, hL₃, hang'⟩ := hang
  obtain ⟨ε₄, L₄, hε₄, hL₄, hnos⟩ := hnotseg
  refine ⟨min (min ε₁ ε₂) (min ε₃ ε₄), min (min L₁ L₂) (min L₃ L₄),
    lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), lt_min (lt_min hL₁ hL₂) (lt_min hL₃ hL₄), ?_⟩
  intro lam δ₁ δ₂ ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hε₁' : ε ≤ ε₁ := le_trans h9 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε₂' : ε ≤ ε₂ := le_trans h9 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε₃' : ε ≤ ε₃ := le_trans h9 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₄' : ε ≤ ε₄ := le_trans h9 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hL₁' : lam ≤ L₁ := le_trans h2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hL₂' : lam ≤ L₂ := le_trans h2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hL₃' : lam ≤ L₃ := le_trans h2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hL₄' : lam ≤ L₄ := le_trans h2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ₁L₁ : δ₁ ≤ L₁ := le_trans h5 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₁L₂ : δ₁ ≤ L₂ := le_trans h5 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₁L₃ : δ₁ ≤ L₃ := le_trans h5 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₁L₄ : δ₁ ≤ L₄ := le_trans h5 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ₂L₁ : δ₂ ≤ L₁ := le_trans h7 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₂L₂ : δ₂ ≤ L₂ := le_trans h7 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₂L₃ : δ₂ ≤ L₃ := le_trans h7 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₂L₄ : δ₂ ≤ L₄ := le_trans h7 (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the frame brick supplies the chord direction `v` and `0 < ‖V‖` (its own `e` is discarded:
  -- the chart direction is the canonical one)
  obtain ⟨e₀, v, -, hv, hev₀, hVpos, hVv, hbase₀⟩ :=
    hframe lam δ₁ δ₂ ε h1 hL₁' h3 h4 hδ₁L₁ h6 hδ₂L₁ h8 hε₁' h10
      (hnos lam δ₁ δ₂ ε h1 hL₄' h3 h4 hδ₁L₄ h6 hδ₂L₄ h8 hε₄' h10)
  set u : Space := chartUp r D lam δ₁ δ₂ ε v with hu
  have hu_ne : u ≠ 0 := by
    intro h0
    have hc0 : chartUp r D lam δ₁ δ₂ ε v = 0 := by rw [← hu, h0]
    have hz : shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε
        = (nCoord r D lam δ₁ δ₂ ε v 0) • v := by
      have := hc0
      rw [chartUp] at this
      exact sub_eq_zero.mp this
    have hve₀ : inner ℝ v e₀ = 0 := by rw [real_inner_comm]; exact hev₀
    have hzero : inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) e₀ = 0 := by
      rw [hz, real_inner_smul_left, hve₀, mul_zero]
    rw [nHeight] at hbase₀
    linarith
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have he_ne : ‖u‖ ≠ 0 := ne_of_gt hu_pos
  have hnorm_e : ‖(‖u‖)⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), inv_mul_cancel₀ he_ne]
  have horth_e : inner ℝ ((‖u‖)⁻¹ • u) v = 0 := by
    rw [real_inner_smul_left, hu, inner_chartUp_v r D lam δ₁ δ₂ ε hv, mul_zero]
  have hu_inner : inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) u = ‖u‖ ^ 2 := by
    rw [hu]
    exact inner_shiftedNeedle_chartUp r D lam δ₁ δ₂ ε hv
  have hheight : nHeight r D lam δ₁ δ₂ ε ((‖u‖)⁻¹ • u) 0 = ‖u‖ := by
    rw [nHeight]
    exact inner_smul_unit_of_inner_eq _ _ hu_inner
  refine ⟨(‖u‖)⁻¹ • u, v, ‖u‖ / 2, hnorm_e, hv, horth_e, hVpos, hVv,
    by linarith, by rw [hheight]; linarith, ?_, ?_⟩
  · intro t ht0 htp hcoord
    exact hray lam δ₁ δ₂ ε h1 hL₂' h3 h4 hδ₁L₂ h6 hδ₂L₂ h8 hε₂' h10 _ v hnorm_e hv horth_e
      hVpos hVv _ (by linarith) (by rw [hheight]; linarith) t ht0 htp hcoord
  · intro t
    exact hang' lam δ₁ δ₂ ε h1 hL₃' h3 h4 hδ₁L₃ h6 hδ₂L₃ h8 hε₃' h10 v hv hVv _ (by linarith)
      (by rw [← hu]; linarith) t

end Work.Drive
