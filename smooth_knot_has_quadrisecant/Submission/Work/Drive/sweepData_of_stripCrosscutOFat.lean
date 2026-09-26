import Mathlib
import Submission.Helpers
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.chordSweepDefs

/-!
# From the `E3` crosscut to the sweep data of the endgame

`Work.Drive.crosscut_or_spreadQuad'`s second branch is a bottom–top crosscut `γ` of the period strip
avoiding `OFatObstruction r ρ = OFatR r ρ ∪ TCset r`.  The endgame `E1`/`E4` of the lead's
`OFat` design consumes a **band arc** together with its `SweepData` (`Work.Drive.SweepData`: the two
continuous lifts `ta`, `tb` of the chord's endpoints, with `ta 0 = tb 0` and `tb 1 = ta 1 + period`).

This module performs that conversion, and it transfers the avoidance in the form the chamfer analysis
uses:

* `∀ s ∈ (0,1), ∀ u, ta s + ρ ≤ u → u ≤ tb s - ρ → r u ∉ openSegment ℝ (r (ta s)) (r (tb s))` —
  there is **no retained middle fat at scale `ρ`**: every middle of the retained arc is
  *corner-local* (within `ρ` of an endpoint);
* the chord at parameter `s` is tangent at **neither** endpoint
  (`cross3 (r (tb s) - r (ta s)) (velocity r (ta s)) ≠ 0` and the mirror) — this is the
  non-tangency `hntA`/`hntB` of the sweep.

The `SweepData` is the obvious one: `ta s = (γ s).1`, `tb s = (γ s).1 + (γ s).2`; the two endpoint
conditions are `(γ 0).2 = 0` and `(γ 1).2 = period`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

open scoped unitInterval

/-- **The band arc and its `SweepData` attached to an `E3` crosscut, with the avoidance.** -/
theorem bandArcData_sweepData_of_stripCrosscutOFat {r : ℝ → Space} {ρ : ℝ}
    (γ : C(I, ℝ × ℝ)) (hbot : (γ 0).2 = 0) (htop : (γ 1).2 = period)
    (hint : ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < (γ t).2 ∧ (γ t).2 < period)
    (havoid : ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∉ OFatObstruction r ρ) :
    ∃ d : BandArcData, ∃ D : SweepData d, BandArcNonSeparating d ∧
      (∀ (s : I), ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
        ∀ u : ℝ, D.ta s + ρ ≤ u → u ≤ D.tb s - ρ →
          r u ∉ openSegment ℝ (r (D.ta s)) (r (D.tb s))) ∧
      (∀ (s : I), ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
        cross3 (r (D.tb s) - r (D.ta s)) (velocity r (D.ta s)) ≠ 0 ∧
        cross3 (r (D.tb s) - r (D.ta s)) (velocity r (D.tb s)) ≠ 0) := by
  classical
  set a : I → AddCircle period := fun s => ((γ s).1 : AddCircle period) with ha
  set b : I → AddCircle period :=
    fun s => (((γ s).1 + (γ s).2 : ℝ) : AddCircle period) with hb
  have hcont_a : Continuous a :=
    (AddCircle.continuous_mk' period).comp (continuous_fst.comp γ.continuous)
  have hcont_b : Continuous b :=
    (AddCircle.continuous_mk' period).comp
      ((continuous_fst.comp γ.continuous).add (continuous_snd.comp γ.continuous))
  have hleft : a 0 = b 0 := by
    show ((γ 0).1 : AddCircle period) = (((γ 0).1 + (γ 0).2 : ℝ) : AddCircle period)
    rw [hbot]
    simp
  have hright : a 1 = b 1 := by
    show ((γ 1).1 : AddCircle period) = (((γ 1).1 + (γ 1).2 : ℝ) : AddCircle period)
    rw [htop, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hoff : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → a s ≠ b s := by
    intro s hs0 hs1
    have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
    have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
    have hh := hint s hpos hlt
    show ((γ s).1 : AddCircle period) ≠ (((γ s).1 + (γ s).2 : ℝ) : AddCircle period)
    exact coe_ne_coe_of_lt hh.1 hh.2
  let d : BandArcData :=
    { a := a, b := b, cont_a := hcont_a, cont_b := hcont_b,
      collapse_left := hleft, collapse_right := hright, offdiag := hoff }
  let D : SweepData d :=
    { ta := fun s => (γ s).1
      tb := fun s => (γ s).1 + (γ s).2
      cont_ta := continuous_fst.comp γ.continuous
      cont_tb := (continuous_fst.comp γ.continuous).add (continuous_snd.comp γ.continuous)
      lift_a := fun s => rfl
      lift_b := fun s => rfl
      left_eq := by simp [hbot]
      right_eq := by rw [htop] }
  have hns : BandArcNonSeparating d :=
    ⟨D.ta, D.tb, D.cont_ta, D.cont_tb, D.lift_a, D.lift_b, D.left_eq, D.right_eq⟩
  refine ⟨d, D, hns, ?_, ?_⟩
  · intro s hs0 hs1 u hu1 hu2 hmem
    have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
    have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
    obtain ⟨hh1, hh2⟩ := hint s hpos hlt
    refine havoid s hpos hlt (Or.inl ?_)
    show 0 < (γ s).2 ∧ (γ s).2 < period ∧ ∃ u : ℝ, (γ s).1 + ρ ≤ u ∧
      u ≤ (γ s).1 + (γ s).2 - ρ ∧ r u ∈ openSegment ℝ (r (γ s).1) (r ((γ s).1 + (γ s).2))
    exact ⟨hh1, hh2, u, hu1, hu2, hmem⟩
  · intro s hs0 hs1
    have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
    have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
    obtain ⟨hh1, hh2⟩ := hint s hpos hlt
    have hnotA := havoid s hpos hlt
    have hTC : ¬ ((cross3 (r ((γ s).1 + (γ s).2) - r (γ s).1) (velocity r (γ s).1) = 0) ∨
        (cross3 (r ((γ s).1 + (γ s).2) - r (γ s).1) (velocity r ((γ s).1 + (γ s).2)) = 0)) := by
      intro h
      exact hnotA (Or.inr ⟨hh1, hh2, h⟩)
    have h1 : cross3 (r ((γ s).1 + (γ s).2) - r (γ s).1) (velocity r (γ s).1) ≠ 0 :=
      fun h => hTC (Or.inl h)
    have h2 : cross3 (r ((γ s).1 + (γ s).2) - r (γ s).1) (velocity r ((γ s).1 + (γ s).2)) ≠ 0 :=
      fun h => hTC (Or.inr h)
    exact ⟨h1, h2⟩

/-- **The cut arc misses the chord.**  If the retained middles of a `SweepData` are all within `ρ` of
an endpoint and the chamfer cuts the arc at depth `la ≥ ρ`, then no point of the *cut* arc
`[ta s + la, tb s - la]` lies on the chord of the slice.  This is the form in which the chamfer
analysis (`E1`) consumes the avoidance: after the cut, the arc part of the slice loop is
chord-free. -/
theorem sweepData_arc_no_chordPoint {r : ℝ → Space} {ρ la : ℝ} (hρle : ρ ≤ la)
    {d : BandArcData} {D : SweepData d}
    (hmid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1), ∀ u : ℝ,
      D.ta s + ρ ≤ u → u ≤ D.tb s - ρ →
        r u ∉ openSegment ℝ (r (D.ta s)) (r (D.tb s))) :
    ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1), ∀ u : ℝ,
      D.ta s + la ≤ u → u ≤ D.tb s - la →
        r u ∉ openSegment ℝ (r (D.ta s)) (r (D.tb s)) := by
  intro s hs0 hs1 u hu1 hu2 hmem
  exact hmid s hs0 hs1 u (by linarith) (by linarith) hmem

end Work.Drive
