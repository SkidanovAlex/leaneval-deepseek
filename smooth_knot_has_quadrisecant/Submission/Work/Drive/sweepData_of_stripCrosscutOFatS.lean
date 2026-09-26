import Mathlib
import Submission.Work.Drive.sweepData_of_stripCrosscutOFat
import Submission.Work.Drive.oFatDefsS

/-!
# The `E3′` crosscut: the band arc, its `SweepData`, and the two middle-freeness clauses

This is the `E3′` analogue of `Work.Drive.bandArcData_sweepData_of_stripCrosscutOFat`: the crosscut
of the uniform-`ρ₀` design avoids the *enlarged* obstruction set
`Work.Drive.OFatObstructionS r ρ δs = OFatObstruction r ρ ∪ ShortMid r δs`
(`Submission/Work/Drive/oFatDefsS.lean`), and the band arc it defines therefore carries **two**
middle-freeness clauses:

* at scale `ρ` on the retained arc — as before, the output of the `OFatObstruction`-avoidance
  (`OFatR r ρ`); this is what the *deep* zones of the depth schedule use;
* **no middle at all** on every chord of parameter length `≤ δs` (or `≥ period - δs`) — the output
  of the `ShortMid`-avoidance; this is what the *shallow* zones use, and it is exactly what removes
  the crosscut-dependent coupling `ρ ≤ lam · sweepW'` of the old design.

The non-tangency clause (`cross3` at both endpoints) is unchanged: a crosscut avoiding
`ShortMid` avoids `TCset` in particular.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

open scoped unitInterval

/-- **The band arc and its `SweepData` attached to an `E3′` crosscut, with both middle-freeness
clauses.** -/
theorem bandArcData_sweepData_of_stripCrosscutOFatS {r : ℝ → Space} {ρ δs : ℝ}
    (γ : C(I, ℝ × ℝ)) (hbot : (γ 0).2 = 0) (htop : (γ 1).2 = period)
    (hint : ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < (γ t).2 ∧ (γ t).2 < period)
    (havoid : ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∉ OFatObstructionS r ρ δs) :
    ∃ d : BandArcData, ∃ D : SweepData d, BandArcNonSeparating d ∧
      (∀ (s : I), ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
        ∀ u : ℝ, D.ta s + ρ ≤ u → u ≤ D.tb s - ρ →
          r u ∉ openSegment ℝ (r (D.ta s)) (r (D.tb s))) ∧
      (∀ (s : I), ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
        (D.tb s - D.ta s ≤ δs ∨ period - (D.tb s - D.ta s) ≤ δs) →
        ∀ u : ℝ, D.ta s ≤ u → u ≤ D.tb s →
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
  refine ⟨d, D, hns, ?_, ?_, ?_⟩
  · intro s hs0 hs1 u hu1 hu2 hmem
    have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
    have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
    obtain ⟨hh1, hh2⟩ := hint s hpos hlt
    refine havoid s hpos hlt (Or.inl (Or.inl ?_))
    exact ⟨hh1, hh2, u, hu1, hu2, hmem⟩
  · intro s hs0 hs1 hshort u hu1 hu2 hmem
    have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
    have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
    obtain ⟨hh1, hh2⟩ := hint s hpos hlt
    have hD : D.tb s - D.ta s = (γ s).2 := by dsimp only [D]; ring
    have hshort' : (γ s).2 ≤ δs ∨ period - (γ s).2 ≤ δs := by rwa [hD] at hshort
    refine havoid s hpos hlt (Or.inr ?_)
    show 0 < (γ s).2 ∧ (γ s).2 < period ∧ ((γ s).2 ≤ δs ∨ period - (γ s).2 ≤ δs) ∧
      ∃ u : ℝ, (γ s).1 ≤ u ∧ u ≤ (γ s).1 + (γ s).2 ∧
        r u ∈ openSegment ℝ (r (γ s).1) (r ((γ s).1 + (γ s).2))
    exact ⟨hh1, hh2, hshort', u, hu1, hu2, hmem⟩
  · intro s hs0 hs1
    have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
    have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
    obtain ⟨hh1, hh2⟩ := hint s hpos hlt
    have hnotA := havoid s hpos hlt
    have hTC : ¬ ((cross3 (r ((γ s).1 + (γ s).2) - r (γ s).1) (velocity r (γ s).1) = 0) ∨
        (cross3 (r ((γ s).1 + (γ s).2) - r (γ s).1) (velocity r ((γ s).1 + (γ s).2)) = 0)) := by
      intro h
      exact hnotA (Or.inl (Or.inr ⟨hh1, hh2, h⟩))
    have h1 : cross3 (r ((γ s).1 + (γ s).2) - r (γ s).1) (velocity r (γ s).1) ≠ 0 :=
      fun h => hTC (Or.inl h)
    have h2 : cross3 (r ((γ s).1 + (γ s).2) - r (γ s).1) (velocity r ((γ s).1 + (γ s).2)) ≠ 0 :=
      fun h => hTC (Or.inr h)
    exact ⟨h1, h2⟩

/-- **The cut arc misses the chord, with the `E3′` input.**  If the retained middles are all within
`ρ` of an endpoint and the chamfer cuts the arc at depth `la ≥ ρ`, no point of the cut arc is on the
chord; and if in addition the chord is *short* (`≤ δs`) or *almost a full period*
(`≥ period - δs`), then the same holds at **every** cut depth `la ≥ 0`. -/
theorem sweepData_arc_no_chordPointS {r : ℝ → Space} {ρ δs la : ℝ} (hρle : ρ ≤ la)
    (hla : 0 ≤ la)
    {d : BandArcData} {D : SweepData d}
    (hmid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1), ∀ u : ℝ,
      D.ta s + ρ ≤ u → u ≤ D.tb s - ρ →
        r u ∉ openSegment ℝ (r (D.ta s)) (r (D.tb s)))
    (hshort : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      (D.tb s - D.ta s ≤ δs ∨ period - (D.tb s - D.ta s) ≤ δs) →
      ∀ u : ℝ, D.ta s ≤ u → u ≤ D.tb s →
        r u ∉ openSegment ℝ (r (D.ta s)) (r (D.tb s))) :
    ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1), ∀ u : ℝ,
      D.ta s + la ≤ u → u ≤ D.tb s - la →
        r u ∉ openSegment ℝ (r (D.ta s)) (r (D.tb s)) := by
  intro s hs0 hs1 u hu1 hu2 hmem
  by_cases hcase : D.tb s - D.ta s ≤ δs ∨ period - (D.tb s - D.ta s) ≤ δs
  · exact hshort s hs0 hs1 hcase u (by linarith) (by linarith) hmem
  · exact hmid s hs0 hs1 u (by linarith) (by linarith) hmem

end Work.Drive
