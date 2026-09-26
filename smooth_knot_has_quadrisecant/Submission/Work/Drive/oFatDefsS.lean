import Mathlib
import Submission.Work.Drive.oFatDefs

/-!
# The `E3′` obstruction set of the lead's uniform-`ρ₀` design (`NOTES_LEAD_endgameUniform.md` §1)

The endgame needs the crosscut to avoid, besides `OFatObstruction r ρ = OFatR r ρ ∪ TCset r` (the
*retained* middles at scale `ρ`), also the chords whose parameter length is *short* (`≤ δs`, or, in
the wrap-around direction, `≥ period - δs`) and that carry *any* middle at all.  The reason is the
`E3′` no-middle brick `Work.Drive.noMiddle_near_farthest`: near a maximiser of `‖r‖` there is no
middle at all on a chord whose two ends lie in a uniform window, so a `ShortMid` point can never have
its middle close to a slab centre `t₀ + k·period`, which is what makes the cell index of
`Work.Drive.components_bounded_of_no_spreadQuad` extend to the enlarged obstruction set.

* `Work.Drive.ShortMid r δs` — the strip points of a short chord with a middle;
* `Work.Drive.OFatObstructionS r ρ δs` — `OFatObstruction r ρ ∪ ShortMid r δs`;
* `Work.Drive.StripCrosscutAvoidingOFatS r ρ δs` — the corresponding crosscut.

Everything else (closedness, the edge band, the bounded components, the `C²`-ball form
`crosscut_or_spreadQuad_of_closeS`) is stated in terms of these three.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

open scoped unitInterval

/-- **The `E3′` short-middle set**: the strip points `q = (a, y)` whose chord has parameter length
`y ≤ δs` (or `period - y ≤ δs`, i.e. the complementary arc is short) **and** carries a middle `u`
anywhere on its arc (`q.1 ≤ u ≤ q.1 + q.2`) — no fatness condition. -/
def ShortMid (r : ℝ → Space) (δs : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 < q.2 ∧ q.2 < period ∧ (q.2 ≤ δs ∨ period - q.2 ≤ δs) ∧
    ∃ u : ℝ, q.1 ≤ u ∧ u ≤ q.1 + q.2 ∧ r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2))}

/-- Membership in `ShortMid`, unfolded. -/
lemma mem_ShortMid_iff {r : ℝ → Space} {δs : ℝ} {q : ℝ × ℝ} :
    q ∈ ShortMid r δs ↔ 0 < q.2 ∧ q.2 < period ∧ (q.2 ≤ δs ∨ period - q.2 ≤ δs) ∧
      ∃ u : ℝ, q.1 ≤ u ∧ u ≤ q.1 + q.2 ∧
        r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) := Iff.rfl

/-- **The `E3′` obstruction set**: the retained fat middles at scale `ρ`, the tangent chords, and the
short chords with any middle. -/
def OFatObstructionS (r : ℝ → Space) (ρ δs : ℝ) : Set (ℝ × ℝ) :=
  OFatObstruction r ρ ∪ ShortMid r δs

/-- `OFatObstruction r ρ` is contained in `OFatObstructionS r ρ δs`. -/
lemma OFatObstruction_subset_OFatObstructionS (r : ℝ → Space) (ρ δs : ℝ) :
    OFatObstruction r ρ ⊆ OFatObstructionS r ρ δs := Set.subset_union_left

/-- `ShortMid r δs` is contained in `OFatObstructionS r ρ δs`. -/
lemma ShortMid_subset_OFatObstructionS (r : ℝ → Space) (ρ δs : ℝ) :
    ShortMid r δs ⊆ OFatObstructionS r ρ δs := Set.subset_union_right

/-- `OFatObstructionS r ρ δs` is antitone in `ρ` (`OFatR r ρ` is). -/
lemma OFatObstructionS_mono (r : ℝ → Space) {ρ ρ' δs : ℝ} (h : ρ ≤ ρ') :
    OFatObstructionS r ρ' δs ⊆ OFatObstructionS r ρ δs := by
  rintro q (hq | hq)
  · rcases hq with hq | hq
    · exact Or.inl (Or.inl (OFatR_mono r h hq))
    · exact Or.inl (Or.inr hq)
  · exact Or.inr hq

/-- **The `E3′` crosscut.**  A bottom–top crosscut of the period strip avoiding
`Work.Drive.OFatObstructionS r ρ δs`. -/
def StripCrosscutAvoidingOFatS (r : ℝ → Space) (ρ δs : ℝ) : Prop :=
  ∃ γ : C(I, ℝ × ℝ), (γ 0).2 = 0 ∧ (γ 1).2 = period ∧
    (∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < (γ t).2 ∧ (γ t).2 < period) ∧
    (∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∉ OFatObstructionS r ρ δs)

end Work.Drive
