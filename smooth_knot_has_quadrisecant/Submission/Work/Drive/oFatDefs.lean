import Mathlib
import Submission.TrisecantLocus
import Submission.Work.Drive.Prelude
import Submission.StripCrosscut

/-!
# The lead's `OFat ρ` obstruction set (the 00:10 design)

The project lead's 00:10 decision replaces Kuperberg's `O'` (and the refuted sharpening `OPrimeK` —
see `Submission/Work/Drive/NOTES_OPrimeK_sharpening_REFUTED.md`) by

    OFat ρ := { classes whose chord carries a middle point at parameter-distance ≥ ρ from BOTH
                endpoints },

with `ρ > 0` **uniform** over `C²`-bounded families (from `hinfl` + `C²` bounds +
`exists_separation_knotMap`).  The chord sweep of a non-separating arc avoiding `OFat ρ ∪ TC`
(`TC` = the tangent chords, finite under `TangentChordGP` + `hinfl`) then has only *corner-local*
crossings (a middle within `ρ₀` of an endpoint), and those are removed by deepening the chamfer; the
resulting `ρ`-fat quadrisecant is non-degenerate in the limit, which is exactly what the spread
bookkeeping of `Work.Drive.quadrisecant_of_genericCase_approx` consumes
(`Work.Drive.SpreadCrux`, `Drive/spreadBookkeepingK_spreadCrux.lean`).

This module fixes the vocabulary (`OFat`, `liftedOFat`) and the two immediate facts.  The version
below quantifies over ordered representatives (`OrderedPairs`); the two fatness clauses are symmetric
in the two endpoints, so the set is representative-independent (the same argument as
`Work.Drive.HasMiddleOnClass_rep`).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The lead's `OFat ρ`**: the classes of the open Möbius band whose chord carries a middle point
at parameter-distance at least `ρ` from **both** of its endpoints.  (Larger `ρ` gives a *smaller*
set: `Work.Drive.OFat_mono`.) -/
def OFat (r : ℝ → Space) (ρ : ℝ) : Set OpenMobius :=
  {c | ∃ p : OrderedPairs, mobiusCover p = c ∧ ∃ m : AddCircle period,
    IsMiddleOnChord r p.1.1 p.1.2 m ∧ ρ ≤ dist m p.1.1 ∧ ρ ≤ dist m p.1.2}

/-- Membership in `OFat ρ`, unfolded. -/
lemma mem_OFat_iff {r : ℝ → Space} {ρ : ℝ} {c : OpenMobius} :
    c ∈ OFat r ρ ↔ ∃ p : OrderedPairs, mobiusCover p = c ∧ ∃ m : AddCircle period,
      IsMiddleOnChord r p.1.1 p.1.2 m ∧ ρ ≤ dist m p.1.1 ∧ ρ ≤ dist m p.1.2 := Iff.rfl

/-- `OFat ρ` is a subset of the trisecant locus `O`: a fat middle is a middle. -/
lemma OFat_subset_trisecantSet (r : ℝ → Space) (ρ : ℝ) :
    OFat r ρ ⊆ trisecantSet r := by
  rintro c ⟨p, hp, m, hm, -, -⟩
  exact ⟨m, p, hp, hm⟩

/-- `OFat ρ` is antitone in `ρ` (a larger threshold is a smaller obstruction set). -/
lemma OFat_mono (r : ℝ → Space) {ρ ρ' : ℝ} (h : ρ ≤ ρ') : OFat r ρ' ⊆ OFat r ρ := by
  rintro c ⟨p, hp, m, hm, h1, h2⟩
  exact ⟨p, hp, m, hm, le_trans h h1, le_trans h h2⟩

/-- **The lift of `OFat ρ` to the period strip** (the `OFat`-analogue of `liftedTrisecant` and
`liftedOPrime`). -/
def liftedOFat (r : ℝ → Space) (ρ : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ h0 : 0 < p.2, ∃ h1 : p.2 < period, stripSecantClass p h0 h1 ∈ OFat r ρ}

/-- `liftedOFat ρ` lies inside the lifted trisecant locus. -/
lemma liftedOFat_subset_liftedTrisecant (r : ℝ → Space) (ρ : ℝ) :
    liftedOFat r ρ ⊆ liftedTrisecant r := by
  rintro p ⟨h0, h1, hp⟩
  exact ⟨h0, h1, OFat_subset_trisecantSet r ρ hp⟩

/-- Membership in `liftedOFat`, unfolded. -/
lemma mem_liftedOFat_iff {r : ℝ → Space} {ρ : ℝ} {p : ℝ × ℝ} :
    p ∈ liftedOFat r ρ ↔ ∃ h0 : 0 < p.2, ∃ h1 : p.2 < period,
      stripSecantClass p h0 h1 ∈ OFat r ρ := Iff.rfl


/-! ## 2. The lead's strip-level definitions (`NOTES_LEAD_OFat.md`, 01:40)

The design uses *strip* sets (not classes), because the sweep lives in the strip and because the
"middle" must lie on the **retained arc** of the chord (the part of the knot between the two endpoints
in the retained direction), not merely anywhere on the chord.

* `Work.Drive.FatMiddle r ρ u` — `u` is a middle of some chord `(a, a+y)` of `r` with `y ∈ (0, period)`
  at parameter-distance at least `ρ` from **both** endpoints;
* `Work.Drive.OFatR r ρ` — the strip points whose chord carries a *fat* middle:
  `{q | 0 < q.2 < period ∧ ∃ u, q.1 + ρ ≤ u ≤ q.1 + q.2 - ρ ∧ r u ∈ openSegment ℝ (r q.1) (r (q.1+q.2))}`;
* `Work.Drive.TCset r` — the strip points where the chord is tangent at one of its endpoints;
* `A := OFatR r' ρ ∪ TCset r'` — the obstruction set of the design.
-/

/-- **A fat middle**: `u` is a strict middle of the chord `(a, a+y)` (`0 < y < period`) at
parameter-distance at least `ρ` from both endpoints. -/
def FatMiddle (r : ℝ → Space) (ρ : ℝ) (u : ℝ) : Prop :=
  ∃ a y : ℝ, 0 < y ∧ y < period ∧ a + ρ ≤ u ∧ u ≤ a + y - ρ ∧
    r u ∈ openSegment ℝ (r a) (r (a + y))

/-- **The lead's `OFatR`**: the strip points whose chord carries a fat middle on its retained arc. -/
def OFatR (r : ℝ → Space) (ρ : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 < q.2 ∧ q.2 < period ∧ ∃ u : ℝ, q.1 + ρ ≤ u ∧ u ≤ q.1 + q.2 - ρ ∧
    r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2))}

/-- **The lead's `TCset`**: the strip points whose chord is tangent at one of its endpoints. -/
def TCset (r : ℝ → Space) : Set (ℝ × ℝ) :=
  {q | 0 < q.2 ∧ q.2 < period ∧
    (cross3 (r (q.1 + q.2) - r q.1) (velocity r q.1) = 0 ∨
     cross3 (r (q.1 + q.2) - r q.1) (velocity r (q.1 + q.2)) = 0)}

/-- The obstruction set `A` of the design. -/
def OFatObstruction (r : ℝ → Space) (ρ : ℝ) : Set (ℝ × ℝ) := OFatR r ρ ∪ TCset r

/-- Membership in `OFatR`, unfolded. -/
lemma mem_OFatR_iff {r : ℝ → Space} {ρ : ℝ} {q : ℝ × ℝ} :
    q ∈ OFatR r ρ ↔ 0 < q.2 ∧ q.2 < period ∧ ∃ u : ℝ, q.1 + ρ ≤ u ∧ u ≤ q.1 + q.2 - ρ ∧
      r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) := Iff.rfl

/-- Membership in `TCset`, unfolded. -/
lemma mem_TCset_iff {r : ℝ → Space} {q : ℝ × ℝ} :
    q ∈ TCset r ↔ 0 < q.2 ∧ q.2 < period ∧
      (cross3 (r (q.1 + q.2) - r q.1) (velocity r q.1) = 0 ∨
       cross3 (r (q.1 + q.2) - r q.1) (velocity r (q.1 + q.2)) = 0) := Iff.rfl

/-- A point of `OFatR r ρ` has chord length at least `2ρ`. -/
lemma two_mul_le_snd_of_mem_OFatR {r : ℝ → Space} {ρ : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ OFatR r ρ) : 2 * ρ ≤ q.2 := by
  obtain ⟨-, -, u, h1, h2, -⟩ := hq
  linarith

/-- `FatMiddle` transported to the strip: a fat middle of the chord of a point of `OFatR`. -/
lemma fatMiddle_of_mem_OFatR {r : ℝ → Space} {ρ : ℝ} {q : ℝ × ℝ} (hq : q ∈ OFatR r ρ) :
    FatMiddle r ρ (q.1 + ρ) ∨ FatMiddle r ρ (q.1 + q.2 - ρ) ∨
      ∃ u : ℝ, FatMiddle r ρ u ∧ q.1 + ρ ≤ u ∧ u ≤ q.1 + q.2 - ρ := by
  obtain ⟨h0, h1, u, hu1, hu2, hu3⟩ := hq
  exact Or.inr (Or.inr ⟨u, ⟨q.1, q.2, h0, h1, hu1, hu2, hu3⟩, hu1, hu2⟩)

/-- `OFatR r ρ` is antitone in `ρ`. -/
lemma OFatR_mono (r : ℝ → Space) {ρ ρ' : ℝ} (h : ρ ≤ ρ') : OFatR r ρ' ⊆ OFatR r ρ := by
  rintro q ⟨h0, h1, u, hu1, hu2, hu3⟩
  exact ⟨h0, h1, u, by linarith, by linarith, hu3⟩

end Work.Drive

