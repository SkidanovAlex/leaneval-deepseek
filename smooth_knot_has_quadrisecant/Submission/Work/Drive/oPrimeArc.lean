import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.secantDiskAPI
import Submission.Work.Drive.chordSweepDefs

/-!
# The `O'`-avoiding non-separating band arc

Kuperberg's §3 "topological non-triviality" argument replaces the trisecant locus `O` by

    O' = OPrime r  (the *topologically non-trivial* trisecants, together with the quadrisecants that
    are non-trivial at the middle secant, `Submission/OPrime.lean`),

and asks for a non-separating band arc avoiding `O'` (not `O`!).  An `O'`-avoiding arc *may* meet
`O`, namely at topologically trivial trisecants; Kuperberg's Fig.-3 surgery repairs the spanning disk
at those meetings.  This module fixes the vocabulary:

* `Work.Drive.NonSeparatingArcAvoidingOPrime r` — `NonSeparatingArcAvoidingO` with `OPrime r` in
  place of the full trisecant set;
* `Work.Drive.NonSeparatingArcAvoidingOPrime.toAvoidingO` — an `O'`-avoiding arc is in particular an
  `O`-avoiding arc (since `O' ⊆ O`, `LeanEval.KnotTheory.Quadrisecant.OPrime_subset_trisecantSet`);
* `Work.Drive.NonSeparatingArcAvoidingO.toAvoidingOPrime` — conversely, if the whole trisecant locus
  is avoidable, so is `O'` (same arc, `O' ⊆ O`).

This is the vocabulary in which the corrected decomposition of
`Work.Drive.exists_nontrivial_quadrisecant_of_generalPosition_noInflection` is stated.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped unitInterval

/-- **A non-separating band arc avoiding `O'`**: the two branches of the arc sweep the knot once
(`BandArcNonSeparating`) and every interior secant of the arc is *not* a topologically non-trivial
trisecant (nor a quadrisecant non-trivial at the middle secant), i.e. avoids `OPrime r`. -/
def NonSeparatingArcAvoidingOPrime (r : ℝ → Space) : Prop :=
  ∃ d : BandArcData, BandArcNonSeparating d ∧
    ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ OPrime r

/-- An arc avoiding the whole trisecant locus `O` avoids `O'` as well, since `O' ⊆ O`
(`LeanEval.KnotTheory.Quadrisecant.OPrime_subset_trisecantSet`).  (The converse fails in general:
an `O'`-avoiding arc may meet `O` at topologically trivial trisecants — this is exactly where
Kuperberg's Fig.-3 surgery is needed.) -/
lemma NonSeparatingArcAvoidingO.toAvoidingOPrime {r : ℝ → Space}
    (h : NonSeparatingArcAvoidingO r) : NonSeparatingArcAvoidingOPrime r := by
  obtain ⟨d, hns, hav⟩ := h
  exact ⟨d, hns, fun s hs0 hs1 hc => hav s hs0 hs1 (OPrime_subset_trisecantSet hc)⟩

end Work.Drive
