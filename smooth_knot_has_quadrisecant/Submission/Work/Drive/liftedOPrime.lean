import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.oPrimeArc
import Submission.StripCrosscut

/-!
# The lift of the `O'`-locus to the strip

Mirrors `Submission/StripCrosscut.lean`'s `liftedTrisecant` for Kuperberg's `O'`-locus
(`LeanEval.KnotTheory.Quadrisecant.OPrime r`, `Submission/OPrime.lean`): the preimage of `O'` in the
strip of lifted secants, together with the two basic facts the strip/crosscut argument needs
(the inclusion `liftedOPrime ⊆ liftedTrisecant` and the invariance under the deck generator
`stripFlip`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The lifted `O'`-locus**: the preimage in the strip `ℝ × (0, period)` of Kuperberg's `O'`
under the covering `stripSecantClass`. -/
def liftedOPrime (r : ℝ → Space) : Set (ℝ × ℝ) :=
  {p | ∃ h0 : 0 < p.2, ∃ h1 : p.2 < period, stripSecantClass p h0 h1 ∈ OPrime r}

lemma mem_liftedOPrime_iff {r : ℝ → Space} {p : ℝ × ℝ} :
    p ∈ liftedOPrime r ↔ ∃ h0 : 0 < p.2, ∃ h1 : p.2 < period,
      stripSecantClass p h0 h1 ∈ OPrime r := Iff.rfl

/-- `O'`-membership in the strip does not depend on the distinctness witnesses. -/
lemma liftedOPrime_congr_witness {r : ℝ → Space} {p : ℝ × ℝ}
    (h0 h0' : 0 < p.2) (h1 h1' : p.2 < period) :
    stripSecantClass p h0 h1 ∈ OPrime r ↔ stripSecantClass p h0' h1' ∈ OPrime r := by
  rw [stripSecantClass_congr h0 h0' h1 h1']

/-- **`O'` lifts inside `O`**: `liftedOPrime r ⊆ liftedTrisecant r` (`O' ⊆ O`). -/
lemma liftedOPrime_subset_liftedTrisecant (r : ℝ → Space) :
    liftedOPrime r ⊆ liftedTrisecant r := by
  rintro p ⟨h0, h1, hmem⟩
  exact ⟨h0, h1, OPrime_subset_trisecantSet hmem⟩

/-- **Invariance under the deck generator.**  The strip points `(x, y)` and
`(x + y, period - y)` carry the same secant class, hence `liftedOPrime` — like `liftedTrisecant` —
is invariant under `stripFlip`. -/
lemma stripFlip_mem_liftedOPrime {r : ℝ → Space} {p : ℝ × ℝ} :
    stripFlip p ∈ liftedOPrime r ↔ p ∈ liftedOPrime r := by
  constructor
  · rintro ⟨h0, h1, hmem⟩
    have k0 : 0 < p.2 := by rw [stripFlip_snd] at h1; linarith
    have k1 : p.2 < period := by rw [stripFlip_snd] at h0; linarith
    exact ⟨k0, k1, by rwa [stripSecantClass_stripFlip k0 k1 h0 h1] at hmem⟩
  · rintro ⟨k0, k1, hmem⟩
    have h0 : 0 < (stripFlip p).2 := by rw [stripFlip_snd]; linarith
    have h1 : (stripFlip p).2 < period := by rw [stripFlip_snd]; linarith
    exact ⟨h0, h1, by rw [stripSecantClass_stripFlip k0 k1 h0 h1]; exact hmem⟩

/-- Invariance under the translation by one period — `stripFlip` squared. -/
lemma liftedOPrime_add_period (r : ℝ → Space) :
    ∀ q : ℝ × ℝ, q ∈ liftedOPrime r ↔ (q.1 + period, q.2) ∈ liftedOPrime r := by
  intro q
  have h1 : stripFlip q ∈ liftedOPrime r ↔ q ∈ liftedOPrime r :=
    stripFlip_mem_liftedOPrime
  have h2 : stripFlip (stripFlip q) ∈ liftedOPrime r ↔ stripFlip q ∈ liftedOPrime r :=
    stripFlip_mem_liftedOPrime
  rw [stripFlip_stripFlip q] at h2
  exact ⟨fun hp => h2.mpr (h1.mpr hp), fun hp => h1.mp (h2.mp hp)⟩

end Work.Drive
