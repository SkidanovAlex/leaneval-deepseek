import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.FamRound

/-!
# Proof-irrelevance plumbing for the round measure

`edgeMeasure 𝓖 p h0 h1` carries the two proofs `h0 : 0 ≤ p` and `h1 : p ≤ 1` as
arguments, and different proofs give only *propositionally* equal measures.  The
per-set lemmas (`r2_Yfam_mean`, `r2_Yfam_tail`, `r2_Wfam_tail`, …) are stated at
their own canonical proof terms, while the round lemma
`nibble_round2_fam_asm` quantifies over *arbitrary* proofs `hp0`, `hp1` of the
same propositions.  This module records the trivial congruence that reconciles
the two, together with its `prob`/`exp` forms.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The round measure does not depend on the proof terms of its side conditions. -/
lemma edgeMeasure_congr (𝓖 : Set (Set V)) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (h0' : 0 ≤ p) (h1' : p ≤ 1) :
    edgeMeasure 𝓖 p h0 h1 = edgeMeasure 𝓖 p h0' h1' := by
  rw [FinProb.mk.injEq]

-- The probability does not depend on the proof terms of the side conditions.
lemma edgeMeasure_prob_congr (𝓖 : Set (Set V)) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (h0' : 0 ≤ p) (h1' : p ≤ 1) (A : Set (𝓖 → Bool)) :
    (edgeMeasure 𝓖 p h0 h1).prob A = (edgeMeasure 𝓖 p h0' h1').prob A := by
  rw [edgeMeasure_congr 𝓖 h0 h1 h0' h1']

-- The expectation does not depend on the proof terms of the side conditions.
lemma edgeMeasure_exp_congr (𝓖 : Set (Set V)) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (h0' : 0 ≤ p) (h1' : p ≤ 1) (X : (𝓖 → Bool) → ℝ) :
    (edgeMeasure 𝓖 p h0 h1).exp X = (edgeMeasure 𝓖 p h0' h1').exp X := by
  rw [edgeMeasure_congr 𝓖 h0 h1 h0' h1']

end Work.Deep.Nibble
