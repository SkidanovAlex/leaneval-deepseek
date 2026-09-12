import ChallengeDeps
import Submission.PaperBand.RadicalBounds
import Submission.Work.TpatternEscape
open OptimalMoebius
open Topology ContDiff
open scoped BigOperators
open Submission.PaperBand

set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Bridge lemma for `theorem_1_1` (GREEN — no `sorry`)

`theorem_1_1` reduces, via `RadicalBounds.aspect_bound`, to the single
geometric statement `lemmaG_inequality` (PROVED in `Submission.Work.TpatternEscape`):

    if `f : ℝ² → ℝ³` is a smooth embedded paper Möbius band of aspect ratio
    `a` (`IsMoebiusEmbedding a f`), then there is a real `t` with
    `2 * a > max (aspectDelta t) (aspectNu t)`.

That statement is proved in `Submission.Work.TpatternEscape` (assembling
Schwartz's Lemma T, Prop main0, and Lemma G).  Here only the algebraic bridge
to `a > √3` remains, via `aspect_bound` (`Submission.PaperBand.RadicalBounds`).
-/

/-- The main theorem of Schwartz's paper, proved from `lemmaG_inequality` and
the already-formalized algebra of Lemma G. -/
theorem theorem_1_1_bridge (a : ℝ) (ha : a > 0) (f : ℝ² → ℝ³)
    (hf : IsMoebiusEmbedding a f) : a > √3 := by
  rcases Submission.lemmaG_inequality hf ha with ⟨t, ht⟩
  exact aspect_bound (L := a) ht
