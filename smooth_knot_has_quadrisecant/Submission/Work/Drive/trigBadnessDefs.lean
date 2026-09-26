import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.trigFun

/-!
# Vocabulary for the tangent–chord construction

Shared (sorry-free) definitions used by the approximation argument for
`Work.Drive.torusGeneralPositionTransverse_noInflection_dense`.

* `trigDegLe D P` — the trigonometric sums of degree at most `D` (the finite-dimensional
  perturbation family);
* `trigJets a b m P` — the jet data `(P, P')` at the three parameters `a`, `b`, `m`;
* `chordTangentVec`-style maps of a curve and a parameter triple (the "badness" maps whose
  zero sets are the bad locus).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The trigonometric sums of degree at most `D`: all frequencies with nonzero coefficient
lie in `[-D, D]`. -/
def trigDegLe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℕ) (P : TrigFun E) : Prop :=
  (∀ k : ℤ, P.c k ≠ 0 → k ∈ Set.Icc (-(D : ℤ)) (D : ℤ)) ∧
  (∀ k : ℤ, P.d k ≠ 0 → k ∈ Set.Icc (-(D : ℤ)) (D : ℤ))

/-- The `(value, first derivative)` jet data of a trigonometric sum at the parameters
`a`, `b`, `m`. -/
def trigJets (a b m : ℝ) (P : TrigFun Space) :
    (Space × Space) × (Space × Space) × (Space × Space) :=
  ((P.toFun a, deriv P.toFun a), (P.toFun b, deriv P.toFun b), (P.toFun m, deriv P.toFun m))

end

end Work.Drive
