/-
  Work.WilE2 — area E2.  **`E2_components`** (the frozen statement, Spec.lean area E).

  The number of connected components of an EA semi-Pfaffian set is polynomial in the atom degrees
  for a fixed format:

    `E2_components : ∀ F, ∃ p, ∀ (k) (X : SemiPf k), X.fmt ≤ F →
       ∃ s : Finset, s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
         ∀ x ∈ X.set, ∃ y ∈ s, cc x = cc y`

  The conclusion is the frozen statement verbatim; the witness polynomial is built in
  `E2_components_of_basic`.

  Ingredients (all proved in this directory):
  * `E2_components_of_basic` — the frozen conclusion from the per-basic-set bound (a finite union
    of basic sets, via `exists_meet_components_iUnion`);
  * `sign_components_bound` — Gabrielov–Vorobjov Theorem 3.7 (a basic set is one sign assignment,
    dominated by the variety `{∏ (g ± ε)² = δ}`), from the variety bound;
  * `variety_components_bound` — Gabrielov–Vorobjov Corollary 3.3, from Khovanskii (`E2a`) and the
    Morse genericity (`regular_values_dense`);
  * `E2_khovanskii_proved` — the Khovanskii bound of `E2a`;
  * `regular_values_dense` — Sard for rectangular `C²` maps.
-/
import Mathlib
import Submission.Work.WilE2.E2_components_of_basic
import Submission.Work.WilE2.sign_components_bound
import Submission.Work.WilE2.variety_components_bound
import Submission.Work.WilE2.E2_khovanskii_proved
import Submission.Work.WilE2.regular_values_dense

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

/-- **E2b. Components.**  An EA semi-Pfaffian set has polynomially many connected components;
concretely, for every format bound `F` there is a finite set of `p.eval X.deg` points of `X`
meeting every connected component of `X`. -/
theorem E2_components_proved : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k),
    X.fmt ≤ F →
    ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
      ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y :=
  E2_components_of_basic fun F =>
    sign_components_bound F
      (variety_components_bound (fun F => E2_khovanskii_proved F)
        (fun _ G hG => regular_values_dense G hG) F)

end Work.WilE2
