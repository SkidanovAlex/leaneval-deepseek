/-
  Work.WilE2 — area E2.  **`E2_khovanskii`** (the frozen statement, Spec.lean area E).

  This is the assembled Khovanskii bound for EA chains:

    `E2_khovanskii : ∀ F, ∃ p, ∀ (k r) (c : EAChain k r) (f : Fin k → EAPoly k r) (s : Finset),
       k + r ≤ F → (∀ x ∈ s, (∀ i, eaEval c (f i) x = 0) ∧ det(eaD c j (f i) x) ≠ 0) →
       s.card ≤ p.eval (∑ i, atomDeg (f i))`

  The conclusion is the frozen statement verbatim; the witness polynomial is `khoPoly F`
  (`Submission.Work.WilE2.Bound`).

  Ingredients (all proved in this directory):
  * `E2_khovanskii_of_sard` (`E2KhovanskiiOfSard.lean`) — the whole induction, reduced to the
    density of regular values of a rectangular `C²` map;
  * `regular_values_dense` — that Sard input (Sard for `ℝ^{m+1} → ℝ^m`, via
    `RegVals/sard_codim_one`);
  * `kho_base` (Bézout), `kho_sphere` (compactness/augmentation), `kho_good_exists` (genericity +
    inverse function theorem), `kho_proper` (Khovanskii–Rolle), `KhovB_mono`,
    `KhovB_le_khoPoly` (bookkeeping), `KhoCount` (the Rolle counting), `RolleDetAnalytic`
    (Claim `regular-solutions`), `SmoothLift` (smoothness of the lift).
-/
import Mathlib
import Submission.Work.WilE2.E2KhovanskiiOfSard
import Submission.Work.WilE2.regular_values_dense

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

/-- **E2a. Khovanskii for EA chains.**  Non-degenerate zeros of `k` EA functions in `k`
variables are polynomially bounded in terms of the atom degrees, uniformly in the chain
coefficients. -/
theorem E2_khovanskii_proved : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r)
    (f : Fin k → EAPoly k r) (s : Finset (Fin k → ℝ)), k + r ≤ F →
    (∀ x ∈ s, (∀ i, eaEval c (f i) x = 0) ∧
      (Matrix.of fun i j => eaEval c (eaD c j (f i)) x).det ≠ 0) →
    s.card ≤ p.eval (∑ i, atomDeg (f i)) :=
  E2_khovanskii_of_sard fun _ G hG => regular_values_dense G hG

end Work.WilE2
