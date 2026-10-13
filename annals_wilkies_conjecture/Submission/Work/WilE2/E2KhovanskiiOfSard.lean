/-
  Work.WilE2 — area E2.  `E2_khovanskii` modulo Sard.

  The frozen statement of `E2_khovanskii` (Spec.lean, area E) is reduced here to ONE explicit
  input:

  * `hSard` — Sard's theorem for a rectangular `C²` map `ℝ^{m+1} → ℝ^m`, in the form of the
    density of regular values.  Its proof is `Work.WilE2.regular_values_dense` (in flight in this
    directory, via `RegVals/sard_codim_one`); it is the only remaining ingredient of the area.

  Everything else is proved here or in this directory: the smoothness of the lifted system
  (`SmoothLift.contDiff_liftSystem`), the induction `kho_all_of`, and the four remaining inputs of
  `E2_khovanskii_of_parts` (`kho_base`, `kho_sphere`, `kho_good_exists`, `kho_proper`).
-/
import Mathlib
import Submission.Work.WilE2.KhoAssemble
import Submission.Work.WilE2.kho_base
import Submission.Work.WilE2.kho_sphere
import Submission.Work.WilE2.kho_good_exists
import Submission.Work.WilE2.kho_proper
import Submission.Work.WilE2.SmoothLift

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

/-- **`E2_khovanskii` from Sard for rectangular maps.**  The conclusion is the frozen statement
verbatim. -/
theorem E2_khovanskii_of_sard
    (hSard : ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)), ContDiff ℝ 2 G →
      ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
        ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z)) :
    ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (f : Fin k → EAPoly k r)
      (s : Finset (Fin k → ℝ)), k + r ≤ F →
      (∀ x ∈ s, (∀ i, eaEval c (f i) x = 0) ∧
        (Matrix.of fun i j => eaEval c (eaD c j (f i)) x).det ≠ 0) →
      s.card ≤ p.eval (∑ i, atomDeg (f i)) := by
  refine E2_khovanskii_of_parts ?_ ?_ ?_ ?_
  · intro n S F T hT
    exact kho_base S F T hT
  · intro n s S F T hT
    exact kho_sphere S F T hT
  · intro n s S F T hT hproper
    exact kho_good_exists S F T hT hproper (hSard n (liftSystem S F) (contDiff_liftSystem S F))
  · intro n s S F T hproper hT ih y hy
    exact kho_proper S F T hproper hT ih y hy

end Work.WilE2
