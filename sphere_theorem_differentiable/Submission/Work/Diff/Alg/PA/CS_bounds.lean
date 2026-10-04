import Mathlib
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.PA.CS_aux
import Submission.Work.Diff.Alg.PA.tpair_abs_le
import Submission.Work.Diff.Alg.PA.Q_comp_abs_le
import Submission.Work.Diff.Alg.PA.Qbil_comp_abs_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cauchy–Schwarz bounds for the reaction term `Q`, its polarisation `Qbil` and the pairing `tpair`

Contract `PA` of `Submission/Diff/Grad.lean` needs the elementary fact that Hamilton's reaction term
`Q` is *quadratic* in the curvature array and that the Frobenius pairing is Cauchy–Schwarz:

* `∃ c ≥ 0`, `√|Q A|² ≤ c |A|²` and `√|Qbil A B|² ≤ c √|A|² √|B|²` for all 4-index arrays
  (no algebraic curvature symmetry is required), and
* `|⟪A,B⟫| ≤ √|A|² √|B|²`.

Both are proved by componentwise estimates.  Writing `|A|² = frobSq A`,

* each component of `Q A` is at most `5 n² |A|²` (three sums of products, bounded by
  Cauchy–Schwarz / triangle inequality), so `frobSq (Q A) ≤ n⁴ (5 n² |A|²)²` and hence
  `√(frobSq (Q A)) ≤ 5 n⁴ |A|²`;
* each component of `Qbil A B` is at most `5 n² |A| |B|` (six products), giving
  `√(frobSq (Qbil A B)) ≤ 5 n⁴ |A| |B|`.

So the constant `c = 5 n⁴` works simultaneously for `Q` and `Qbil`.  The componentwise bounds are
proved in the imported files `Q_comp_abs_le` and `Qbil_comp_abs_le`; the passage from a
componentwise bound to the `frobSq` bound is `CS_aux.frobSq_le_of_comp_bound`, and the
Cauchy–Schwarz inequality for `tpair` is `tpair_abs_le`.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

theorem CS_bounds (n : ℕ) :
    (∃ c : ℝ, 0 ≤ c ∧
      (∀ A : Curv4 n, Real.sqrt (frobSq (Q A)) ≤ c * frobSq A) ∧
      (∀ A B : Curv4 n, Real.sqrt (frobSq (Qbil n A B)) ≤ c * Real.sqrt (frobSq A) * Real.sqrt (frobSq B))) ∧
    (∀ A B : Curv4 n, |tpair n A B| ≤ Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) := by
  refine ⟨⟨5 * (n : ℝ) ^ 4, by positivity, ?_, ?_⟩, ?_⟩
  · -- the componentwise bound on `Q` upgrades to `√(frobSq (Q A)) ≤ 5 n⁴ frobSq A`
    intro A
    have hsq : frobSq (Q A) ≤ (5 * (n : ℝ) ^ 4 * frobSq A) ^ 2 := by
      calc frobSq (Q A) ≤ (n : ℝ) ^ 4 * (5 * (n : ℝ) ^ 2 * frobSq A) ^ 2 :=
            frobSq_le_of_comp_bound (Q A) _ (Q_comp_abs_le n A)
        _ = (5 * (n : ℝ) ^ 4 * frobSq A) ^ 2 := by ring
    calc Real.sqrt (frobSq (Q A)) ≤ Real.sqrt ((5 * (n : ℝ) ^ 4 * frobSq A) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = |5 * (n : ℝ) ^ 4 * frobSq A| := Real.sqrt_sq_eq_abs _
      _ = 5 * (n : ℝ) ^ 4 * frobSq A :=
          abs_of_nonneg (mul_nonneg (by positivity) (frobSq_nonneg A))
  · -- the componentwise bound on `Qbil` upgrades to `√(frobSq (Qbil A B)) ≤ 5 n⁴ √|A|² √|B|²`
    intro A B
    have hsq : frobSq (Qbil n A B) ≤
        (5 * (n : ℝ) ^ 4 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B))) ^ 2 := by
      calc frobSq (Qbil n A B) ≤
            (n : ℝ) ^ 4 * (5 * (n : ℝ) ^ 2 *
              (Real.sqrt (frobSq A) * Real.sqrt (frobSq B))) ^ 2 :=
            frobSq_le_of_comp_bound (Qbil n A B) _ (Qbil_comp_abs_le n A B)
        _ = (5 * (n : ℝ) ^ 4 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B))) ^ 2 := by ring
    calc Real.sqrt (frobSq (Qbil n A B))
        ≤ Real.sqrt ((5 * (n : ℝ) ^ 4 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B))) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = 5 * (n : ℝ) ^ 4 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) := by
          rw [Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (mul_nonneg (by positivity)
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      _ = 5 * (n : ℝ) ^ 4 * Real.sqrt (frobSq A) * Real.sqrt (frobSq B) := by ring
  · -- Cauchy–Schwarz for the Frobenius pairing
    intro A B
    exact tpair_abs_le n A B

end Work.Diff.Alg.PA
