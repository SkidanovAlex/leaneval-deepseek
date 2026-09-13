/-
# Savin's Proposition 4.1 (improvement of flatness) in the concrete setting

This file assembles the proof of the "improvement of flatness" statement for the concrete operator
family `Fop C ε` of `Submission.Savin.Operator`, which is the input of the Caffarelli iteration
leading to Savin's Theorem 1.3 (and hence to `Submission.SavinInput`).

We work with the *linearised* form of the equation: `v` solves `Fop C ε (D²v) = 0` where
`C = cofOp N` for a quadratic solution `N` of `σ₂ = 1`.  Writing `Ψ := ε • v` converts it into the
unperturbed equation `s2 (N + D²Ψ) = 1` (see `Submission.Savin.Prop41.exists_correct_fop` for the
conversion at the level of the equation, and the Roadmap for the general discussion).

This file contains, in order:
* `exists_correct_fop`: the correction step (find a multiple of the identity whose addition makes a
  nearly-linear solution an exact solution of `Fop C ε = 0`).
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Correction
import Submission.Savin.Diag
import Submission.Savin.Mono
import Submission.Savin.LinearQuad

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-! ## The correction step -/

/-- **Correction of a nearly-linear solution.**  If `A := trOp C + 3 ε trOp M > 0` and the
discriminant `A² - 24 ε D` (with `D := pairOp C M + ε s2 M`) is nonnegative, then there is
`lam` with `Fop C ε (M + lam • 1) = 0` and `|lam| ≤ 2|D|/A`. -/
theorem exists_correct_fop {C M : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) (hM : M.IsSymmetric)
    {ε : ℝ} (hε : 0 < ε)
    (hA : 0 < trOp C + 3 * ε * trOp M)
    (hdisc : 0 ≤ (trOp C + 3 * ε * trOp M) ^ 2 - 24 * ε * (pairOp C M + ε * s2 M)) :
    ∃ lam : ℝ, Fop C ε (M + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) = 0 ∧
      |lam| ≤ 2 * |pairOp C M + ε * s2 M| / (trOp C + 3 * ε * trOp M) := by
  have h12 : (12 : ℝ) * ε ≠ 0 := by positivity
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 2
      = (trOp C + 3 * ε * trOp M) ^ 2 - 24 * ε * (pairOp C M + ε * s2 M) :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, Real.sq_sqrt hdisc⟩
  set A : ℝ := trOp C + 3 * ε * trOp M with hAdef
  set D : ℝ := pairOp C M + ε * s2 M with hDdef
  have hApos : 0 < A := by rw [hAdef]; exact hA
  have hs2 : s ^ 2 = A ^ 2 - 24 * ε * D := by rw [hAdef, hDdef]; exact hs
  refine ⟨(-A + s) / (12 * ε), ?_, ?_⟩
  · have hexp : Fop C ε (M + ((-A + s) / (12 * ε)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))
        = (pairOp C M + ε * s2 M) + ((-A + s) / (12 * ε)) * (trOp C + 3 * ε * trOp M)
          + 6 * ε * ((-A + s) / (12 * ε)) ^ 2 := by
      rw [Fop, pairOp_add, pairOp_smul, pairOp_one, s2_add_smul_one]
      ring
    rw [hexp, ← hAdef, ← hDdef]
    field_simp
    nlinarith [hs2]
  · have hlam : ((-A + s) / (12 * ε)) * (A + s) = -2 * D := by
      have hfac : (-A + s) * (A + s) = s ^ 2 - A ^ 2 := by ring
      rw [div_mul_eq_mul_div, hfac, hs2]
      field_simp
      ring
    have hAs : 0 < A + s := by linarith
    have h1 : |((-A + s) / (12 * ε)) * (A + s)| = 2 * |D| := by
      rw [hlam, abs_mul]
      norm_num
    rw [abs_mul, abs_of_pos hAs] at h1
    have h2 : |(-A + s) / (12 * ε)| = 2 * |D| / (A + s) := by
      rw [eq_div_iff hAs.ne']
      exact h1
    rw [h2]
    have h3 : (0 : ℝ) ≤ 2 * |D| := by positivity
    calc 2 * |D| / (A + s) ≤ 2 * |D| / A :=
          div_le_div_of_nonneg_left h3 hApos (by linarith)

end

end Submission
