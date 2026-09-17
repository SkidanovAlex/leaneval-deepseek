import Mathlib
import Submission.MatSpace
import Submission.MatBridge
import Submission.Rescale
import Submission.Commons.Analysis.Matrix.det_add_smul_one_eq_prod_eigenvalues
import Submission.Commons.Analysis.Matrix.trace_mul_self_eq_sum_eigenvalues_sq
import Submission.Commons.Analysis.SpecialFunctions.Log.log_le_log_add_sub_sq

/-!
# The global Taylor bound for `log det` along a segment

For a symmetric matrix `M` with eigenvalues in `[-r, r]` (`r < a₀`), the logarithm of the
determinant of `a₀·Id + M` is bounded by its second-order Taylor expansion at `a₀·Id`:

    log det(a₀·Id + M) ≤ d log a₀ + tr M / a₀ - (1/2)(a₀+r)⁻² tr(M²).

This replaces the per-step Taylor estimate of `Submission/DriftStep.lean` by a single global one;
the proof is the elementary scalar inequality `log(a₀+x) ≤ log a₀ + x/a₀ - x²/(2(a₀+r)²)` for
`|x| ≤ r` applied to the eigenvalues, together with
`det(c·1 + M) = ∏ (c + λ_i)`, `tr M = Σ λ_i` and `tr(M²) = Σ λ_i²`.
-/

namespace Submission.LogDet

open Matrix Matrix.IsHermitian
open Submission.MatSpace

noncomputable section

variable {d : ℕ}

/-- **Global second-order Taylor bound for `log det`.** -/
theorem log_det_add_smul_one_le (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    {a₀ r : ℝ} (ha₀ : 0 < a₀) (hr : 0 ≤ r) (har : r < a₀)
    (hspec : ∀ i, |hM.eigenvalues i| ≤ r) :
    Real.log (a₀ • 1 + M).det ≤ (d : ℝ) * Real.log a₀ + M.trace / a₀
      - (1 / 2) * (a₀ + r)⁻¹ ^ 2 * (M * M).trace := by
  have hpos : ∀ i, 0 < a₀ + hM.eigenvalues i := by
    intro i
    have := hspec i
    rw [abs_le] at this
    linarith [this.1, har]
  rw [Commons.Analysis.Matrix.det_add_smul_one_eq_prod_eigenvalues M hM a₀,
    Real.log_prod (s := Finset.univ) (f := fun i : Fin d => a₀ + hM.eigenvalues i)
      (fun i _ => ne_of_gt (hpos i))]
  calc ∑ i, Real.log (a₀ + hM.eigenvalues i)
      ≤ ∑ i, (Real.log a₀ + hM.eigenvalues i / a₀
          - hM.eigenvalues i ^ 2 / (2 * (a₀ + r) ^ 2)) :=
        Finset.sum_le_sum fun i _ =>
          Commons.Analysis.SpecialFunctions.Log.log_le_log_add_sub_sq ha₀ hr har (hspec i)
    _ = (d : ℝ) * Real.log a₀ + (∑ i, hM.eigenvalues i) / a₀
          - (1 / 2) * (a₀ + r)⁻¹ ^ 2 * ∑ i, (hM.eigenvalues i) ^ 2 := by
        have h2 : (∑ i : Fin d, hM.eigenvalues i ^ 2 / (2 * (a₀ + r) ^ 2))
            = (1 / 2) * (a₀ + r)⁻¹ ^ 2 * ∑ i : Fin d, (hM.eigenvalues i) ^ 2 := by
          have hc : ∀ i : Fin d, hM.eigenvalues i ^ 2 / (2 * (a₀ + r) ^ 2)
              = ((1 / 2) * (a₀ + r)⁻¹ ^ 2) * hM.eigenvalues i ^ 2 := by
            intro i
            rw [div_eq_mul_inv, mul_inv, ← inv_pow]
            ring
          rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.mul_sum]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, h2]
    _ = (d : ℝ) * Real.log a₀ + M.trace / a₀
          - (1 / 2) * (a₀ + r)⁻¹ ^ 2 * (M * M).trace := by
        rw [hM.trace_eq_sum_eigenvalues,
          Commons.Analysis.Matrix.trace_mul_self_eq_sum_eigenvalues_sq M hM]
        simp

end

end Submission.LogDet
