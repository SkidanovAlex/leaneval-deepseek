import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Scale.frob_tmC_le
import Submission.Work.TMC7Core.Scale.frob_matProd_le

namespace Work.TMLECore

open Work.TMC7Core

/-- On the compact set of energies `‖E - E₀‖ ≤ 1` and scales `r ≤ k`, the Frobenius norm of
the transfer cocycle `A_r(x)` is bounded uniformly in the phase `x`.  Explicitly, with
`M = √((‖E₀‖ + 1 + 2|λ|)² + 2) ≥ 1`,

`frob (A_r(x)) ≤ √2 · M^r ≤ √2 · M^k`,

because each transfer matrix satisfies `frob (tmC λ E y) ≤ M` (`frob_tmC_le` plus
`‖E‖ ≤ ‖E₀‖ + 1`) and ordered products are submultiplicative (`frob_matProd_le`). -/
theorem log_frob_iterC_low_scale_bound (α lam : ℝ) (E₀ : ℂ) (k : ℕ) :
    ∃ B : ℝ, ∀ (r : ℕ) (E : ℂ) (x : ℝ), r ≤ k → ‖E - E₀‖ ≤ 1 →
      Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E r x)) ≤ B := by
  set M : ℝ := Real.sqrt ((‖E₀‖ + 1 + 2 * |lam|) ^ 2 + 2) with hM
  have hM1 : 1 ≤ M := by
    rw [hM, ← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (‖E₀‖ + 1 + 2 * |lam|)]
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  refine ⟨Real.log (Real.sqrt 2 * M ^ k), ?_⟩
  intro r E x hr hE
  -- `‖E‖ ≤ ‖E₀‖ + 1` on the ball
  have hEnorm : ‖E‖ ≤ ‖E₀‖ + 1 := by
    have hsplit : ‖E‖ ≤ ‖E₀‖ + ‖E - E₀‖ := by
      simpa [add_sub_cancel] using norm_add_le E₀ (E - E₀)
    linarith
  -- each transfer matrix in the product has Frobenius norm at most `M`
  have hA : ∀ j : ℕ, frob (tmC lam E (x + (j : ℝ) * α)) ≤ M := by
    intro j
    refine le_trans (Work.TMC7Core.Scale.frob_tmC_le lam E (x + (j : ℝ) * α)) ?_
    rw [hM]
    apply Real.sqrt_le_sqrt
    have hle : ‖E‖ + 2 * |lam| ≤ ‖E₀‖ + 1 + 2 * |lam| := by linarith
    nlinarith [hle, norm_nonneg E, abs_nonneg lam]
  -- ordered product bound
  have hbound : frob (iterC α lam E r x) ≤ Real.sqrt 2 * M ^ r := by
    rw [iterC_eq_matProd]
    exact Work.TMC7Core.Scale.frob_matProd_le _ M (le_trans zero_le_one hM1) hA r
  have hrle : Real.sqrt 2 * M ^ r ≤ Real.sqrt 2 * M ^ k := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hr) (Real.sqrt_nonneg 2)
  -- positivity, so that `log` is monotone
  have hpos : 0 < frob (iterC α lam E r x) := by
    have h2 := Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam E r x)
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  have hpos2 : 0 < Real.sqrt 2 * M ^ r := by positivity
  calc Real.log (frob (iterC α lam E r x))
      ≤ Real.log (Real.sqrt 2 * M ^ r) := Real.log_le_log hpos hbound
    _ ≤ Real.log (Real.sqrt 2 * M ^ k) := Real.log_le_log hpos2 hrle

end Work.TMLECore
