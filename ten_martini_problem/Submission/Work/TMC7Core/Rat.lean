import Submission.Work.TMC7Core.Cocycle

/-!
# TMC7Core: the spectral radius of `SL(2,ℝ)` matrices via the trace

For `M ∈ SL(2,ℝ)` with real trace `τ` the eigenvalues are `(τ ± √(τ²−4))/2`; the spectral
radius is `1` when `|τ| ≤ 2` (elliptic) and `(|τ| + √(τ²−4))/2` when `|τ| ≥ 2` (hyperbolic).
`rhoSL` is that function of `τ` alone, which is what the rational (periodic) side of C7
needs: for rational frequency the Lyapunov exponent is the average of `log (rhoSL (tr A_q))`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core

/-- Spectral radius of an `SL(2,ℝ)` matrix with trace `τ`. -/
def rhoSL (τ : ℝ) : ℝ := if 2 ≤ |τ| then (|τ| + Real.sqrt (τ ^ 2 - 4)) / 2 else 1

theorem rhoSL_nonneg (τ : ℝ) : 0 ≤ rhoSL τ := by
  rw [rhoSL]
  split_ifs with h
  · have h1 : 0 ≤ |τ| := abs_nonneg τ
    have h2 : 0 ≤ Real.sqrt (τ ^ 2 - 4) := Real.sqrt_nonneg _
    positivity
  · norm_num

theorem rhoSL_one_le (τ : ℝ) : 1 ≤ rhoSL τ := by
  rw [rhoSL]
  split_ifs with h
  · have hτ : 4 ≤ τ ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
    have h2 : 0 ≤ Real.sqrt (τ ^ 2 - 4) := Real.sqrt_nonneg _
    linarith
  · norm_num

theorem rhoSL_le (τ : ℝ) : rhoSL τ ≤ max 1 |τ| := by
  rw [rhoSL]
  split_ifs with h
  · have h2 : Real.sqrt (τ ^ 2 - 4) ≤ |τ| := by
      rw [Real.sqrt_le_iff]
      exact ⟨abs_nonneg τ, by nlinarith [sq_abs τ]⟩
    have h3 : 1 ≤ |τ| := by linarith
    rw [max_eq_right h3]
    linarith
  · exact le_max_left _ _

theorem log_rhoSL_le_log_abs (τ : ℝ) :
    Real.log (rhoSL τ) ≤ max 0 (Real.log |τ|) := by
  have h1 : 1 ≤ rhoSL τ := rhoSL_one_le τ
  have h2 : rhoSL τ ≤ max 1 |τ| := rhoSL_le τ
  have h3 : Real.log (rhoSL τ) ≤ Real.log (max 1 |τ|) := Real.log_le_log (by linarith) h2
  have h4 : Real.log (max 1 |τ|) ≤ max 0 (Real.log |τ|) := by
    rcases le_total 1 |τ| with h | h
    · rw [max_eq_right h, max_eq_right (Real.log_nonneg h)]
    · rw [max_eq_left h, max_eq_left (by exact Real.log_nonpos (abs_nonneg τ) h), Real.log_one]
  linarith

end Work.TMC7Core
