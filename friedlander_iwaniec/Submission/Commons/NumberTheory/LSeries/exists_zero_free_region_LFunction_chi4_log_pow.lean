import Mathlib
import Submission.Commons.NumberTheory.LSeries.zero_free_region_LFunction_chi4
import Submission.Commons.NumberTheory.LSeries.exists_bound_deriv_LFunction_chi4_log_sq

namespace Commons.NumberTheory.LSeries

/-- **Unconditional quantitative zero-free region for `L(·,χ₄)`**: there is `c > 0` such that
`L(σ + it, χ₄) ≠ 0` whenever `2 ≤ |t|` and `σ ≥ 1 - c/(log(|t|+2))⁹`, where `χ₄` is
`Commons.NumberTheory.DirichletCharacter.chi4`.

PROOF.  Combine
`Commons.NumberTheory.LSeries.exists_bound_deriv_LFunction_chi4_log_sq`, which provides `C, d > 0`
with `‖L'(σ+it,χ₄)‖ ≤ C (log(|t|+2))²` on `1 - d/log(|t|+2) ≤ σ ≤ 1 + 1/(2log(|t|+2))`
(`2 ≤ |t|`), with `Commons.NumberTheory.LSeries.zero_free_region_LFunction_chi4`, which turns
such a derivative bound into non-vanishing for
`σ ≥ 1 - min(1/(40960 C⁴), d/2)/(log(|t|+2))⁹`. -/
theorem exists_zero_free_region_LFunction_chi4_log_pow :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 2 ≤ |t| →
      1 - c / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4
        ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨C, d, hC, hd, hderiv⟩ :=
    Commons.NumberTheory.LSeries.exists_bound_deriv_LFunction_chi4_log_sq
  -- Enlarge the constant so that it is at least `1`, as required by the parametric lemma.
  have hC1 : 1 ≤ max C 1 := le_max_right C 1
  have hmaxpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one hC1
  have hden : 0 < 40960 * (max C 1) ^ 4 := by positivity
  refine ⟨min (1 / (40960 * (max C 1) ^ 4)) (d / 2), lt_min (by positivity) (by linarith), ?_⟩
  intro σ t ht hσ
  refine Commons.NumberTheory.LSeries.zero_free_region_LFunction_chi4 (max C 1) d hC1 hd ?_ σ t ht hσ
  intro σ t ht h1 h2
  refine le_trans (hderiv σ t ht h1 h2) ?_
  exact mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)

end Commons.NumberTheory.LSeries
