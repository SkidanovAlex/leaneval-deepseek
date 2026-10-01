import Mathlib
import Submission.Work.ZeroDensity.Jutila.sum_div_sq_le

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset

/-- For `q ≥ 1` one has `q^{-3} ≤ q^{-2}`. -/
private lemma inv_cube_le_inv_sq (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) / (q : ℝ) ^ 3 ≤ (1 : ℝ) / (q : ℝ) ^ 2 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have h2 : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
    have := pow_le_pow_right₀ hq1 (by norm_num : (2 : ℕ) ≤ 3)
    simpa using this
  exact one_div_le_one_div_of_le h1 h2

theorem SumInvPowLeHere :
  (∀ Q : ℕ, (∑ q ∈ Finset.Icc 1 Q, (1:ℝ)/(q:ℝ)^3) ≤ 2)
  ∧ (∀ Q : ℕ, (∑ q ∈ Finset.Icc 1 Q, (1:ℝ)/(q:ℝ)^2) ≤ 2) := by
  refine ⟨fun Q => ?_, fun Q => ?_⟩
  · -- compare the cubic sum with the quadratic one term by term
    have hsq : (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 2 :=
      by simpa only [one_div] using sum_sq_inv_le_two Q
    exact (Finset.sum_le_sum fun q hq => inv_cube_le_inv_sq q (Finset.mem_Icc.mp hq).1).trans hsq
  · simpa only [one_div] using sum_sq_inv_le_two Q

end Work.ZeroDensity.Jutila.LzDiffAux
