import Mathlib
import Submission.Work.Cert.ThetaDefs

namespace Work.Cert

open Complex Finset

/-- Splitting `thetaA q = Σ_{n≥0} q^{tri n}` (which is absolutely convergent for `‖q‖ < 1`)
after the first `13` terms: the head `Asum q 13` plus the tail re-indexed by `n ↦ n + 13`. -/
theorem thetaA_eq (q : ℂ) (hq : ‖q‖ < 1) :
    thetaA q = Asum q 13 + ∑' n : ℕ, q ^ tri (n + 13) := by
  -- absolute convergence: `‖q ^ tri n‖ = ‖q‖^{tri n} ≤ ‖q‖^n` and `∑ ‖q‖^n` converges.
  have hsum : Summable (fun n : ℕ => q ^ tri n) := by
    apply Summable.of_norm_bounded (g := fun n => ‖q‖ ^ n)
    · exact summable_geometric_of_norm_lt_one (by simpa using hq)
    · intro n
      rw [norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg q) (le_of_lt hq) (le_tri n)
  have h := Summable.sum_add_tsum_nat_add 13 hsum
  simpa [Asum, thetaA, tri] using h.symm

end Work.Cert
