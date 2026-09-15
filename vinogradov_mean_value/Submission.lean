import ChallengeDeps
import Submission.Vinogradov.Main

open LeanEval.NumberTheory.VinogradovMeanValue

set_option autoImplicit false

namespace Submission

open Submission.Vinogradov

/-- The Vinogradov mean value theorem (main conjecture).  The proof is
assembled from the elementary regimes (`k = 0`, `k = 1`, `s ≤ k`), the
classical quadratic case `k = 2`, and the deep core (`3 ≤ k`, `s ≥ k + 1`,
Wooley / Bourgain–Demeter–Guth). -/
theorem vinogradov_mean_value (s k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    J s k =O[Filter.atTop]
      fun X ↦ (X ^ (s + ε) + X ^ ((2 * s : ℝ) - k * (k + 1) / 2 + ε) : ℝ) := by
  by_cases hk0 : k = 0
  · subst k
    exact vmvt_k0 s ε hε
  · have hk1pos : 1 ≤ k := by omega
    by_cases hk1 : k = 1
    · subst k
      exact vmvt_k1 s ε hε
    · have hk2 : 2 ≤ k := by omega
      by_cases hk2' : k = 2
      · subst k
        exact vmvt_k2 s ε hε
      · have hk3 : 3 ≤ k := by omega
        by_cases hs : s ≤ k
        · exact vmvt_short s k hs ε hε
        · have hcore : k + 1 ≤ s := by omega
          exact core_vinogradov s k hk3 hcore ε hε

end Submission
