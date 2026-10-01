/-
# ZeroFreeTables/Rep9/principalBoundAmended — the amended (repaired) principal bound of HB §9

The requested `Rep9.principalBound` is false (see `Rep9/principalBound.lean`, `Rep9/NOTES.md`,
`Rep9/REFUTATION.md`): it bounds `λ₁` by a *free*, universally quantified `M`, which makes the
conclusion uniform in the shift `α = a + λ₁`, whereas the discrepancy is a cubic in `α` (the
cubic coefficient being `(1/3)L⁻³Re(-ζ'/ζ)''(s) > 0` for `|Im s| = 3`, versus `O(L⁻⁴)` on the
right).  The repair — the same one as `Rep9/principalBoundM.lean`, with `M` a *parameter* so
that `L₀` may depend on the bound on `λ₁` — is *proved* here from
`Rep9/principalRepair.principalBoundM_of_bounds` and its three analytic inputs:

* `P9.zetaCorrector_three_bounds` — the two-sided bounds for `-ζ'/ζ - 1/(z-1)` and its two
  derivatives on `1 < Re s ≤ 2, |Im s| ≤ 5`;
* `Rep9.principalSigmaDiff` — the contribution of the primes dividing `q`;
* `Rep9.shiftAbsorb` — the absorption of the corrections into `α·e` (proved).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Rep9.principalRepair
import Submission.Work.ZeroFreeTables.Rep9.principalSigmaDiff
import Submission.Work.ZeroFreeTables.Rep9.shiftAbsorb
import Submission.Work.ZeroFreeTables.P9.zetaCorrector_three_bounds

open DirichletCharacter Complex
open scoped BigOperators

namespace Work.ZeroFreeTables.Rep9

/-- **The amended principal bound of HB §9** (`Rep9.principalBoundM`, with the shift bound as a
parameter): for `a, e > 0` and any bound `M` on `λ₁` there is `L₀` such that for `L ≥ L₀`
(and `log q ≤ L`) the principal-character functional is bounded by the pole term plus `α·e`. -/
theorem principalBoundAmended {a e M : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ}, L₀ ≤ L → Real.log (q:ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ M →
      ∀ s : ℂ, s.re = 1 + a/L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
          ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
              + (a + lam₁) * e := by
  by_cases hM : 0 ≤ M
  · exact principalBoundM_of_bounds (a := a) (e := e) (M := M) ha hM he
      (Work.ZeroFreeTables.P9.zetaCorrector_three_bounds) (principalSigmaDiff ha hM)
      (fun C C' hC hC' => shiftAbsorb (a := a) (M := M) (e := e) ha hM he hC hC')
  · refine ⟨0, ?_⟩
    intro q _inst L lam₁ hL hlogq hlam0 hlamM s hsre hsim
    exact absurd (le_trans hlam0 hlamM) hM

end Work.ZeroFreeTables.Rep9
