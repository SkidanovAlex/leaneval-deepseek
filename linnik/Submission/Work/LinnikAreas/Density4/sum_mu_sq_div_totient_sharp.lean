import Mathlib
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs
import Submission.Work.LinnikAreas.Density4.HhBound
import Submission.Work.LinnikAreas.Density4.hh_reindex
import Submission.Work.LinnikAreas.Density4.sum_sqfree_cw_two_pow_bounds
import Submission.Work.LinnikAreas.Density4.mu_sq_div_totient_eq_hh_harmonic

open Finset BigOperators

namespace Work.LinnikAreas.Density4

/-- Sharp Mertens-type bound: `Σ_{δ ≤ z} μ(δ)²/φ(δ) ≤ log z + C` (the coefficient of `log z`
must be exactly `1`; the workspace's `sum_mu_sq_div_totient_le_log` only gives `2(1+log z)`).
Proof route: the convolution identity `n·μ(n)²/φ(n) = Σ_{e | n} e·h(e)` with the multiplicative `h`
given by `h(p) = 1/(p(p-1))`, `h(p²) = -1/(p(p-1))`, `h(p^j) = 0` for `j ≥ 3`; then
`Σ_{n ≤ z} μ(n)²/φ(n) = Σ_{e ≤ z} h(e)·H_{⌊z/e⌋}` and one uses `log M ≤ H_M ≤ 1 + log M`. -/
theorem sum_mu_sq_div_totient_sharp : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 1 ≤ z →
    (∑ δ ∈ Finset.Icc 1 z, ((ArithmeticFunction.moebius δ : ℝ)^2) / (Nat.totient δ : ℝ))
      ≤ Real.log (z : ℝ) + C := by
  obtain ⟨C, hCpos, hBdd, _hTail⟩ := sum_sqfree_cw_two_pow_bounds
  refine ⟨1 + 2 * C, by linarith, ?_⟩
  intro z hz
  have hkey := hh_reindex_sum_le C hCpos hBdd z hz
  have hid := mu_sq_div_totient_eq_hh_harmonic z
  have hrei := hh_reindex z (fun e => (harmonic (z / e) : ℝ))
  rw [hid, hrei]
  exact hkey

end Work.LinnikAreas.Density4
