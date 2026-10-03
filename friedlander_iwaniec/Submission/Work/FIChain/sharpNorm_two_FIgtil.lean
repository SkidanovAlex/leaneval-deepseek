/-
# `Work.FIChain.sharpNorm_two_FIgtil`

The sharp "two-dimensional" norm of the §6 sieve density of the FI sequence: over any window
`w ≤ p < z'` of primes, the product of the local factors `(1 − g̃(p)·h(p))⁻¹` is

    O( (log z' / log w)² ),

uniformly in the sieve level `Δ ≥ z'` and in the truncation parameter `ε = 1/log Δ` implicit in
`hSieveC g̃ ε`.

## Why the exponent `2` is the right sharp value

Write `g̃ = Submission.ASP.FIgtil` and `t_p = p^{-1/log Δ} ∈ (0,1]`.  At a prime,

    hSieveC g̃ ε p = (1 + t_p)/(1 + t_p·g̃(p)),
    (1 − g̃(p)·hSieveC g̃ ε p)⁻¹ = (1 + t_p·g̃(p))/(1 − g̃(p)),

so

    log ∏_{w ≤ p < z'} (1 − g̃ p · h p)⁻¹
      = ∑_{w ≤ p < z'} log(1 + t_p g̃ p) − ∑_{w ≤ p < z'} log(1 − g̃ p)
      ≤ 2 ∑_{w ≤ p < z'} g̃ p + O(1),

because `t_p ≤ 1` and `−log(1 − u) = u + O(u²)` with `∑ g̃(p)² = O(1)` (a pure `1/p²`-sum).
The density satisfies the second-Mertens relation

    ∑_{p ≤ y} g̃ p = log log y + O(1)

(`Submission.ASP.FIgtil_sum_19_nat`, proved in the workspace), so the window sum is
`log log z' − log log w + O(1) = log(log z'/log w) + O(1)`, and exponentiating gives the exponent
`2`.  The two numerical consequences used below are therefore exactly the sharp ones; a weaker
`−log(1−u) ≤ 3u` would give the false exponent `4`.

## The three analytic inputs (delegated, proved separately)

* `Work.FIChain.window_sum_FIgtil_le` — `∑_{window} g̃ p ≤ log log z' − log log w + C`;
* `Work.FIChain.sum_sq_FIgtil_le` — `∑_{p < Δ} g̃(p)² ≤ C`;
* `Work.FIChain.prod_inv_le_of_window_bounds` — the assembly of the product from these two
  (it contains the pointwise step `Work.FIChain.sieveFactor_inv_le_exp`).

Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S27
import Submission.Work.FIChain.window_sum_FIgtil_le
import Submission.Work.FIChain.sum_sq_FIgtil_le
import Submission.Work.FIChain.prod_inv_le_of_window_bounds

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem sharpNorm_two_FIgtil :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ → ∀ w z' : ℝ, 2 ≤ w → w < z' → z' ≤ (Δ : ℝ) →
      (∏ p ∈ (Nat.primesBelow Δ).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
          (1 - Submission.ASP.FIgtil p
            * Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p)⁻¹)
        ≤ K * (Real.log z' / Real.log w) ^ (2 : ℝ) := by
  obtain ⟨Cw, _hCw0, hCw⟩ := window_sum_FIgtil_le
  obtain ⟨Cs, _hCs0, hCs⟩ := sum_sq_FIgtil_le
  refine ⟨Real.exp (2 * Cw + 3 * Cs) + 1, by positivity, ?_⟩
  intro Δ hΔ w z' hw hwz hzΔ
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith : (1 : ℝ) < w)
  have hlogz : 0 < Real.log z' := Real.log_pos (by linarith : (1 : ℝ) < z')
  have hratio : 0 ≤ Real.log z' / Real.log w := by positivity
  have h := prod_inv_le_of_window_bounds Δ hΔ w z' hw hwz hzΔ
    (hCw Δ w z' hw hwz hzΔ) (hCs Δ)
  refine le_trans h (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hratio 2))
  linarith [Real.exp_pos (2 * Cw + 3 * Cs)]

end

end Work.FIChain
