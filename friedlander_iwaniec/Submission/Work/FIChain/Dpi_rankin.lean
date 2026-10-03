/-
# `Submission.Work.FIChain.Dpi_rankin` — Rankin's trick for the `Δπ`-divisor tail

The companion paper's §10 splits the inner variable as `n = n₀ n₁` with `n₁ ∣ Π = ∏_{p ≤ Pz} p`
and absorbs `n₁ ≤ Δπ` by the smoothing, while the tail `n₁ > Δπ` is estimated by **Rankin's
trick**: for any `σ > 0`

`∑_{d ∣ Π, d > Δ} τ(d)^k / d ≤ Δ^{-σ} ∏_{p ≤ Pz} (1 + 2^k p^{σ-1}) .

Choosing `σ = 1/(2 (log log x)²)` and using `Δ ≥ exp(κ (log log x)³)`, `log Pz ≤ 2(log log x)²`
together with Mertens' bound `∑_{p ≤ Pz} 1/p ≤ log log Pz + O(1)`, the right-hand side is

`(log x)^{-κ/2} · exp(O(2^k)) · (log Pz)^{2^k}`,

which is dominated by `(log x)^{-κ/2} (log Pz)^{2^{k+3}}` because `2^k · e < 2^{k+3}`.

The three ingredients are proved in the sibling files
`dpi_sum_eq_subset_sum`, `rankin_dpi_sum_le` and `prod_primes_one_add_le`; this file assembles
them into the requested statement.
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FIChain.dpi_sum_eq_subset_sum
import Submission.Work.FIChain.rankin_dpi_sum_le
import Submission.Work.FIChain.prod_primes_one_add_le

set_option maxHeartbeats 800000

namespace Work.FIChain

open Finset
open scoped BigOperators

theorem Dpi_rankin (k : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x Pz : ℕ, X₀ ≤ x → 2 ≤ Pz →
      2 ≤ Real.log (Real.log (x : ℝ)) →
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
      Real.log (Pz : ℝ) ≤ 2 * (Real.log (Real.log (x : ℝ))) ^ 2 →
      (∑ d ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun d => Work.FIChain.Dpi x κ < d),
          ((d.divisors.card : ℝ)) ^ k / (d : ℝ))
        ≤ C * (Real.log (x : ℝ)) ^ (-(κ / 2)) * (Real.log (Pz : ℝ)) ^ (2 ^ (k + 3) : ℕ) := by
  obtain ⟨Cm, hCm0, hCm⟩ := prod_primes_one_add_le k
  refine ⟨Cm, hCm0, 3, ?_⟩
  intro x Pz hx3 hPz hL2 hLP hLP2
  have hlogx_pos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  rw [dpi_sum_eq_subset_sum k κ x Pz]
  have hR := rankin_dpi_sum_le k κ x Pz hκ hL2
  have hP := hCm x Pz hPz hL2 hLP hLP2
  have hnonneg : 0 ≤ (Real.log (x : ℝ)) ^ (-(κ / 2)) := Real.rpow_nonneg hlogx_pos.le _
  have hstep : (Real.log (x : ℝ)) ^ (-(κ / 2)) * (Cm * (Real.log (Pz : ℝ)) ^ ((2 : ℝ) ^ (k + 3)))
      = Cm * (Real.log (x : ℝ)) ^ (-(κ / 2)) * (Real.log (Pz : ℝ)) ^ (2 ^ (k + 3) : ℕ) := by
    have hexp : (2 : ℝ) ^ (k + 3) = ((2 ^ (k + 3) : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast]
    ring
  exact le_trans (le_trans hR (mul_le_mul_of_nonneg_left hP hnonneg)) (le_of_eq hstep)

end Work.FIChain
