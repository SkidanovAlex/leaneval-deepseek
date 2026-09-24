import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic
import Submission.Work.ChenPlan.LinearSieve.Buchstab.moebius_identity
import Submission.Work.LinearSieve.Selberg.error_bound
import Submission.Work.LinearSieve.Selberg.optimal_weights

/-!
# Selberg's `Λ²` upper bound sieve, assembled

Combining
* the existence of Selberg's optimal truncated weights (`Work.LinearSieve.Selberg.optimal_weights`),
* the `3^{ω(d)}` error bound for `λ²` weights (`Work.LinearSieve.Selberg.error_bound`),
* Mathlib's `siftedSum_le_mainSum_errSum_of_upperMoebius` + `upperMoebius_lambdaSquared`,

every linear sieve problem satisfies, at *every* level `ξ > 1`,

  `S(A,z) ≤ X / G(ξ,z) + Σ_{d < ξ², d ∣ P} 3^{ω(d)} |r_d|`,  `G(ξ,z) = Σ_{d < ξ} h(d)`.

This is the starting point of the Jurkat–Richert iteration; the remaining input is the lower bound
`G(ξ,z) · V ≥ σ(2 log ξ / log z) - o(1)` (Ankeny–Onishi), see `PLAN.md` for the traps in it.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve

/-- The truncated Selberg sum `G(ξ,z)` is positive for `ξ > 1` (its `d = 1` term is `h(1) = 1`). -/
theorem gSum_pos (s : BoundingSieve) {ξ : ℝ} (hξ : 1 < ξ) : 0 < gSum s ξ := by
  have h1 : (1 : ℕ) ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < ξ) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, s.prodPrimes_ne_zero⟩, by exact_mod_cast hξ⟩
  have hnonneg : ∀ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < ξ),
      0 ≤ (s.selbergTerms) d := by
    intro d hd
    exact le_of_lt (BoundingSieve.selbergTerms_pos
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1)
  have hone : (s.selbergTerms) (1 : ℕ) = 1 := by
    rw [BoundingSieve.selbergTerms_apply]
    simp [ArithmeticFunction.IsMultiplicative.map_one s.nu_mult]
  have hle : (s.selbergTerms) (1 : ℕ) ≤ gSum s ξ := by
    rw [gSum]
    exact Finset.single_le_sum hnonneg h1
  rw [hone] at hle
  exact lt_of_lt_of_le zero_lt_one hle

/-- `remSelberg` at level `ξ` is the interface remainder sum at `D = ξ²`. -/
theorem remSelberg_eq_remSum (s : BoundingSieve) (ξ : ℝ) :
    remSelberg s ξ = Submission.ChenPlan.remSum s (ξ ^ 2) := rfl

/-- Mathlib's `errSum` for `λ²` weights is the local `lambdaErrSum`. -/
theorem errSum_lambdaSquared_eq (s : BoundingSieve) (w : ℕ → ℝ) :
    s.errSum (BoundingSieve.lambdaSquared w) = lambdaErrSum s w := rfl

/-- **Selberg's `Λ²` upper bound**, for every level `ξ > 1` and every nonnegative total mass. -/
theorem selberg_bound (s : BoundingSieve) {ξ : ℝ} (hξ : 1 < ξ) (hX : 0 ≤ s.totalMass) :
    s.siftedSum ≤ s.totalMass / gSum s ξ + Submission.ChenPlan.remSum s (ξ ^ 2) := by
  obtain ⟨w, hw1, hwabs, -, hwsupp, hmain⟩ :=
    Work.LinearSieve.Selberg.optimal_weights s hξ
  have hGpos : 0 < gSum s ξ := gSum_pos s hξ
  have hmain' : s.mainSum (BoundingSieve.lambdaSquared w) ≤ 1 / gSum s ξ := by
    rw [le_div_iff₀ hGpos]
    exact hmain
  have hupper : BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared w) :=
    BoundingSieve.upperMoebius_lambdaSquared w hw1
  have hstep := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (s := s) (BoundingSieve.lambdaSquared w) hupper
  have herr : s.errSum (BoundingSieve.lambdaSquared w) ≤ remSelberg s ξ :=
    Work.LinearSieve.Selberg.error_bound s (le_of_lt (by linarith : (0 : ℝ) < ξ)) hwabs hwsupp
  have hmul : s.totalMass * s.mainSum (BoundingSieve.lambdaSquared w)
      ≤ s.totalMass * (1 / gSum s ξ) :=
    mul_le_mul_of_nonneg_left hmain' hX
  rw [remSelberg_eq_remSum] at herr
  have := add_le_add hmul herr
  rw [mul_one_div] at hmul
  linarith [hstep, hmul]

end Work.ChenPlan.LinearSieve
