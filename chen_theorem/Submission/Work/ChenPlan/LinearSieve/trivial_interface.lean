import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic
import Submission.Work.ChenPlan.LinearSieve.trivial_case
import Submission.Work.ChenPlan.LinearSieve.Utab.one_le_Utab

/-!
# The `D > P` half of the linear-sieve interface, unconditionally

`LinearSieveUpper` and `LinearSieveLower` are stated for all levels `D ≥ D₀`.  When the level
exceeds the modulus `P = s.prodPrimes` no sieve theory is needed: the exact Möbius identity
`S = X V + Σ_{d ∣ P} μ(d) r_d` plus `|μ| ≤ 1 ≤ 3^{ω(d)}` and `D > P` (so that *all* divisors of `P`
appear in `remSum`) give both inequalities outright.

Hence `linear_sieve` follows from its `D ≤ P` (equivalently `logs ≤ log P / log z`) half; the
remaining mathematics is the Selberg/`σ` main term, the fundamental lemma and the Jurkat–Richert
iterations — see `PLAN.md`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve

/-- `sieveV` is positive. -/
theorem sieveV_pos (s : BoundingSieve) : 0 < Submission.ChenPlan.sieveV s := by
  rw [Submission.ChenPlan.sieveV]
  refine Finset.prod_pos fun p hp => ?_
  have hpP : p ∣ s.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
  have := s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpP
  linarith

/-- Upper bound of the interface, in the regime `D > P`. -/
theorem upper_of_prodPrimes_lt (s : BoundingSieve) {z D η : ℝ}
    (hD : (s.prodPrimes : ℝ) < D) (hX : 0 ≤ s.totalMass) (hz : 1 < z) (hη : 0 ≤ η) :
    s.siftedSum ≤ s.totalMass * Submission.ChenPlan.sieveV s
        * (Submission.ChenPlan.Utab (Real.log D / Real.log z) + η)
      + Submission.ChenPlan.remSum s D := by
  have htriv := siftedSum_le_trivial s hD
  have hVpos : 0 < Submission.ChenPlan.sieveV s := sieveV_pos s
  have hVnn : 0 ≤ s.totalMass * Submission.ChenPlan.sieveV s := mul_nonneg hX hVpos.le
  have hP1 : (1 : ℕ) ≤ s.prodPrimes := Nat.one_le_iff_ne_zero.mpr s.prodPrimes_ne_zero
  have hD1 : (1 : ℝ) < D := lt_of_le_of_lt (by exact_mod_cast hP1) hD
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hs : 0 < Real.log D / Real.log z := div_pos hlogD hlogz
  have h1 : 1 ≤ Submission.ChenPlan.Utab (Real.log D / Real.log z) + η := by
    have := Work.ChenPlan.LinearSieve.Utab.one_le_Utab hs
    linarith
  have hmul : s.totalMass * Submission.ChenPlan.sieveV s
      ≤ s.totalMass * Submission.ChenPlan.sieveV s * (Submission.ChenPlan.Utab (Real.log D / Real.log z) + η) := by
    simpa using mul_le_mul_of_nonneg_left h1 hVnn
  linarith [htriv, hmul]

/-- Lower bound of the interface, in the regime `D > P`. -/
theorem lower_of_prodPrimes_lt (s : BoundingSieve) {D c : ℝ}
    (hD : (s.prodPrimes : ℝ) < D) (hX : 0 ≤ s.totalMass) (hc : c ≤ 1) :
    s.totalMass * Submission.ChenPlan.sieveV s * c - Submission.ChenPlan.remSum s D
      ≤ s.siftedSum :=
  trivial_le_siftedSum s hD hX hc

end Work.ChenPlan.LinearSieve
