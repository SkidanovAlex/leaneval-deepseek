import Mathlib
import Submission.Work.LinnikAreas.Density4.LFunction_one_apply_one

/-!
# The value at `s = 1` of the `L`-function of the trivial character is nonzero

For the trivial (principal) Dirichlet character `χ₀ = 1` modulo `q ≥ 2`, the `L`-function
has a pole at `s = 1`; Mathlib's `DirichletCharacter.LFunction` (a linear combination of
Hurwitz zeta functions) nevertheless assigns a definite value to `s = 1`, namely
(see `Work.LinnikAreas.Density4.LFunction_one_apply_one`)

`L(1, χ₀) = (∏_{p | q} (1 - p⁻¹)) * (log q + ζ(1) + ∑_{p | q} log p / (p - 1))`,

where `ζ(1) = (γ - log 4π)/2` is Mathlib's value of `riemannZeta` at `1`.

The first factor is a nonzero complex number.  For the second we show that its real value is
positive: `log 4 ≤ log q + ∑_{p | q} log p/(p - 1)` always holds for `q ≥ 2` (the cases
`2 | q`, `3 | q`, and the rest), and therefore

`log q + (γ - log 4π)/2 + ∑_{p | q} log p/(p - 1) ≥ log 4 + (γ - log 4π)/2
   = (log(4/π) + γ)/2 > 0`,

using `π < 4` and `γ > 1/2`.  Hence `LFunction 1 1 ≠ 0`.
-/

namespace Work.LinnikAreas.BGTZ

/-- The weighted log-sum `∑_{p | q} log p / (p - 1)` over the prime factors of `q` is
nonnegative. -/
lemma detTriv_primeFactors_weightedLogSum_nonneg (q : ℕ) :
    0 ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)

/-- For every `q ≥ 2` we have `log 4 ≤ log q + ∑_{p | q} log p / (p - 1)`.

The three cases are `2 ∣ q` (then `log q + log 2 ≥ 2 log 2 = log 4`), `2 ∤ q` and `3 ∣ q`
(then `log q + log 3 / 2 ≥ (3/2) log 3 = log(√27) > log 4`), and `2 ∤ q`, `3 ∤ q` (then
`q ≥ 5` so `log q ≥ log 5 > log 4`). -/
lemma detTriv_log_four_le (q : ℕ) (hq : 2 ≤ q) :
    Real.log 4 ≤ Real.log q + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  have hnn : ∀ i ∈ q.primeFactors, 0 ≤ Real.log (i : ℝ) / ((i : ℝ) - 1) := by
    intro i hi
    have hi2 : (2 : ℝ) ≤ i := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hi).two_le
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  by_cases h2 : 2 ∣ q
  · have hmem : 2 ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, by omega⟩
    have hsum := Finset.single_le_sum (s := q.primeFactors)
      (f := fun p : ℕ => Real.log (p : ℝ) / ((p : ℝ) - 1)) hnn hmem
    simp only [Nat.cast_ofNat] at hsum
    have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h4]
    linarith
  · by_cases h3 : 3 ∣ q
    · have hmem : 3 ∈ q.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, by omega⟩
      have hsum := Finset.single_le_sum (s := q.primeFactors)
        (f := fun p : ℕ => Real.log (p : ℝ) / ((p : ℝ) - 1)) hnn hmem
      simp only [Nat.cast_ofNat] at hsum
      have hq3 : 3 ≤ q := by
        by_contra h
        have : q = 2 := by omega
        exact h2 (by rw [this])
      have hlogq : Real.log 3 ≤ Real.log q :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
      have h43 : 2 * Real.log 4 ≤ 3 * Real.log 3 := by
        have h16 : Real.log ((4 : ℝ) ^ 2) ≤ Real.log ((3 : ℝ) ^ 3) :=
          Real.log_le_log (by norm_num) (by norm_num)
        rw [Real.log_pow, Real.log_pow] at h16
        push_cast at h16
        linarith
      linarith
    · have hq5 : 5 ≤ q := by
        by_contra h
        have h4 : q ≤ 4 := by omega
        interval_cases q
        · exact h2 (dvd_refl 2)
        · exact h3 (dvd_refl 3)
        · exact h2 (by norm_num : 2 ∣ 4)
      have hlogq : Real.log 4 ≤ Real.log q :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ q))
      have hnn2 := detTriv_primeFactors_weightedLogSum_nonneg q
      linarith

theorem DetTrivCharValue (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) 1 ≠ 0 := by
  rw [Work.LinnikAreas.Density4.LFunction_one_apply_one q hq]
  refine mul_ne_zero ?_ ?_
  · -- the Euler product factor `∏_{p | q} (1 - p⁻¹)` is nonzero
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hpne : (p : ℂ) ≠ 1 := by
      intro h
      have : p = 1 := by exact_mod_cast h
      omega
    exact sub_ne_zero.mpr (Ne.symm fun h => hpne (inv_eq_one.mp h))
  · -- the second factor is a positive real number
    have hγ : 0 < Real.eulerMascheroniConstant :=
      lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
    have hpos2 : 0 < Real.log 4 + (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 := by
      have hlt : Real.log (4 * Real.pi) < Real.log 16 :=
        Real.log_lt_log (by positivity) (by nlinarith [Real.pi_lt_four])
      have hlog16 : Real.log 16 = 2 * Real.log 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      linarith
    have hmain : 0 < Real.log q + (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
        + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
      have := detTriv_log_four_le q hq
      linarith
    have hcast :
        ((↑(Real.log (q : ℝ)) : ℂ) + riemannZeta 1
            + ∑ p ∈ q.primeFactors, (↑(Real.log (p : ℝ) / ((p : ℝ) - 1)) : ℂ))
          = ((Real.log q + (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
              + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) := by
      have hlog : (4 : ℂ) * ↑Real.pi = ↑(4 * Real.pi) := by
        push_cast
        ring
      rw [riemannZeta_one, hlog, ← Complex.ofReal_log (show (0 : ℝ) ≤ 4 * Real.pi by positivity)]
      push_cast
      ring
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr hmain.ne'

end Work.LinnikAreas.BGTZ
