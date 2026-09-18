import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.PrimeCounting

open scoped BigOperators

namespace Commons.NumberTheory.Mertens

/-- Lower bound for `log (p/(p-1))` coming from the artanh power series
(`Real.sum_range_le_log_div` with `x = 1/(2p-1)`):
`2 * Σ_{i<n} (1/(2p-1))^(2i+1)/(2i+1) ≤ log (p/(p-1))`. -/
theorem log_div_pred_ge_artanh (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, (1 / (2 * (p:ℝ) - 1)) ^ (2 * i + 1) / (2 * i + 1)) ≤
      Real.log ((p:ℝ) / ((p:ℝ) - 1)) := by
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hden : (0:ℝ) < 2 * (p:ℝ) - 1 := by linarith
  have hx0 : 0 ≤ 1 / (2 * (p:ℝ) - 1) := by positivity
  have hx1 : 1 / (2 * (p:ℝ) - 1) < 1 := by
    rw [div_lt_one hden]; linarith
  have h := Real.sum_range_le_log_div hx0 hx1 n
  have h2 : 2 * (∑ i ∈ Finset.range n, (1 / (2 * (p:ℝ) - 1)) ^ (2 * i + 1) / (2 * i + 1)) ≤
      Real.log ((1 + 1/(2*(p:ℝ)-1)) / (1 - 1/(2*(p:ℝ)-1))) := by
    have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)
    have e : 2 * (1/2 * Real.log ((1 + 1/(2*(p:ℝ)-1)) / (1 - 1/(2*(p:ℝ)-1)))) =
        Real.log ((1 + 1/(2*(p:ℝ)-1)) / (1 - 1/(2*(p:ℝ)-1))) := by ring
    linarith [h']
  have hid : (1 + 1/(2*(p:ℝ)-1)) / (1 - 1/(2*(p:ℝ)-1)) = (p:ℝ)/((p:ℝ)-1) := by
    have hD : (2:ℝ)*(p:ℝ)-1 ≠ 0 := by linarith
    have hp1 : (p:ℝ)-1 ≠ 0 := by linarith
    rw [div_eq_div_iff]
    · field_simp
      ring
    · have : 1/(2*(p:ℝ)-1) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    · exact hp1
  rw [hid] at h2
  exact h2

theorem corr_sum_100_ge_3146 :
    (0.3146 : ℝ) ≤ ∑ p ∈ Nat.primesLE 100,
      (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ)) := by
  have hterm : ∀ p ∈ Nat.primesLE 100,
      (2 * (∑ i ∈ Finset.range 4, (1 / (2 * (p:ℝ) - 1)) ^ (2*i+1) / (2*i+1)) - 1/(p:ℝ))
        ≤ (Real.log ((p:ℝ) / ((p:ℝ) - 1)) - 1 / (p:ℝ)) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
    have h := log_div_pred_ge_artanh p hp2 4
    linarith
  have hnum : (0.3146 : ℝ) ≤ ∑ p ∈ Nat.primesLE 100,
      (2 * (∑ i ∈ Finset.range 4, (1 / (2 * (p:ℝ) - 1)) ^ (2*i+1) / (2*i+1)) - 1/(p:ℝ)) := by
    have hprimes : Nat.primesLE 100 =
        ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} : Finset ℕ) := by
      decide
    rw [hprimes]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hsum : (∑ p ∈ Nat.primesLE 100,
        (2 * (∑ i ∈ Finset.range 4, (1 / (2 * (p:ℝ) - 1)) ^ (2*i+1) / (2*i+1)) - 1/(p:ℝ)))
      ≤ ∑ p ∈ Nat.primesLE 100,
        (Real.log ((p:ℝ) / ((p:ℝ) - 1)) - 1 / (p:ℝ)) :=
    Finset.sum_le_sum hterm
  linarith

end Commons.NumberTheory.Mertens