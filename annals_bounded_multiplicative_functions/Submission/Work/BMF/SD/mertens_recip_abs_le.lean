import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Work.BMF.liouville.mertens_recip_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Finset Real

/-- **Mertens' second theorem, two-sided uniform form.**

`∑_{p ≤ x} 1/p = log log x + O(1)`: there is a constant `D ≥ 0` with
`|∑_{p ≤ ⌊x⌋} 1/p − log log x| ≤ D` for every real `x ≥ 2`.

The bound for `x ≥ 11` is imported from the shared library
(`Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`, proved from the
convergence of `∑ 1/p − log log x`); the compact range `2 ≤ x < 11` is handled
by monotonicity of the partial sums (`⌊x⌋ < 11` implies the prime set is a
subset of the primes `≤ 11`) together with the monotonicity of `log log` on
`[log 2, log 11]`. -/
theorem mertens_recip_abs_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x)| ≤ D := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  set B : ℝ := ∑ p ∈ Nat.primesLE 11, (1 : ℝ) / (p : ℝ) with hB
  set L : ℝ := |Real.log (Real.log 2)| + |Real.log (Real.log 11)| with hL
  have hBnonneg : 0 ≤ B := by
    rw [hB]; exact Finset.sum_nonneg (fun p _ => by positivity)
  have hLnonneg : 0 ≤ L := by
    rw [hL]; positivity
  refine ⟨C + (B + L), by linarith, ?_⟩
  intro x hx2
  by_cases hx11 : 11 ≤ x
  · exact le_trans (hC x hx11) (by linarith)
  · -- compact range `2 ≤ x < 11`
    have hx11' : x ≤ 11 := le_of_lt (not_le.mp hx11)
    have hfloor : ⌊x⌋₊ ≤ 11 := by
      have h : ⌊x⌋₊ < 11 := (Nat.floor_lt' (by norm_num : (11 : ℕ) ≠ 0)).mpr (not_le.mp hx11)
      omega
    have hsub : (⌊x⌋₊).primesLE ⊆ Nat.primesLE 11 := Nat.primesLE_mono hfloor
    have hSle : (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) ≤ B := by
      rw [hB]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    have hSnonneg : 0 ≤ (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) :=
      Finset.sum_nonneg (fun p _ => by positivity)
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlo : Real.log (Real.log 2) ≤ Real.log (Real.log x) :=
      Real.log_le_log hlog2pos (Real.log_le_log (by norm_num) hx2)
    have hhi : Real.log (Real.log x) ≤ Real.log (Real.log 11) :=
      Real.log_le_log hlogxpos (Real.log_le_log (by linarith) hx11')
    have hLbound : |Real.log (Real.log x)| ≤ L := by
      rw [hL]
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 := neg_abs_le (Real.log (Real.log 2))
        have h2 := abs_nonneg (Real.log (Real.log 11))
        linarith
      · have h1 := le_abs_self (Real.log (Real.log 11))
        have h2 := abs_nonneg (Real.log (Real.log 2))
        linarith
    have htri : |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x)|
        ≤ (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) + |Real.log (Real.log x)| := by
      calc |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x)|
          = |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) + (-Real.log (Real.log x))| := by
            rw [sub_eq_add_neg]
        _ ≤ |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ))| + |-Real.log (Real.log x)| :=
            abs_add_le _ _
        _ = (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) + |Real.log (Real.log x)| := by
            rw [abs_of_nonneg hSnonneg, abs_neg]
    calc |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x)|
        ≤ (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) + |Real.log (Real.log x)| := htri
      _ ≤ B + L := add_le_add hSle hLbound
      _ ≤ C + (B + L) := by linarith

end Work.BMF.SD
