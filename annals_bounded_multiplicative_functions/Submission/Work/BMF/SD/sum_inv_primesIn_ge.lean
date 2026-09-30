import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.mertens_recip_abs_le
import Submission.Work.BMF.SD.sum_primesIn_eq
import Submission.Work.BMF.SD.loglog_floor_le
import Submission.Work.BMF.SD.loglog_ceil_pred_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Finset Real

/-- Mertens-type lower bound: `∑_{p ∈ [P,Q]} 1/p ≥ log(log Q / log P) − C`.  Available inputs:
`Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`
(`|∑_{p ≤ x} 1/p − log log x| ≤ C` for `x ≥ 11`) and
`Submission.Work.BMF.liouville.mertens_recip_le` (the upper bound for `x ≥ 3`);
`Work.BMF.primesIn P Q = (Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).filter Nat.Prime`. -/
theorem sum_inv_primesIn_ge :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      Real.log (Real.log Q / Real.log P) - C ≤
        ∑ p ∈ Work.BMF.primesIn P Q, (1 : ℝ) / (p : ℝ) := by
  -- Two-sided Mertens bound `|∑_{p ≤ x} 1/p − log log x| ≤ D` for all `x ≥ 2`.
  obtain ⟨D, hD0, hAb⟩ := mertens_recip_abs_le
  refine ⟨Real.log 2 + 2 * D + |Real.log (Real.log 2)|, ?_, ?_⟩
  · have h1 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have h2 : 0 ≤ 2 * D := by linarith
    have h3 : 0 ≤ |Real.log (Real.log 2)| := abs_nonneg _
    linarith
  · intro P Q hP hPQ
    have hP1 : (1 : ℝ) < P := by linarith
    have hQ1 : (1 : ℝ) < Q := by linarith
    have hlogPpos : 0 < Real.log P := Real.log_pos hP1
    have hlogQpos : 0 < Real.log Q := Real.log_pos hQ1
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    -- `log log 2 ≤ log log P` since `2 ≤ P`.
    have hloglogP_ge : Real.log (Real.log 2) ≤ Real.log (Real.log P) :=
      Real.log_le_log hlog2pos (Real.log_le_log (by norm_num) hP)
    have hQ2 : (2 : ℝ) ≤ Q := le_trans hP hPQ
    have hb2 : 2 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ2)
    have hn2 : 2 ≤ ⌈P⌉₊ := by
      have h : ⌈(2 : ℝ)⌉₊ ≤ ⌈P⌉₊ := Nat.ceil_mono hP
      simpa using h
    -- Split the sum over `primesIn P Q` into a difference of prime-reciprocal sums.
    have hsum := sum_primesIn_eq P Q hP hPQ (fun p : ℕ => (1 : ℝ) / (p : ℝ))
    -- Lower bound at the upper endpoint `⌊Q⌋₊`.
    have hb_ge : Real.log (Real.log (⌊Q⌋₊ : ℝ)) - D
        ≤ ∑ p ∈ (⌊Q⌋₊).primesLE, (1 : ℝ) / (p : ℝ) := by
      have h := hAb (⌊Q⌋₊ : ℝ) (by exact_mod_cast hb2)
      rw [Nat.floor_natCast] at h
      have := (abs_le.mp h).1
      linarith
    have hC' := loglog_floor_le Q hQ2
    by_cases hcase : 2 ≤ ⌈P⌉₊ - 1
    · -- The lower `primesLE` index is at least `2`, so the Mertens upper bound applies.
      have hp_le : (∑ p ∈ (⌈P⌉₊ - 1).primesLE, (1 : ℝ) / (p : ℝ))
          ≤ Real.log (Real.log ((⌈P⌉₊ - 1 : ℕ) : ℝ)) + D := by
        have h := hAb (((⌈P⌉₊ - 1 : ℕ)) : ℝ) (by exact_mod_cast hcase)
        rw [Nat.floor_natCast] at h
        have := (abs_le.mp h).2
        linarith
      have hD' := loglog_ceil_pred_le P hP hcase
      rw [hsum, Real.log_div (ne_of_gt hlogQpos) (ne_of_gt hlogPpos)]
      have hCge : Real.log 2 + 2 * D ≤ Real.log 2 + 2 * D + |Real.log (Real.log 2)| := by
        linarith [abs_nonneg (Real.log (Real.log 2))]
      linarith [hb_ge, hp_le, hC', hD', hloglogP_ge, hCge]
    · -- Degenerate case `⌈P⌉₊ - 1 = 1`: the lower sum vanishes, and `log log P ≥ log log 2`.
      have hn1 : ⌈P⌉₊ - 1 = 1 := by omega
      have hzero : (∑ p ∈ (⌈P⌉₊ - 1).primesLE, (1 : ℝ) / (p : ℝ)) = 0 := by
        rw [hn1, Nat.primesLE_one, Finset.sum_empty]
      rw [hsum, hzero, sub_zero, Real.log_div (ne_of_gt hlogQpos) (ne_of_gt hlogPpos)]
      have hCge : Real.log 2 + D - Real.log (Real.log 2) ≤
          Real.log 2 + 2 * D + |Real.log (Real.log 2)| := by
        have := neg_le_abs (Real.log (Real.log 2))
        linarith
      linarith [hb_ge, hC', hloglogP_ge, hCge]

end Work.BMF.SD
