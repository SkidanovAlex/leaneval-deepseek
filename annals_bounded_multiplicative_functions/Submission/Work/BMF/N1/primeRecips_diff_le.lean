import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Work.BMF.N1.loglog_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N1

/-- Difference of reciprocal prime sums between two scales.

Use the existing lemma `Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`
(module `Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`), which gives
`∃ C > 0, ∀ x ≥ 11, |∑_{p ∈ (⌊x⌋₊).primesLE} 1/p − Real.log (Real.log x)| ≤ C`:
import that module (it is in this workspace at Submission/Commons/...).  The companion
log-log estimate `Real.log (Real.log Z) ≤ Real.log (Real.log Y) + Real.log ((m:ℝ) + |Real.log C|)`
for `11 ≤ Y ≤ Z ≤ C * Y^m`, `1 ≤ m` should be proved inline here. -/
theorem primeRecips_diff_le (k : ℕ) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y Z : ℝ, 11 ≤ Y → Y ≤ Z → Z ≤ C₀ * Y ^ (2 * (k + 1)) →
      (∑ p ∈ (⌊Z⌋₊).primesLE, (1 : ℝ) / p) - (∑ p ∈ (⌊Y⌋₊).primesLE, (1 : ℝ) / p) ≤
        Real.log ((2 * (k + 1) : ℝ) + |Real.log C₀|) + K := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  refine ⟨2 * C, by linarith, ?_⟩
  intro Y Z hY hYZ hZY
  have hZ : 11 ≤ Z := le_trans hY hYZ
  -- Upper bound on `S Z - log log Z`.
  have h1 : (∑ p ∈ (⌊Z⌋₊).primesLE, (1 : ℝ) / p) - Real.log (Real.log Z) ≤ C :=
    (abs_le.mp (hC Z hZ)).2
  -- Upper bound on `log log Y - S Y`.
  have h2 : Real.log (Real.log Y) - (∑ p ∈ (⌊Y⌋₊).primesLE, (1 : ℝ) / p) ≤ C := by
    have h := (abs_le.mp (hC Y hY)).1
    linarith
  -- Comparison of the two iterated logarithms.
  have h3 : Real.log (Real.log Z) ≤
      Real.log (Real.log Y) + Real.log ((2 * (k + 1) : ℝ) + |Real.log C₀|) := by
    have := loglog_le C₀ hC₀ (2 * (k + 1)) (by omega) hY hZ hZY
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using this
  linarith

end Work.BMF.N1
