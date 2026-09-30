import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

open Finset Real

/-- Two-sided Mertens: for `11 ≤ y ≤ x` the total reciprocal-prime mass of the primes in
`(y, x]` is at most `log (log x / log y) + O(1)` with an absolute constant.  This follows from the
workspace lemma `Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound` (module
`Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`), which gives
`∃ C0 > 0, ∀ z ≥ 11, |∑_{p ∈ (⌊z⌋₊).primesLE} 1/p − log log z| ≤ C0`. -/
theorem primeRecips_loglog_split :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 11 ≤ y → y ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / p) ≤
        Real.log (Real.log x / Real.log y) + C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro x y hy hxy
  have hx11 : (11 : ℝ) ≤ x := le_trans hy hxy
  -- `(y, x]` cut-off: the smaller prime set is contained in the larger one
  have hsub : (⌊y⌋₊).primesLE ⊆ (⌊x⌋₊).primesLE :=
    Nat.primesLE_mono (Nat.floor_mono hxy)
  have hsplit := Finset.sum_sdiff hsub (f := fun p : ℕ => (1 : ℝ) / p)
  -- two-sided Mertens at `x` and at `y`
  have hxup : (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p) - Real.log (Real.log x) ≤ C₀ :=
    (abs_le.mp (hC₀ x hx11)).2
  have hylo : -C₀ ≤ (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / p) - Real.log (Real.log y) :=
    (abs_le.mp (hC₀ y hy)).1
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  rw [Real.log_div (ne_of_gt hlogx) (ne_of_gt hlogy)]
  linarith

end Work.BMF.HL
