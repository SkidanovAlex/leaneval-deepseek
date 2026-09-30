import Mathlib
import Submission.Work.BMF.HL.primeRecips_loglog_split
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

open Finset Real

/-- Two-sided Mertens split valid down to `y = 2`: for `2 ≤ y ≤ x`,
`Σ_{y<p≤x} 1/p ≤ log(log x/log y) + O(1)` with an absolute constant.  Route: the Finset
`(⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE` is exactly the primes in `(y, x]`; for `y ≥ 11` use the
already-proved `Work.BMF.HL.primeRecips_loglog_split` (module
`Submission.Work.BMF.HL.primeRecips_loglog_split`); for `2 ≤ y < 11` the left side is at most
`Σ_{p ≤ x} 1/p − 1/2`, which is `≤ log log x + O(1)` by Mertens (module
`Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`), while
`log(log x/log y) ≥ 0` and `log log y ≤ log log 11 < 1`. -/
theorem primeRecips_loglog_split_all :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / p) ≤
        Real.log (Real.log x / Real.log y) + C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  obtain ⟨C₁, hC₁pos, hC₁⟩ := primeRecips_loglog_split
  refine ⟨max C₁ (Real.log (Real.log 11) + C₀), ?_, ?_⟩
  · exact lt_of_lt_of_le hC₁pos (le_max_left _ _)
  · intro x y hy hxy
    have hylog : 0 < Real.log y := Real.log_pos (by linarith)
    have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
    rcases le_or_gt 11 y with hy11 | hy11
    · exact le_trans (hC₁ x y hy11 hxy)
        (by linarith [le_max_left C₁ (Real.log (Real.log 11) + C₀)])
    · -- 2 ≤ y < 11
      set z : ℝ := max x 11 with hz
      have hz11 : 11 ≤ z := le_max_right x 11
      have hxz : x ≤ z := le_max_left x 11
      have hsubBA : (⌊y⌋₊).primesLE ⊆ (⌊x⌋₊).primesLE :=
        Nat.primesLE_mono (Nat.floor_mono hxy)
      have hsubAz : (⌊x⌋₊).primesLE ⊆ (⌊z⌋₊).primesLE :=
        Nat.primesLE_mono (Nat.floor_mono hxz)
      have h2B : (2 : ℕ) ∈ (⌊y⌋₊).primesLE :=
        Nat.mem_primesLE.mpr ⟨Nat.le_floor hy, Nat.prime_two⟩
      have hsumB : (1 : ℝ) / 2 ≤ ∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / p := by
        have := Finset.single_le_sum (s := (⌊y⌋₊).primesLE)
          (f := fun p : ℕ => (1 : ℝ) / p) (fun p _ => by positivity) h2B
        simpa using this
      have hSadd : (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / p)
            + (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / p)
          = ∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p :=
        Finset.sum_sdiff hsubBA (f := fun p : ℕ => (1 : ℝ) / p)
      have hS : (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / p)
          = (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p)
            - (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / p) := by linarith
      have hsumAz : (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p)
          ≤ ∑ p ∈ (⌊z⌋₊).primesLE, (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubAz (fun p _ _ => by positivity)
      have hmert : (∑ p ∈ (⌊z⌋₊).primesLE, (1 : ℝ) / p) ≤ Real.log (Real.log z) + C₀ :=
        by have := (abs_le.mp (hC₀ z hz11)).2; linarith
      have hlogz : Real.log (Real.log z)
          ≤ Real.log (Real.log x / Real.log y) + Real.log (Real.log 11) := by
        rcases le_or_gt 11 x with hx11 | hx11
        · have hzeq : z = x := by rw [hz, max_eq_left hx11]
          rw [hzeq, Real.log_div (ne_of_gt hxlog) (ne_of_gt hylog)]
          have h1 : Real.log (Real.log y) ≤ Real.log (Real.log 11) :=
            Real.log_le_log hylog
              (Real.log_le_log (by linarith : (0 : ℝ) < y) (le_of_lt hy11))
          linarith
        · have hzeq : z = 11 := by rw [hz, max_eq_right (le_of_lt hx11)]
          rw [hzeq]
          have h1 : 0 ≤ Real.log (Real.log x / Real.log y) := by
            apply Real.log_nonneg
            rw [le_div_iff₀ hylog]
            have hlogxy : Real.log y ≤ Real.log x :=
              Real.log_le_log (by linarith : (0 : ℝ) < y) hxy
            linarith
          linarith
      rw [hS]
      linarith [hsumB, hsumAz, hmert, hlogz,
        le_max_right C₁ (Real.log (Real.log 11) + C₀)]

end Work.BMF.HL
