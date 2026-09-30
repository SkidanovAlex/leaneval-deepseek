import Mathlib
import Submission.Work.BMF.HL.primeRecips_loglog_split

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

open Finset Real

/-- The reciprocal-prime weighted by `1/log p` over the block `(x, x²]` is `O(1/log x)`, with
the explicit constant `log 2 + C`.  The point is the elementary comparison
`1/(p log p) ≤ (1/log x)·(1/p)` valid for `p > x ≥ 11`, which turns the target into the
reciprocal-prime mass of the block; the latter is at most `log 2 + C` by the two-sided
Mertens bound `primeRecips_loglog_split` applied with `y = x`, `x = x²`
(and `log(log x² / log x) = log 2`). -/
theorem prime_block_inv_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 11 ≤ x →
      (∑ p ∈ (⌊x ^ 2⌋₊).primesLE \ (⌊x⌋₊).primesLE, 1 / ((p : ℝ) * Real.log p))
        ≤ (Real.log 2 + C) / Real.log x := by
  obtain ⟨C₀, _hC₀pos, hC₀⟩ := primeRecips_loglog_split
  refine ⟨max C₀ 1, lt_of_lt_of_le one_pos (le_max_right C₀ 1), ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) < x := by linarith
  have hxpos : 0 < x := by linarith
  have hlogxpos : 0 < Real.log x := Real.log_pos hx1
  have hxx2 : x ≤ x ^ 2 := by nlinarith [hx]
  -- Pointwise comparison `1/(p log p) ≤ (1/log x)·(1/p)` for `p` in the block.
  have hterm : ∀ p ∈ (⌊x^2⌋₊).primesLE \ (⌊x⌋₊).primesLE,
      1 / ((p:ℝ) * Real.log p) ≤ (1 / Real.log x) * (1 / (p:ℝ)) := by
    intro p hp
    obtain ⟨hpA, hpB⟩ := Finset.mem_sdiff.mp hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpA
    -- `p` is a prime greater than `⌊x⌋`, hence `p > x`, hence `log p ≥ log x`.
    have hpgt : ⌊x⌋₊ < p := by
      by_contra h
      exact hpB (Nat.mem_primesLE.mpr ⟨not_lt.mp h, hpprime⟩)
    have hplt : x < (p:ℝ) := by
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (p:ℝ) := by exact_mod_cast hpgt
      have h1 := Nat.lt_floor_add_one x
      linarith
    have hlogp : Real.log x ≤ Real.log p := Real.log_le_log hxpos hplt.le
    have hp0 : (0:ℝ) < (p:ℝ) := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.two_le
      linarith
    have hstep1 : 1 / Real.log p ≤ 1 / Real.log x :=
      one_div_le_one_div_of_le hlogxpos hlogp
    have hpnonneg : (0:ℝ) ≤ 1 / (p:ℝ) := by positivity
    have h2 := mul_le_mul_of_nonneg_right hstep1 hpnonneg
    calc 1 / ((p:ℝ) * Real.log p)
        = (1 / Real.log p) * (1 / (p:ℝ)) := by field_simp
      _ ≤ (1 / Real.log x) * (1 / (p:ℝ)) := h2
  -- Summing and factoring out `1/log x`.
  have hsum_le : (∑ p ∈ (⌊x^2⌋₊).primesLE \ (⌊x⌋₊).primesLE, 1 / ((p:ℝ) * Real.log p))
      ≤ (1 / Real.log x) *
        (∑ p ∈ (⌊x^2⌋₊).primesLE \ (⌊x⌋₊).primesLE, 1 / (p:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  -- Two-sided Mertens on `(x, x²]`: the reciprocal-prime mass is `≤ log 2 + C₀`.
  have hsplit := hC₀ (x^2) x hx hxx2
  have hlogxsq : Real.log (x^2) = 2 * Real.log x := Real.log_pow x 2
  have hlog2 : Real.log (Real.log (x^2) / Real.log x) = Real.log 2 := by
    have hq : Real.log (x^2) / Real.log x = 2 := by
      rw [hlogxsq, mul_div_cancel_right₀ 2 (ne_of_gt hlogxpos)]
    rw [hq]
  rw [hlog2] at hsplit
  calc (∑ p ∈ (⌊x^2⌋₊).primesLE \ (⌊x⌋₊).primesLE, 1 / ((p:ℝ) * Real.log p))
      ≤ (1 / Real.log x) *
        (∑ p ∈ (⌊x^2⌋₊).primesLE \ (⌊x⌋₊).primesLE, 1 / (p:ℝ)) := hsum_le
    _ ≤ (1 / Real.log x) * (Real.log 2 + C₀) :=
        mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = (Real.log 2 + C₀) / Real.log x := by ring
    _ ≤ (Real.log 2 + max C₀ 1) / Real.log x :=
        div_le_div_of_nonneg_right (by linarith [le_max_left C₀ 1]) hlogxpos.le

end Work.BMF.HL
