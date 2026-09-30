import Mathlib
import Submission.Work.BMF.HL.sum_log_div_prime_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Real

/-- The cross sum `Σ_{p ≤ y} (1 − p^{−α})/p` is bounded uniformly on the region
`α log y ≤ 1`, `0 < α`, `y ≥ 2`.

Proof: for a prime `p` the mean-value inequality `1 − e^{−t} ≤ t` (`t = α log p ≥ 0`) gives the
pointwise bound `1 − p^{−α} ≤ α log p`, hence
`Σ (1 − p^{−α})/p ≤ α · Σ_{p ≤ y} (log p)/p`.
The latter is `≤ C log y` by `Work.BMF.HL.sum_log_div_prime_le` (Abel summation against the
Chebyshev/Mertens estimate `θ(y) ≪ y`), and `α · C log y ≤ C` because `α log y ≤ 1`. -/
theorem cross_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ α y : ℝ, 0 < α → 2 ≤ y → α * Real.log y ≤ 1 →
      (∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p) ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := Work.BMF.HL.sum_log_div_prime_le
  refine ⟨C, hCpos, ?_⟩
  intro α y hα hy hαy
  -- pointwise: `1 − p^{−α} ≤ α log p` for every prime `p`
  have hterm : ∀ p ∈ (⌊y⌋₊).primesLE,
      (1 - (p : ℝ) ^ (-α)) / (p : ℝ) ≤ α * Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hrpow : (p : ℝ) ^ (-α) = Real.exp (-(α * Real.log (p : ℝ))) := by
      rw [Real.rpow_def_of_pos hp0]
      congr 1
      ring
    have hkey : 1 - (p : ℝ) ^ (-α) ≤ α * Real.log (p : ℝ) := by
      rw [hrpow]
      have := Real.one_sub_le_exp_neg (α * Real.log (p : ℝ))
      linarith
    exact div_le_div_of_nonneg_right hkey hp0.le
  calc (∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p)
      ≤ ∑ p ∈ (⌊y⌋₊).primesLE, α * Real.log (p : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum hterm
    _ = α * ∑ p ∈ (⌊y⌋₊).primesLE, Real.log (p : ℝ) / (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
    _ ≤ α * (C * Real.log y) := mul_le_mul_of_nonneg_left (hC y hy) hα.le
    _ = C * (α * Real.log y) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hαy hCpos.le
    _ = C := by ring

end Work.BMF
