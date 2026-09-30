import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Complex

/-- Rewrite the window sum with weight `n ^ (-(1 + I t))` as a sum over the same
integers with the weight split as `n⁻¹ · n ^ (-(I t))`.  The lower index is written
`Ioc (⌈Y⌉₊ - 1) ...` so that, for `Y ≥ 2`, it matches `natIcc Y (3Y) = Icc ⌈Y⌉₊ ⌊3Y⌋₊`. -/
theorem window_sum_cpow_eq (g : ℕ → ℂ) (Y t : ℝ) (hY : 2 ≤ Y) :
    (∑ n ∈ Work.BMF.natIcc Y (3 * Y), g n * (n : ℂ) ^ (-(1 + Complex.I * t)))
      = ∑ n ∈ Finset.Ioc (⌈Y⌉₊ - 1) ⌊3 * Y⌋₊,
          (((n : ℝ))⁻¹ : ℂ) * (g n * (n : ℂ) ^ (-(Complex.I * t))) := by
  have hceil : 2 ≤ ⌈Y⌉₊ := by
    have h := Nat.le_ceil Y
    have h2 : (2 : ℝ) ≤ (⌈Y⌉₊ : ℝ) := le_trans hY h
    exact_mod_cast h2
  have hset : Finset.Ioc (⌈Y⌉₊ - 1) ⌊3 * Y⌋₊ = Finset.Icc ⌈Y⌉₊ ⌊3 * Y⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simp only [Work.BMF.natIcc]
  rw [hset]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn0 : n ≠ 0 := by omega
  have hcn : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hpow : (n : ℂ) ^ (-(1 + Complex.I * t))
      = (n : ℂ)⁻¹ * (n : ℂ) ^ (-(Complex.I * t)) := by
    have h1 : -(1 + Complex.I * t) = (-1 : ℂ) + (-(Complex.I * t)) := by ring
    rw [h1, Complex.cpow_add _ _ hcn, Complex.cpow_neg_one]
  have hinv : (((n : ℝ))⁻¹ : ℂ) = (n : ℂ)⁻¹ := by simp
  rw [hpow, hinv]
  ring

end Work.BMF.mr_direct
