import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Reindexing identity: the sum over `ℕ ∩ [X, 2X]` of `f m * m^{-(1+it)}` equals the sum over
`Ioc (⌈X⌉₊ - 1) ⌊2X⌋₊` of `m^{-1} * (f m * m^{-it})`.  The two index sets agree because
`1 ≤ ⌈X⌉₊` for `X ≥ 16`, and the summands agree because
`m^{-(1+it)} = m^{-1} * m^{-it}` for `m ≠ 0`. -/
theorem window_reindex (f : ℕ → ℂ) (X t : ℝ) (hX : 16 ≤ X) :
    ∑ m ∈ Work.BMF.natIcc X (2 * X), f m * (m : ℂ) ^ (-(1 + Complex.I * t))
      = ∑ n ∈ Finset.Ioc (⌈X⌉₊ - 1) ⌊2 * X⌋₊,
          (((n : ℝ))⁻¹ : ℂ) * (f n * (n : ℂ) ^ (-(Complex.I * t))) := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hceil : 1 ≤ ⌈X⌉₊ := Nat.ceil_pos.mpr hXpos
  rw [Work.BMF.natIcc]
  refine Finset.sum_congr ?_ ?_
  · ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro n hn
    have hnne : n ≠ 0 := by
      simp only [Finset.mem_Ioc] at hn
      omega
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnne
    have hsplit : (n : ℂ) ^ (-(1 + Complex.I * t))
        = (n : ℂ) ^ (-1 : ℂ) * (n : ℂ) ^ (-(Complex.I * t)) := by
      rw [show -(1 + Complex.I * t) = (-1 : ℂ) + (-(Complex.I * t)) by ring]
      exact Complex.cpow_add _ _ hn0
    rw [hsplit, Complex.cpow_neg_one]
    push_cast
    ring

end Work.BMF.mr_direct
