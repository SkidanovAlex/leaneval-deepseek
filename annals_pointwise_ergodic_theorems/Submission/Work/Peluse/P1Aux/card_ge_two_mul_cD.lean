import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.P1Aux

/-- The cardinality of the symmetric interval `symIcc N = [-N, N] ∩ ℤ` is `2N + 1`. -/
theorem card_symIcc (N : ℕ) : (((Work.Peluse.symIcc N).card : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]
  push_cast
  ring

/-- If `M₁ M₂ ≤ N / c` and `D ≤ M₁ M₂` (all in `ℝ`, with `c` a positive integer), then
`2 c D ≤ |symIcc N| = 2N + 1`: indeed `c D ≤ c M₁ M₂ ≤ N`. -/
theorem card_ge_two_mul_cD {c : ℤ} {M₁ M₂ N D : ℕ} (hc : 1 ≤ c)
    (hNM : (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ)) (hD : (D : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ)) :
    2 * (c : ℝ) * (D : ℝ) ≤ (((Work.Peluse.symIcc N).card : ℕ) : ℝ) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by
    have : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    linarith
  have hmul : (c : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) ≤ (N : ℝ) := by
    calc (c : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) ≤ (c : ℝ) * ((N : ℝ) / (c : ℝ)) :=
          mul_le_mul_of_nonneg_left hNM (le_of_lt hcR)
      _ = (N : ℝ) := by field_simp
  have hcD : (c : ℝ) * (D : ℝ) ≤ (N : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hD (le_of_lt hcR)) hmul
  rw [card_symIcc]
  nlinarith [hcD]

end Work.Peluse.P1Aux
