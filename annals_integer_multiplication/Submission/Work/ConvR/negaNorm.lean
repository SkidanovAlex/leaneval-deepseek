import Mathlib
import Submission.Work.ConvR.basic

/-!
# The sup-norm bound for the negacyclic product `negaMul` (paper Lemma 2.5, `‖·‖` part)

For `a b : Fin r → ℂ`, the product `negaMul r a b` in the synthetic ring
`ℝ = ℂ[y]/(y^r+1)` is the negacyclic convolution

  `(negaMul r a b) k = ∑_{i+j=k} a i * b j - ∑_{i+j=k+r} a i * b j`,

where each of the two index conditions determines `j` uniquely from `i`.  Hence every
coefficient of the product is a sum of exactly `r` products `a i * b j`, one for each `i`,
and `‖negaMul r a b‖ ≤ r * ‖a‖ * ‖b‖`.

The key point (used by the cost analysis of Prop. 3.4) is that the factor is `r`, not `r ^ 2`:
for each `i` at most one `j` contributes.  This is made explicit by `negaMul_explicit`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- Explicit form of the negacyclic product: for a fixed output index `k` and each `i : Fin r`
exactly one `j : Fin r` contributes, namely `j = k - i` when `i ≤ k` (coefficient `a i * b j`,
from `i + j = k`) and `j = k + r - i` when `i > k` (coefficient `-(a i * b j)`, from
`i + j = k + r`). -/
theorem negaMul_explicit (r : ℕ) (a b : Fin r → ℂ) (k : Fin r) :
    HvdH.negaMul r a b k =
      ∑ i : Fin r, (if h : (i : ℕ) ≤ (k : ℕ) then
        a i * b ⟨(k : ℕ) - (i : ℕ), by omega⟩
      else -(a i * b ⟨(k : ℕ) + r - (i : ℕ), by omega⟩)) := by
  simp only [HvdH.negaMul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) ≤ (k : ℕ)
  · rw [dite_eq_left hi]
    rw [Finset.sum_eq_single (⟨(k : ℕ) - (i : ℕ), by omega⟩ : Fin r)]
    · rw [ite_eq_left (by omega : (i : ℕ) + ((k : ℕ) - (i : ℕ)) = (k : ℕ))]
    · intro j _ hj
      by_cases h1 : (i : ℕ) + (j : ℕ) = (k : ℕ)
      · exact absurd (Fin.ext (by omega : (j : ℕ) = (k : ℕ) - (i : ℕ))) hj
      · rw [ite_eq_right h1]
        by_cases h2 : (i : ℕ) + (j : ℕ) = (k : ℕ) + r
        · omega
        · rw [ite_eq_right h2]
    · intro ha
      exact absurd (Finset.mem_univ _) ha
  · rw [dite_eq_right hi]
    rw [Finset.sum_eq_single (⟨(k : ℕ) + r - (i : ℕ), by omega⟩ : Fin r)]
    · rw [ite_eq_right (by omega : ¬ ((i : ℕ) + ((k : ℕ) + r - (i : ℕ)) = (k : ℕ)))]
      rw [ite_eq_left (by omega : (i : ℕ) + ((k : ℕ) + r - (i : ℕ)) = (k : ℕ) + r)]
    · intro j _ hj
      by_cases h1 : (i : ℕ) + (j : ℕ) = (k : ℕ)
      · omega
      · rw [ite_eq_right h1]
        by_cases h2 : (i : ℕ) + (j : ℕ) = (k : ℕ) + r
        · exact absurd (Fin.ext (by omega : (j : ℕ) = (k : ℕ) + r - (i : ℕ))) hj
        · rw [ite_eq_right h2]
    · intro ha
      exact absurd (Finset.mem_univ _) ha

theorem negaNorm (r : ℕ) (a b : Fin r → ℂ) :
    ‖HvdH.negaMul r a b‖ ≤ (r : ℝ) * ‖a‖ * ‖b‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [negaMul_explicit r a b k]
  have h2 : (∑ i : Fin r, ‖a i‖ * ‖b‖) ≤ (r : ℝ) * (‖a‖ * ‖b‖) := by
    have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin r))
      (fun i => ‖a i‖ * ‖b‖) (‖a‖ * ‖b‖)
      (fun i _ => mul_le_mul_of_nonneg_right (norm_le_pi_norm a i) (norm_nonneg b))
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun i : Fin r => ‖a i‖ * ‖b‖) (fun i _ => ?_)) ?_
  · split
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm b _) (norm_nonneg _)
    · rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm b _) (norm_nonneg _)
  · calc (∑ i : Fin r, ‖a i‖ * ‖b‖) ≤ (r : ℝ) * (‖a‖ * ‖b‖) := h2
      _ = (r : ℝ) * ‖a‖ * ‖b‖ := by ring

end Work.ConvR
