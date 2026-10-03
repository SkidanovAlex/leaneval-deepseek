import Mathlib
import Submission.Work.Peluse.Pel51.winFacts

/-!
# The direction bound for the padded family

If `|b₀| ≤ B·M₁` and `c·M₁·M₂ ≤ N`, then every element of the arithmetic progression
`arithIcc (c·(a + b₀)) M₂` has absolute value at most `(B+1)·N`, for every `a ∈ [1,M₁]`.
This is the `[-N',N']`-bound needed by `levelRaiseAppendBd` in the transfer
`lemma51P 2 → lemma51P 1` (`Pel51/lemma51P_one_of_two.lean`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Pel51

open Work.Peluse

theorem dirBound {c : ℤ} (hc : 0 < c) {M₁ M₂ N : ℕ} {B : ℕ} {b₀ : ℤ}
    (hd : c * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) (hb : |b₀| ≤ (B : ℤ) * (M₁ : ℤ)) :
    ∀ a ∈ Finset.Icc 1 M₁,
      |c * ((a : ℤ) + b₀)| * (M₂ : ℤ) ≤ (((B + 1 : ℕ)) : ℤ) * (N : ℤ) := by
  intro a ha
  have hM₂0 : (0 : ℤ) ≤ (M₂ : ℤ) := by positivity
  have han : |(a : ℤ)| ≤ (M₁ : ℤ) := by
    have h1 : (a : ℤ) ≤ (M₁ : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp ha).2
    have h0 : (0 : ℤ) ≤ (a : ℤ) := by exact_mod_cast (by omega : 0 ≤ a)
    rw [abs_of_nonneg h0]; exact h1
  have h1 : |c * ((a : ℤ) + b₀)| = c * |(a : ℤ) + b₀| := by rw [abs_mul, abs_of_pos hc]
  have h2 : |(a : ℤ) + b₀| ≤ (((B + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := by
    have h3 : |(a : ℤ) + b₀| ≤ (M₁ : ℤ) + (B : ℤ) * (M₁ : ℤ) :=
      le_trans (abs_add_le _ _) (add_le_add han hb)
    have h4 : (M₁ : ℤ) + (B : ℤ) * (M₁ : ℤ) = (((B + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := by
      push_cast; ring
    rw [h4] at h3; exact h3
  rw [h1]
  have h5 : c * |(a : ℤ) + b₀| * (M₂ : ℤ)
      ≤ c * ((((B + 1 : ℕ)) : ℤ) * (M₁ : ℤ)) * (M₂ : ℤ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (le_of_lt hc)) hM₂0
  have h6 : c * ((((B + 1 : ℕ)) : ℤ) * (M₁ : ℤ)) * (M₂ : ℤ)
      = (((B + 1 : ℕ)) : ℤ) * (c * (M₁ : ℤ) * (M₂ : ℤ)) := by ring
  have h7 : (((B + 1 : ℕ)) : ℤ) * (c * (M₁ : ℤ) * (M₂ : ℤ)) ≤ (((B + 1 : ℕ)) : ℤ) * (N : ℤ) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  rw [h6] at h5
  exact le_trans h5 h7

end Work.Peluse.Pel51
