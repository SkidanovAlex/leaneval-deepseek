import Mathlib
import Submission.Work.HP.dyadic.SumDefs

/-!
# The exponent identity `pow_bigE_eq`

For a difference vector `n : Fin r → ℕ` with `sval r n ≤ M` (where
`sval r n = ∑ i, n i * (r - i)`) one has the exact identity

`2 ^ (bigE' N r n) = 2 ^ ((N - 2) * M) * (1/2) ^ ((N - 2) * (M - sval r n)) * (1/2) ^ (Pval r n)`.

The point is that the total exponent decomposes.  Writing
`wval r i = r - i`, `dval r i = (i - 2) * (r - i)` and `alpha N i = N - max i 2`,
the weight of the coordinate `i` is

`Sval N r i = wval r i * alpha N i = (N - 2) * wval r i - dval r i`,

so that `bigE' N r n = (N - 2) * sval r n - Pval r n`.  Combining this with
`sval r n ≤ M` gives the additive decomposition

`(N - 2) * M = bigE' N r n + ((N - 2) * (M - sval r n) + Pval r n)`,

which is exactly the exponent identity, and the power computation follows from
`2 ^ a * (1/2) ^ a = 1`.
-/

set_option autoImplicit false

namespace Work.HP.dyadic

open Finset

noncomputable section

/-- The weight of a single coordinate splits as `(N - 2) * (r - i) - dval r i`. -/
lemma Sval_add_dval (N r : ℕ) (hrN : r ≤ N) (i : Fin r) :
    Sval N r i + dval r i = (N - 2) * wval r i := by
  have hdval : dval r i = ((i : ℕ) - 2) * wval r i := by simp [dval, wval]
  have hsum : (N - max (i : ℕ) 2) + ((i : ℕ) - 2) = N - 2 := by
    have hiN : (i : ℕ) ≤ N := le_trans (le_of_lt i.isLt) hrN
    rcases lt_or_ge (i : ℕ) 3 with h | h
    · have hmax : max (i : ℕ) 2 = 2 := max_eq_right (show (i : ℕ) ≤ 2 by omega)
      have hz : (i : ℕ) - 2 = 0 := Nat.sub_eq_zero_of_le (show (i : ℕ) ≤ 2 by omega)
      rw [hmax, hz, add_zero]
    · have hmax : max (i : ℕ) 2 = (i : ℕ) := max_eq_left (show 2 ≤ (i : ℕ) by omega)
      rw [hmax]; omega
  rw [Sval, alpha, hdval]
  calc wval r i * (N - max (i : ℕ) 2) + ((i : ℕ) - 2) * wval r i
      = wval r i * ((N - max (i : ℕ) 2) + ((i : ℕ) - 2)) := by ring
    _ = wval r i * (N - 2) := by rw [hsum]
    _ = (N - 2) * wval r i := by ring

/-- The total exponent splits as `bigE' + Pval = (N - 2) * sval`. -/
lemma bigE'_add_Pval (N r : ℕ) (hrN : r ≤ N) (n : Fin r → ℕ) :
    bigE' N r n + Pval r n = (N - 2) * sval r n := by
  rw [bigE', Pval, sval, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_add, Sval_add_dval N r hrN i]
  ring

/-- The exponent of the `2`-power which is `(N - 2) * M`. -/
lemma bigE'_add_split (N r M : ℕ) (hrN : r ≤ N) (n : Fin r → ℕ) (hn : sval r n ≤ M) :
    bigE' N r n + ((N - 2) * (M - sval r n) + Pval r n) = (N - 2) * M := by
  have hBP := bigE'_add_Pval N r hrN n
  have hM : sval r n + (M - sval r n) = M := by omega
  have h1 : (N - 2) * M = (N - 2) * sval r n + (N - 2) * (M - sval r n) := by
    rw [← Nat.mul_add, hM]
  rw [h1, ← hBP]
  ring

theorem pow_bigE_eq (N r M : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) (n : Fin r → ℕ) (hn : sval r n ≤ M) : (2 : ℝ) ^ (bigE' N r n) = (2 : ℝ) ^ ((N - 2) * M) * (1 / 2 : ℝ) ^ ((N - 2) * (M - sval r n)) * (1 / 2 : ℝ) ^ (Pval r n) := by
  have _hN : 3 ≤ N := le_trans hr hrN
  have hkey : (N - 2) * M = bigE' N r n + ((N - 2) * (M - sval r n) + Pval r n) :=
    (bigE'_add_split N r M hrN n hn).symm
  have h2 : (2 : ℝ) ^ ((N - 2) * M) =
      (2 : ℝ) ^ (bigE' N r n) * (2 : ℝ) ^ ((N - 2) * (M - sval r n) + Pval r n) := by
    rw [hkey, pow_add]
  symm
  calc (2 : ℝ) ^ ((N - 2) * M) * (1 / 2 : ℝ) ^ ((N - 2) * (M - sval r n)) * (1 / 2 : ℝ) ^ (Pval r n)
      = (2 : ℝ) ^ ((N - 2) * M) *
          ((1 / 2 : ℝ) ^ ((N - 2) * (M - sval r n)) * (1 / 2 : ℝ) ^ (Pval r n)) := by ring
    _ = (2 : ℝ) ^ ((N - 2) * M) * (1 / 2 : ℝ) ^ ((N - 2) * (M - sval r n) + Pval r n) := by
          rw [← pow_add]
    _ = ((2 : ℝ) ^ (bigE' N r n) *
            (2 : ℝ) ^ ((N - 2) * (M - sval r n) + Pval r n)) *
          (1 / 2 : ℝ) ^ ((N - 2) * (M - sval r n) + Pval r n) := by rw [h2]
    _ = (2 : ℝ) ^ (bigE' N r n) *
          ((2 : ℝ) ^ ((N - 2) * (M - sval r n) + Pval r n) *
            (1 / 2 : ℝ) ^ ((N - 2) * (M - sval r n) + Pval r n)) := by ring
    _ = (2 : ℝ) ^ (bigE' N r n) * ((2 * (1 / 2 : ℝ)) ^ ((N - 2) * (M - sval r n) + Pval r n)) := by
          rw [← mul_pow]
    _ = (2 : ℝ) ^ (bigE' N r n) * 1 ^ ((N - 2) * (M - sval r n) + Pval r n) := by norm_num
    _ = (2 : ℝ) ^ (bigE' N r n) := by simp

end

end Work.HP.dyadic
