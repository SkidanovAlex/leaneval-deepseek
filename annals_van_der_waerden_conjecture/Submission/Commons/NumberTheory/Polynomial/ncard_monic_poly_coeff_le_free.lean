import Mathlib
import Submission.Commons.NumberTheory.Polynomial.ncard_monic_poly_coeff_le

/-!
# Counting monic integer polynomials with a vanishing `x ^ (n-1)` coefficient

This file bounds the number of monic integer polynomials `P` of degree `n` whose
coefficient of `x ^ (n-1)` is `0` and whose remaining coefficients (indexed by
`i ≤ n`, `i ≠ n - 1`) are bounded by `B i`.  The count is at most the product
`∏_{i ∈ range (n+1) \ {n-1}} (2 * B i + 1)`, i.e. the coefficient of `x ^ (n-1)`
contributes a single option rather than the `2 * B (n-1) + 1` options that a
genuinely bounded coefficient would contribute.

The argument reuses `Commons.NumberTheory.Polynomial.ncard_monic_poly_coeff_le`
(the fully bounded case) by introducing the modified bound
`B' i = if i = n - 1 then 0 else B i`.  Since `|c| ≤ 0` forces `c = 0`, the two
sets of polynomials coincide, and the factor at `i = n - 1` in the product is
`2 * 0 + 1 = 1`, which can be erased.
-/

open Finset

namespace Commons.NumberTheory.Polynomial

theorem ncard_monic_poly_coeff_le_free {n : ℕ} (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i) :
    ((Set.ncard {P : Polynomial ℤ | P.Monic ∧ P.natDegree = n ∧ P.coeff (n - 1) = 0 ∧
      ∀ i, i ≤ n → i ≠ n - 1 → |((P.coeff i : ℤ) : ℝ)| ≤ B i} : ℕ) : ℝ) ≤
      ∏ i ∈ (Finset.range (n + 1)).erase (n - 1), (2 * B i + 1) := by
  classical
  -- Modify the bound so that the `(n-1)`-th coefficient is forced to vanish.
  set B' : ℕ → ℝ := fun i => if i = n - 1 then 0 else B i with hB'def
  have hB'm1 : B' (n - 1) = 0 := by rw [hB'def]; simp
  have hB'nonneg : ∀ i, 0 ≤ B' i := by
    intro i
    rw [hB'def]
    by_cases h : i = n - 1
    · simp [h]
    · simp [h, hB i]
  -- The target set coincides with the fully bounded set for `B'`.
  have hset : {P : Polynomial ℤ | P.Monic ∧ P.natDegree = n ∧ P.coeff (n - 1) = 0 ∧
      ∀ i, i ≤ n → i ≠ n - 1 → |((P.coeff i : ℤ) : ℝ)| ≤ B i} =
      {P : Polynomial ℤ | P.Monic ∧ P.natDegree = n ∧
        ∀ i ≤ n, |((P.coeff i : ℤ) : ℝ)| ≤ B' i} := by
    ext P
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hm, hd, hc, hb⟩
      refine ⟨hm, hd, ?_⟩
      intro i hi
      rw [hB'def]
      by_cases h : i = n - 1
      · subst h; simp [hc]
      · simp [h, hb i hi h]
    · rintro ⟨hm, hd, hb⟩
      refine ⟨hm, hd, ?_, ?_⟩
      · have h := hb (n - 1) (by omega)
        rw [hB'm1, abs_nonpos_iff] at h
        exact Int.cast_eq_zero.mp h
      · intro i hi hne
        have h := hb i hi
        rw [hB'def] at h
        simpa [hne] using h
  rw [hset]
  -- Apply the fully bounded counting lemma to `B'`.
  have hmain := ncard_monic_poly_coeff_le (n := n) B' hB'nonneg
  refine hmain.trans (le_of_eq ?_)
  -- The product over `range (n+1)` for `B'` equals the product over the erased range.
  have hmem : n - 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.prod_erase_mul (Finset.range (n + 1)) (fun i => 2 * B' i + 1) hmem]
  have h1 : 2 * B' (n - 1) + 1 = 1 := by rw [hB'm1]; ring
  rw [h1, mul_one]
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i ≠ n - 1 := Finset.ne_of_mem_erase hi
  rw [hB'def]
  simp [hne]

end Commons.NumberTheory.Polynomial
