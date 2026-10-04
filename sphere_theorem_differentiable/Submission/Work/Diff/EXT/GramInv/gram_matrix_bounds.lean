import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bounds for a symmetric matrix from two-sided quadratic-form bounds

Let `A : Matrix (Fin n) (Fin n) ℝ` be symmetric and suppose there are `0 < c ≤ C` with

  `c * ∑ i, (v i)^2 ≤ ∑ i, ∑ j, v i * v j * A i j ≤ C * ∑ i, (v i)^2`  for all `v`.

Then `A` is invertible, its diagonal is `≥ c`, its entries are bounded by `C` in absolute value,
and so are the entries of its inverse (bounded by `1 / c`).

The formalisation keeps everything elementary: the quadratic form
`∑ i, ∑ j, v i * v j * A i j` is identified with the matrix dot product `v ⬝ᵥ (A *ᵥ v)`, and all
estimates are obtained from the two vectors `eᵢ` and `eᵢ ± eⱼ` (for the entries of `A`) and from
the columns of `A⁻¹` (for the entries of `A⁻¹`, whose square-norm is bounded using
`c * ‖col‖² ≤ (col) ⱼ ≤ ‖col‖`).
-/

namespace Work.Diff.EXT.GramInv

open Matrix Finset

variable {n : ℕ}

/-- The quadratic form of a matrix, written as a dot product with the matrix-vector product. -/
lemma qform_eq_dotProduct (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * A i j) = v ⬝ᵥ (A *ᵥ v) := by
  simp only [dotProduct, mulVec, mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The sum of squares is the self dot product. -/
lemma sum_sq_eq_dotProduct (v : Fin n → ℝ) :
    (∑ i, (v i)^2) = v ⬝ᵥ v := by
  simp [dotProduct, sq]

/-- Evaluating the quadratic form of `A` on the standard basis vectors. -/
lemma single_dot_mulVec_single (A : Matrix (Fin n) (Fin n) ℝ) (s t : Fin n) :
    (Pi.single s (1:ℝ) : Fin n → ℝ) ⬝ᵥ (A *ᵥ (Pi.single t (1:ℝ) : Fin n → ℝ)) = A s t := by
  rw [Matrix.dotProduct_mulVec, Matrix.single_one_vecMul, dotProduct_single_one]
  rfl

/-- The dot product of two distinct standard basis vectors is zero. -/
lemma dotProduct_single_single {s t : Fin n} (h : s ≠ t) :
    (Pi.single s (1:ℝ) : Fin n → ℝ) ⬝ᵥ (Pi.single t (1:ℝ) : Fin n → ℝ) = 0 := by
  rw [dotProduct_single_one]
  exact Pi.single_eq_of_ne h.symm 1

/-- The norm of a standard basis vector is one. -/
lemma single_self_dot (s : Fin n) :
    (Pi.single s (1:ℝ) : Fin n → ℝ) ⬝ᵥ (Pi.single s (1:ℝ) : Fin n → ℝ) = 1 := by
  rw [dotProduct_single_one, Pi.single_eq_same]

/-- The quadratic form on `eᵢ + eⱼ`. -/
lemma qf_add (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Pi.single i (1:ℝ) + Pi.single j (1:ℝ) : Fin n → ℝ) ⬝ᵥ
      (A *ᵥ (Pi.single i (1:ℝ) + Pi.single j (1:ℝ) : Fin n → ℝ))
      = A i i + A i j + A j i + A j j := by
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
      single_dot_mulVec_single A i i, single_dot_mulVec_single A j i,
      single_dot_mulVec_single A i j, single_dot_mulVec_single A j j]
  ring

/-- The quadratic form on `eᵢ - eⱼ`. -/
lemma qf_sub (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Pi.single i (1:ℝ) - Pi.single j (1:ℝ) : Fin n → ℝ) ⬝ᵥ
      (A *ᵥ (Pi.single i (1:ℝ) - Pi.single j (1:ℝ) : Fin n → ℝ))
      = A i i - A i j - A j i + A j j := by
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      single_dot_mulVec_single A i i, single_dot_mulVec_single A j i,
      single_dot_mulVec_single A i j, single_dot_mulVec_single A j j]
  ring

/-- Norm squared of `eᵢ + eⱼ` for `i ≠ j`. -/
lemma sq_add (i j : Fin n) (h : i ≠ j) :
    (∑ k, ((Pi.single i (1:ℝ) + Pi.single j (1:ℝ) : Fin n → ℝ) k)^2) = 2 := by
  rw [sum_sq_eq_dotProduct, add_dotProduct, dotProduct_add, dotProduct_add,
      single_self_dot i, dotProduct_single_single h, dotProduct_single_single h.symm,
      single_self_dot j]
  norm_num

/-- Norm squared of `eᵢ - eⱼ` for `i ≠ j`. -/
lemma sq_sub (i j : Fin n) (h : i ≠ j) :
    (∑ k, ((Pi.single i (1:ℝ) - Pi.single j (1:ℝ) : Fin n → ℝ) k)^2) = 2 := by
  rw [sum_sq_eq_dotProduct, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      single_self_dot i, dotProduct_single_single h, dotProduct_single_single h.symm,
      single_self_dot j]
  norm_num

lemma gram_matrix_bounds
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlow : ∀ v : Fin n → ℝ, c * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * A i j)
    (hup : ∀ v : Fin n → ℝ, ∑ i, ∑ j, v i * v j * A i j ≤ C * ∑ i, (v i) ^ 2) :
    A.det ≠ 0 ∧ (∀ i : Fin n, c ≤ A i i) ∧ (∀ i j : Fin n, |A i j| ≤ C) ∧
      (∀ i j : Fin n, |A⁻¹ i j| ≤ 1 / c) := by
  classical
  -- ## Invertibility: a nonzero kernel vector would make the quadratic form vanish.
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h := hlow v
    rw [qform_eq_dotProduct, hv] at h
    simp only [dotProduct_zero] at h
    have hvne : ∃ i, v i ≠ 0 := by
      by_contra hc'
      push Not at hc'
      exact hv0 (funext hc')
    obtain ⟨i, hi⟩ := hvne
    have hpos : 0 < ∑ k, (v k)^2 :=
      Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    nlinarith [hc, hpos]
  -- ## The diagonal, lower and upper bounds.
  have hdiag : ∀ i : Fin n, c ≤ A i i := by
    intro i
    have h := hlow (Pi.single i (1:ℝ))
    rw [qform_eq_dotProduct, sum_sq_eq_dotProduct, single_dot_mulVec_single,
        dotProduct_single_one, Pi.single_eq_same, mul_one] at h
    exact h
  have hdiag_le : ∀ i : Fin n, A i i ≤ C := by
    intro i
    have h := hup (Pi.single i (1:ℝ))
    rw [qform_eq_dotProduct, sum_sq_eq_dotProduct, single_dot_mulVec_single,
        dotProduct_single_one, Pi.single_eq_same, mul_one] at h
    exact h
  -- ## Off-diagonal bounds, by polarisation with `eᵢ ± eⱼ`.
  have habs : ∀ i j : Fin n, |A i j| ≤ C := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · rw [abs_of_pos (lt_of_lt_of_le hc (hdiag i))]
      exact hdiag_le i
    · have h1 := hup (Pi.single i (1:ℝ) + Pi.single j (1:ℝ))
      rw [qform_eq_dotProduct, sq_add i j hij, qf_add A i j] at h1
      have h2 := hup (Pi.single i (1:ℝ) - Pi.single j (1:ℝ))
      rw [qform_eq_dotProduct, sq_sub i j hij, qf_sub A i j] at h2
      rw [hsymm j i] at h1 h2
      have hA : 2 * A i j ≤ 2 * C - A i i - A j j := by linarith
      have hB : -(2 * A i j) ≤ 2 * C - A i i - A j j := by linarith
      have hR : 2 * C - A i i - A j j ≤ 2 * C := by
        have h1 := hdiag i
        have h2 := hdiag j
        linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- ## The entries of the inverse, via the columns of `A⁻¹`.
  have hinv : ∀ i j : Fin n, |A⁻¹ i j| ≤ 1 / c := by
    have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)
    intro i j
    set v : Fin n → ℝ := A⁻¹ *ᵥ (Pi.single j (1:ℝ)) with hvdef
    have hv_apply : ∀ k, v k = A⁻¹ k j := by
      intro k
      rw [hvdef, Matrix.mulVec_single]
      simp [Matrix.col]
    have hmulv : A *ᵥ v = Pi.single j (1:ℝ) := by
      rw [hvdef, Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec]
    have hlowv := hlow v
    rw [qform_eq_dotProduct, hmulv, dotProduct_single_one] at hlowv
    set S : ℝ := ∑ k, (v k)^2 with hSdef
    have hSnn : 0 ≤ S := by
      rw [hSdef]
      exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hvj_le : v j ≤ Real.sqrt S := by
      have h1 : (v j)^2 ≤ S := by
        rw [hSdef]
        exact Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      have h2 : |v j| ≤ Real.sqrt S := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt h1
      exact le_trans (le_abs_self _) h2
    have ht : Real.sqrt S ≤ 1 / c := by
      have hle : c * S ≤ Real.sqrt S := le_trans hlowv hvj_le
      rcases eq_or_lt_of_le (Real.sqrt_nonneg S) with h | h
      · rw [← h]
        positivity
      · have h2 : c * Real.sqrt S ≤ 1 := by
          have hsq := Real.sq_sqrt hSnn
          have : c * Real.sqrt S * Real.sqrt S ≤ 1 * Real.sqrt S := by nlinarith [hle, hsq]
          exact le_of_mul_le_mul_right this h
        rw [le_div_iff₀ hc]
        linarith
    have hvi : |v i| ≤ Real.sqrt S := by
      have h1 : (v i)^2 ≤ S := by
        rw [hSdef]
        exact Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    rw [← hv_apply i]
    exact le_trans hvi ht
  exact ⟨hdet, hdiag, habs, hinv⟩

end Work.Diff.EXT.GramInv
