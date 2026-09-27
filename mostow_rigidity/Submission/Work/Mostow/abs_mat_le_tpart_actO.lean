import Mathlib
import Submission.Work.Mostow.poAux

/-!
# Bounding the entries of a matrix in `O(n,1)` by `tpart (actO A 0)`

For `A : O(n,1)` write `d = mat A (Sum.inr 0) (Sum.inr 0)` for the bottom-right (time–time)
entry.  The defining relations `Mᵀ J M = J` and `M J Mᵀ = J` (`J = pmOneMat`) say that the
columns (resp. rows) of `M = mat A` are `mform`-orthonormal with respect to the Minkowski form
`mform x y = Σᵢ xᵢ yᵢ − x_{n} y_{n}`.  Taking diagonal relations gives

* `∑ i, (mat A (inl i) (inr 0))^2 = d^2 - 1`  (last column is timelike),
* `∑ i, (mat A (inr 0) (inl i))^2 = d^2 - 1`  (last row is timelike),
* `∑ i, (mat A (inl i) (inl b))^2 = 1 + (mat A (inr 0) (inl b))^2`  (spacelike columns),

and hence every entry `mat A i j` satisfies `(mat A i j)^2 ≤ d^2`.  Finally
`actO A 0` has coordinates `tsign A * mat A (inl i) (inr 0)`, so
`tpart (actO A 0)^2 = 1 + ‖actO A 0‖^2 = 1 + (d^2 - 1) = d^2`, i.e.
`tpart (actO A 0) = |d|`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Matrix

noncomputable section

/-- `mform` of a normalised spatial coordinate vector is `1`. -/
lemma mform_single_inl {n : ℕ} (b : Fin n) :
    mform (Pi.single (Sum.inl b) (1 : ℝ)) (Pi.single (Sum.inl b) (1 : ℝ)) = 1 := by
  rw [mform_self_apply]; simp [Pi.single_apply]

/-- The last column `p ↦ mat A p (inr 0)` is timelike, of `mform`-square `-1`. -/
lemma sum_col_sq {n : ℕ} (A : O1 n) :
    (∑ i : Fin n, (mat A (Sum.inl i) (Sum.inr 0)) ^ 2) =
      (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 - 1 := by
  have h := mform_mat_mulVec A (hlift (0 : E n)) (hlift (0 : E n))
  rw [mform_hlift_self] at h
  have hw : ∀ i : Fin n,
      (mat A *ᵥ hlift (0 : E n)) (Sum.inl i) = mat A (Sum.inl i) (Sum.inr 0) := by
    intro i; rw [hlift_zero, Matrix.mulVec_single_one]; rfl
  have hw0 : (mat A *ᵥ hlift (0 : E n)) (Sum.inr 0) = mat A (Sum.inr 0) (Sum.inr 0) := by
    rw [hlift_zero, Matrix.mulVec_single_one]; rfl
  rw [mform_self_apply] at h
  simp only [hw, hw0] at h
  linarith

/-- The last row `p ↦ mat A (inr 0) p` is timelike, of `mform`-square `-1`. -/
lemma sum_row_sq {n : ℕ} (A : O1 n) :
    (∑ i : Fin n, (mat A (Sum.inr 0) (Sum.inl i)) ^ 2) =
      (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 - 1 := by
  have h := mform_matTranspose_mulVec A (hlift (0 : E n)) (hlift (0 : E n))
  rw [mform_hlift_self] at h
  have hw : ∀ i : Fin n,
      ((mat A)ᵀ *ᵥ hlift (0 : E n)) (Sum.inl i) = mat A (Sum.inr 0) (Sum.inl i) := by
    intro i; rw [hlift_zero, Matrix.mulVec_single_one]; rfl
  have hw0 : ((mat A)ᵀ *ᵥ hlift (0 : E n)) (Sum.inr 0) = mat A (Sum.inr 0) (Sum.inr 0) := by
    rw [hlift_zero, Matrix.mulVec_single_one]; rfl
  rw [mform_self_apply] at h
  simp only [hw, hw0] at h
  linarith

/-- Each spacelike column `p ↦ mat A p (inl b)` has `mform`-square `1`. -/
lemma sum_tl_sq {n : ℕ} (A : O1 n) (b : Fin n) :
    (∑ i : Fin n, (mat A (Sum.inl i) (Sum.inl b)) ^ 2) =
      1 + (mat A (Sum.inr 0) (Sum.inl b)) ^ 2 := by
  have h := mform_mat_mulVec A (Pi.single (Sum.inl b) 1) (Pi.single (Sum.inl b) 1)
  rw [mform_single_inl] at h
  have hw : ∀ i : Fin n,
      (mat A *ᵥ Pi.single (Sum.inl b) 1) (Sum.inl i) = mat A (Sum.inl i) (Sum.inl b) := by
    intro i; rw [Matrix.mulVec_single_one]; rfl
  have hw0 : (mat A *ᵥ Pi.single (Sum.inl b) 1) (Sum.inr 0) = mat A (Sum.inr 0) (Sum.inl b) := by
    rw [Matrix.mulVec_single_one]; rfl
  rw [mform_self_apply] at h
  simp only [hw, hw0] at h
  linarith

/-- The hyperbolic norm square of `actO A 0`. -/
lemma norm_sq_actO_zero {n : ℕ} (A : O1 n) :
    ‖actO A (0 : E n)‖ ^ 2 = (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 - 1 := by
  rw [norm_sq_eq_sum]
  have hw : ∀ i : Fin n,
      (actO A (0 : E n)).ofLp i = tsign A * mat A (Sum.inl i) (Sum.inr 0) := by
    intro i
    simp only [actO, WithLp.ofLp_toLp, hlift_zero, Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [hw]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, sum_col_sq A]
  rw [show tsign A ^ 2 = (1 : ℝ) from by rw [pow_two, tsign_sq]]
  ring

/-- `tpart (actO A 0)` is the absolute value of the bottom-right entry of `mat A`. -/
lemma tpart_actO_zero {n : ℕ} (A : O1 n) :
    tpart (actO A (0 : E n)) = |mat A (Sum.inr 0) (Sum.inr 0)| := by
  rw [tpart, norm_sq_actO_zero]
  rw [show (1 : ℝ) + ((mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 - 1) =
      (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 from by ring]
  exact Real.sqrt_sq_eq_abs _

/-- Every entry of `mat A` is bounded in square by the square of the bottom-right entry. -/
lemma entry_sq_le {n : ℕ} (A : O1 n) (i j : Fin n ⊕ Fin 1) :
    (mat A i j) ^ 2 ≤ (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 := by
  have hcol := sum_col_sq A
  have hrow := sum_row_sq A
  rcases i with a | b
  · rcases j with c | d
    · calc (mat A (Sum.inl a) (Sum.inl c)) ^ 2
        ≤ ∑ i : Fin n, (mat A (Sum.inl i) (Sum.inl c)) ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin n => (mat A (Sum.inl i) (Sum.inl c)) ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ a)
        _ = 1 + (mat A (Sum.inr 0) (Sum.inl c)) ^ 2 := sum_tl_sq A c
        _ ≤ 1 + ((mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 - 1) := by
            have hb := Finset.single_le_sum
              (f := fun i : Fin n => (mat A (Sum.inr 0) (Sum.inl i)) ^ 2)
              (fun i _ => sq_nonneg _) (Finset.mem_univ c)
            rw [hrow] at hb
            linarith
        _ = (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 := by ring
    · obtain rfl : d = 0 := Subsingleton.elim _ _
      calc (mat A (Sum.inl a) (Sum.inr 0)) ^ 2
        ≤ ∑ i : Fin n, (mat A (Sum.inl i) (Sum.inr 0)) ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin n => (mat A (Sum.inl i) (Sum.inr 0)) ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ a)
        _ = (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 - 1 := hcol
        _ ≤ (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 := by linarith
  · obtain rfl : b = 0 := Subsingleton.elim _ _
    rcases j with c | d
    · calc (mat A (Sum.inr 0) (Sum.inl c)) ^ 2
        ≤ ∑ i : Fin n, (mat A (Sum.inr 0) (Sum.inl i)) ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin n => (mat A (Sum.inr 0) (Sum.inl i)) ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ c)
        _ = (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 - 1 := hrow
        _ ≤ (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 := by linarith
    · obtain rfl : d = 0 := Subsingleton.elim _ _
      exact le_refl _

theorem abs_mat_le_tpart_actO {n : ℕ} (A : Submission.Mostow.O1 n) (i j : Fin n ⊕ Fin 1) :
    |Submission.Mostow.mat A i j| ≤ Submission.Mostow.tpart (Submission.Mostow.actO A (0 : Submission.Mostow.E n)) := by
  rw [tpart_actO_zero A]
  exact sq_le_sq.mp (entry_sq_le A i j)

end

end Work.Mostow
