import Mathlib
import Submission.Mostow.Interfaces

/-!
# Auxiliary algebra for the `PO(n,1)` action (area T1)

Explicit matrix algebra over `Fin n ⊕ Fin 1`: the time coordinate is `Sum.inr 0`,
`J = pmOneMat = diag(1,…,1,−1)` and the Minkowski form is `mform x y = xᵀ J y`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-! ## The Minkowski form -/

/-- The Minkowski bilinear form `xᵀ J y` on `ℝ^{Fin n ⊕ Fin 1}`. -/
def mform (x y : Fin n ⊕ Fin 1 → ℝ) : ℝ := x ⬝ᵥ (pmOneMat.mulVec y)

/-- The null vector `(ξ, 1)` over `ξ : E n`. -/
def theta (ξ : E n) : Fin n ⊕ Fin 1 → ℝ := Sum.elim (fun i => ξ i) (fun _ => 1)

lemma pmOneMat_transpose :
    (pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)ᵀ = pmOneMat := by
  rw [pmOneMat, Matrix.fromBlocks_transpose]; simp

lemma pmOneMat_mulVec_inl (y : Fin n ⊕ Fin 1 → ℝ) (i : Fin n) :
    (pmOneMat.mulVec y) (Sum.inl i) = y (Sum.inl i) := by
  rw [pmOneMat, Matrix.fromBlocks_mulVec]; simp

lemma pmOneMat_mulVec_inr (y : Fin n ⊕ Fin 1 → ℝ) (i : Fin 1) :
    (pmOneMat.mulVec y) (Sum.inr i) = - y (Sum.inr i) := by
  rw [pmOneMat, Matrix.fromBlocks_mulVec]; simp [Matrix.neg_mulVec]

lemma mform_apply (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform x y = (∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)) - x (Sum.inr 0) * y (Sum.inr 0) := by
  rw [mform, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_one]
  simp [pmOneMat_mulVec_inl, pmOneMat_mulVec_inr, sub_eq_add_neg, mul_neg]

lemma mform_self_apply (x : Fin n ⊕ Fin 1 → ℝ) :
    mform x x = (∑ i : Fin n, x (Sum.inl i) ^ 2) - x (Sum.inr 0) ^ 2 := by
  rw [mform_apply]; simp [pow_two]

lemma mform_comm (x y : Fin n ⊕ Fin 1 → ℝ) : mform x y = mform y x := by
  rw [mform_apply, mform_apply]
  have h : (∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)) =
      ∑ i : Fin n, y (Sum.inl i) * x (Sum.inl i) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h, mul_comm]

/-! ## Invariance of `mform` under `O(n,1)` -/

lemma mform_mulVec (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (h : Mᵀ * pmOneMat * M = pmOneMat) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform (M.mulVec x) (M.mulVec y) = mform x y := by
  simp only [mform]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [show (pmOneMat * M) = (Mᵀ * pmOneMat)ᵀ by rw [Matrix.transpose_mul, pmOneMat_transpose]; simp]
  rw [Matrix.vecMul_transpose, Matrix.mulVec_mulVec, h]
  rw [dotProduct_comm]
  rw [← Matrix.dotProduct_transpose_mulVec (A := (pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ))
      (x := x) (y := y)]
  rw [pmOneMat_transpose]

lemma O1_form_col (A : O1 n) : (mat A)ᵀ * pmOneMat * mat A = pmOneMat := by
  have h1 : mat (star A) * mat A = 1 := by
    have h := A.2.1
    have h2 := congrArg MatrixSum.ofMatrix.symm h
    rwa [map_mul, map_one] at h2
  rw [show mat (star A) = pmOneMat * (mat A)ᵀ * pmOneMat from by
        simp [mat, MatrixSum.ofMatrix, star, Matrix.conjTranspose]; rfl] at h1
  have h3 := congrArg (fun x => pmOneMat * x) h1
  rw [mul_one] at h3
  simpa only [← mul_assoc, pmOneMat_mul_pmOneMat, one_mul] using h3

lemma O1_form_row (A : O1 n) : mat A * pmOneMat * (mat A)ᵀ = pmOneMat := by
  have h1 : mat A * mat (star A) = 1 := by
    have h := A.2.2
    have h2 := congrArg MatrixSum.ofMatrix.symm h
    rwa [map_mul, map_one] at h2
  rw [show mat (star A) = pmOneMat * (mat A)ᵀ * pmOneMat from by
        simp [mat, MatrixSum.ofMatrix, star, Matrix.conjTranspose]; rfl] at h1
  have h3 := congrArg (fun x => x * pmOneMat) h1
  rw [one_mul] at h3
  simpa only [mul_assoc, pmOneMat_mul_pmOneMat, mul_one] using h3

lemma mform_mat_mulVec (A : O1 n) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform (mat A *ᵥ x) (mat A *ᵥ y) = mform x y :=
  mform_mulVec (mat A) (O1_form_col A) x y

lemma mform_matTranspose_mulVec (A : O1 n) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform ((mat A)ᵀ *ᵥ x) ((mat A)ᵀ *ᵥ y) = mform x y :=
  mform_mulVec (mat A)ᵀ (by simpa using O1_form_row A) x y

/-! ## The chart and the hyperboloid -/

lemma hlift_inl (u : E n) (i : Fin n) : hlift u (Sum.inl i) = u i := rfl
lemma hlift_inr (u : E n) : hlift u (Sum.inr 0) = tpart u := rfl

lemma tpart_pos (u : E n) : 0 < tpart u :=
  Real.sqrt_pos.2 (by positivity)

lemma tpart_sq (u : E n) : tpart u ^ 2 = 1 + ‖u‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma norm_sq_eq_sum (u : E n) : ‖u‖ ^ 2 = ∑ i, u i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq u

lemma inner_eq_sum (u v : E n) : inner ℝ u v = ∑ i, u i * v i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma hlift_zero : hlift (0 : E n) = Pi.single (Sum.inr 0) (1 : ℝ) := by
  ext a
  rcases a with i | j
  · simp [hlift]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [hlift, tpart]

lemma mform_hlift_self (u : E n) : mform (hlift u) (hlift u) = -1 := by
  rw [mform_self_apply]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hlift_inl]), hlift_inr, tpart_sq,
    norm_sq_eq_sum]
  ring

lemma mform_hlift_hlift (u v : E n) :
    mform (hlift u) (hlift v) = inner ℝ u v - tpart u * tpart v := by
  rw [mform_apply]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hlift_inl, hlift_inl]), hlift_inr, hlift_inr,
    inner_eq_sum]

lemma hlift_injective : Function.Injective (hlift : E n → Fin n ⊕ Fin 1 → ℝ) := by
  intro u v h
  ext i
  have := congrFun h (Sum.inl i)
  rwa [hlift_inl, hlift_inl] at this

/-- A vector on the upper sheet of the hyperboloid is the lift of its spatial part. -/
lemma eq_hlift_of_upper (y : Fin n ⊕ Fin 1 → ℝ) (h1 : mform y y = -1)
    (h2 : 0 < y (Sum.inr 0)) :
    y = hlift (WithLp.toLp 2 (fun i : Fin n => y (Sum.inl i))) := by
  have hsq : y (Sum.inr 0) ^ 2 = 1 + ∑ i, y (Sum.inl i) ^ 2 := by
    have h := mform_self_apply y
    rw [h1] at h
    linarith
  have hnorm : ‖(WithLp.toLp 2 (fun i : Fin n => y (Sum.inl i)) : E n)‖ ^ 2 =
      ∑ i, y (Sum.inl i) ^ 2 := by
    rw [norm_sq_eq_sum]
  ext a
  rcases a with i | j
  · simp [hlift]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [hlift_inr, tpart]
    rw [hnorm, ← hsq, Real.sqrt_sq (le_of_lt h2)]

/-! ## The boundary null vectors -/

lemma theta_inl (ξ : E n) (i : Fin n) : theta ξ (Sum.inl i) = ξ i := rfl
lemma theta_inr (ξ : E n) : theta ξ (Sum.inr 0) = 1 := rfl

lemma mem_Sph_iff (ξ : E n) : ξ ∈ Sph n ↔ ‖ξ‖ = 1 := by
  rw [Sph, Metric.mem_sphere, dist_zero_right]

lemma theta_self (ξ : E n) : mform (theta ξ) (theta ξ) = ‖ξ‖ ^ 2 - 1 := by
  rw [mform_self_apply]
  rw [Finset.sum_congr rfl (fun i _ => by rw [theta_inl]), theta_inr, norm_sq_eq_sum]
  norm_num

lemma theta_mform_self {ξ : E n} (hξ : ξ ∈ Sph n) : mform (theta ξ) (theta ξ) = 0 := by
  rw [theta_self, (mem_Sph_iff ξ).1 hξ]; ring

/-! ## `mat` interacts with the group operations -/

@[simp] lemma mat_one : mat (1 : O1 n) = 1 := by simp [mat]
@[simp] lemma mat_mul (A B : O1 n) : mat (A * B) = mat A * mat B := by simp [mat]
@[simp] lemma mat_neg (A : O1 n) : mat (-A) = -mat A := by
  simp only [mat, Unitary.coe_neg]; rw [map_neg]

lemma mat_star (A : O1 n) :
    mat (star A) = pmOneMat * (mat A)ᵀ * pmOneMat := by
  simp [mat, MatrixSum.ofMatrix, star, Matrix.conjTranspose]; rfl

lemma O1_mul_neg_one (A : O1 n) : A * (-1 : O1 n) = -A := by
  apply Subtype.ext
  simp [Unitary.coe_neg]

/-! ## Time-time entry -/

lemma O1_tt_sq_ge_one (A : O1 n) : 1 ≤ (mat A (Sum.inr 0) (Sum.inr 0)) ^ 2 := by
  have h := mform_mat_mulVec A (hlift (0 : E n)) (hlift (0 : E n))
  rw [mform_hlift_self] at h
  have hw : (mat A *ᵥ hlift (0 : E n)) (Sum.inr 0) = mat A (Sum.inr 0) (Sum.inr 0) := by
    rw [hlift_zero, Matrix.mulVec_single_one]; rfl
  rw [mform_self_apply, hw] at h
  have hsum : 0 ≤ ∑ i, (mat A *ᵥ hlift (0 : E n)) (Sum.inl i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

lemma O1_tt_ne_zero (A : O1 n) : mat A (Sum.inr 0) (Sum.inr 0) ≠ 0 := by
  intro h
  have := O1_tt_sq_ge_one A
  rw [h] at this; norm_num at this

/-! ## The time sign -/

lemma tsign_ne_zero (A : O1 n) : tsign A ≠ 0 := by
  rw [tsign]; split <;> norm_num

lemma tsign_sq (A : O1 n) : tsign A * tsign A = 1 := by
  rw [tsign]; split <;> norm_num

lemma tsign_eq_one_iff (A : O1 n) : tsign A = 1 ↔ 0 < mat A (Sum.inr 0) (Sum.inr 0) := by
  rw [tsign]
  constructor
  · intro h; by_contra hc
    rw [if_neg hc] at h; norm_num at h
  · intro h; rw [if_pos h]

lemma tsign_eq_neg_one_iff (A : O1 n) :
    tsign A = -1 ↔ mat A (Sum.inr 0) (Sum.inr 0) < 0 := by
  rw [tsign]
  constructor
  · intro h
    have hnc : ¬ (0 < mat A (Sum.inr 0) (Sum.inr 0)) := by
      intro hx; rw [if_pos hx] at h; norm_num at h
    exact lt_of_le_of_ne (le_of_not_gt hnc) (O1_tt_ne_zero A)
  · intro h; rw [if_neg (not_lt.2 h.le)]

lemma tsign_mul_tt (A : O1 n) :
    tsign A * mat A (Sum.inr 0) (Sum.inr 0) = |mat A (Sum.inr 0) (Sum.inr 0)| := by
  rcases lt_or_gt_of_ne (O1_tt_ne_zero A) with h | h
  · rw [tsign, if_neg (not_lt.2 h.le), abs_of_neg h]; ring
  · rw [tsign, if_pos h, abs_of_pos h]; ring


/-! ## Null vectors and invertibility -/

/-- A null vector with vanishing time coordinate is zero. -/
lemma eq_zero_of_mform_self_eq_zero (w : Fin n ⊕ Fin 1 → ℝ) (h : mform w w = 0)
    (ht : w (Sum.inr 0) = 0) : w = 0 := by
  rw [mform_self_apply, ht] at h
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), sub_zero] at h
  have h0 : ∀ i ∈ (Finset.univ : Finset (Fin n)), w (Sum.inl i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).1 h
  ext a
  rcases a with i | j
  · exact (sq_eq_zero_iff.1 (h0 i (Finset.mem_univ i)))
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    exact ht

/-- `mat A` is injective on vectors. -/
lemma eq_zero_of_mulVec_eq_zero (A : O1 n) {w : Fin n ⊕ Fin 1 → ℝ}
    (h : mat A *ᵥ w = 0) : w = 0 := by
  have hJ : pmOneMat *ᵥ w = 0 := by
    calc pmOneMat *ᵥ w = ((mat A)ᵀ * pmOneMat * mat A) *ᵥ w := by rw [O1_form_col A]
      _ = (mat A)ᵀ *ᵥ (pmOneMat *ᵥ (mat A *ᵥ w)) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by rw [h, Matrix.mulVec_zero, Matrix.mulVec_zero]
  calc w = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) *ᵥ w := by rw [Matrix.one_mulVec]
    _ = (pmOneMat * pmOneMat) *ᵥ w := by rw [pmOneMat_mul_pmOneMat]
    _ = pmOneMat *ᵥ (pmOneMat *ᵥ w) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hJ, Matrix.mulVec_zero]

lemma mat_mulVec_theta_mform (A : O1 n) (ξ : E n) :
    mform (mat A *ᵥ theta ξ) (mat A *ᵥ theta ξ) = mform (theta ξ) (theta ξ) :=
  mform_mat_mulVec A _ _

/-- For `ξ` on the boundary sphere, the time coordinate of `mat A *ᵥ (ξ,1)` does not vanish. -/
lemma mat_mulVec_theta_ne_zero (A : O1 n) {ξ : E n} (hξ : ξ ∈ Sph n) :
    (mat A *ᵥ theta ξ) (Sum.inr 0) ≠ 0 := by
  intro h0
  have hw : mat A *ᵥ theta ξ = 0 :=
    eq_zero_of_mform_self_eq_zero _ (by rw [mat_mulVec_theta_mform, theta_mform_self hξ]) h0
  have hz : theta ξ = 0 := eq_zero_of_mulVec_eq_zero A hw
  have : theta ξ (Sum.inr 0) = 0 := by rw [hz]; rfl
  rw [theta_inr] at this
  norm_num at this

/-- Renormalising a vector with non-vanishing time coordinate. -/
lemma smul_theta_of_time_ne_zero (u : Fin n ⊕ Fin 1 → ℝ) (ht : u (Sum.inr 0) ≠ 0) :
    u = u (Sum.inr 0) •
      theta (WithLp.toLp 2 (fun i : Fin n => u (Sum.inl i) / u (Sum.inr 0))) := by
  ext a
  rcases a with i | j
  · simp only [theta, Pi.smul_apply, Sum.elim_inl, smul_eq_mul]
    rw [mul_div_cancel₀ _ ht]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [theta]

lemma bdO_apply (A : O1 n) (ξ : E n) (i : Fin n) :
    bdO A ξ i = (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0) := rfl

/-! ## Membership criterion -/

lemma mem_unitary_iff (M : MatrixSum (Fin n) (Fin 1) ℝ) :
    M ∈ unitary (MatrixSum (Fin n) (Fin 1) ℝ) ↔
      ((MatrixSum.ofMatrix.symm M)ᵀ * pmOneMat * (MatrixSum.ofMatrix.symm M) = pmOneMat ∧
       (MatrixSum.ofMatrix.symm M) * pmOneMat * (MatrixSum.ofMatrix.symm M)ᵀ = pmOneMat) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · have h1' : MatrixSum.ofMatrix.symm (star M) * MatrixSum.ofMatrix.symm M = 1 := by
        have hh := congrArg MatrixSum.ofMatrix.symm h1
        rwa [map_mul, map_one] at hh
      rw [show MatrixSum.ofMatrix.symm (star M) = pmOneMat * (MatrixSum.ofMatrix.symm M)ᵀ * pmOneMat from by
            simp [star, MatrixSum.ofMatrix, Matrix.conjTranspose]; rfl] at h1'
      have h3 := congrArg (fun x => pmOneMat * x) h1'
      rw [mul_one] at h3
      simpa only [← mul_assoc, pmOneMat_mul_pmOneMat, one_mul] using h3
    · have h2' : MatrixSum.ofMatrix.symm M * MatrixSum.ofMatrix.symm (star M) = 1 := by
        have hh := congrArg MatrixSum.ofMatrix.symm h2
        rwa [map_mul, map_one] at hh
      rw [show MatrixSum.ofMatrix.symm (star M) = pmOneMat * (MatrixSum.ofMatrix.symm M)ᵀ * pmOneMat from by
            simp [star, MatrixSum.ofMatrix, Matrix.conjTranspose]; rfl] at h2'
      have h3 := congrArg (fun x => x * pmOneMat) h2'
      rw [one_mul] at h3
      simpa only [mul_assoc, pmOneMat_mul_pmOneMat, mul_one] using h3
  · rintro ⟨h1, h2⟩
    constructor
    · apply MatrixSum.ofMatrix.symm.injective
      rw [map_mul, map_one]
      rw [show MatrixSum.ofMatrix.symm (star M) = pmOneMat * (MatrixSum.ofMatrix.symm M)ᵀ * pmOneMat from by
            simp [star, MatrixSum.ofMatrix, Matrix.conjTranspose]; rfl]
      have key : (pmOneMat * (MatrixSum.ofMatrix.symm M)ᵀ * pmOneMat) * (MatrixSum.ofMatrix.symm M) = 1 := by
        have hh := congrArg (fun x => pmOneMat * x) h1
        rw [mul_assoc, pmOneMat_mul_pmOneMat] at hh
        simpa only [← mul_assoc, pmOneMat_mul_pmOneMat, one_mul] using hh
      exact key
    · apply MatrixSum.ofMatrix.symm.injective
      rw [map_mul, map_one]
      rw [show MatrixSum.ofMatrix.symm (star M) = pmOneMat * (MatrixSum.ofMatrix.symm M)ᵀ * pmOneMat from by
            simp [star, MatrixSum.ofMatrix, Matrix.conjTranspose]; rfl]
      have key : (MatrixSum.ofMatrix.symm M) * (pmOneMat * (MatrixSum.ofMatrix.symm M)ᵀ * pmOneMat) = 1 := by
        have hh := congrArg (fun x => x * pmOneMat) h2
        rw [mul_assoc, pmOneMat_mul_pmOneMat] at hh
        simpa only [mul_assoc, pmOneMat_mul_pmOneMat, mul_one] using hh
      exact key

/-- Build an element of `O(n,1)` from a matrix satisfying the defining relations. -/
def O1.ofMatrix (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (h : Mᵀ * pmOneMat * M = pmOneMat ∧ M * pmOneMat * Mᵀ = pmOneMat) : O1 n :=
  ⟨MatrixSum.ofMatrix M, (mem_unitary_iff (MatrixSum.ofMatrix M)).2 (by simpa using h)⟩

@[simp] lemma mat_O1_ofMatrix (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (h : Mᵀ * pmOneMat * M = pmOneMat ∧ M * pmOneMat * Mᵀ = pmOneMat) :
    mat (O1.ofMatrix M h) = M := by
  simp only [O1.ofMatrix, mat, MatrixSum.ofMatrix]
  rfl

end

end Work.Mostow
