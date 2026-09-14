import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Analysis.Fourier.gaussian_psf_core

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Commons.Analysis.Fourier
namespace GaussianPsfAssembly

lemma smul_mulVec_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    ((c • A).mulVec x) i = c • (A.mulVec x) i := by
  calc
    ((c • A).mulVec x) i = ∑ j : Fin n, (c • A) i j * x j := by
      simp only [Matrix.mulVec, dotProduct]
    _ = ∑ j : Fin n, c * (A i j * x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
      ring
    _ = c * (∑ j : Fin n, A i j * x j) := by
      exact (Finset.mul_sum Finset.univ (fun j : Fin n => A i j * x j) c).symm
    _ = c • (A.mulVec x) i := by
      simp only [Matrix.mulVec, dotProduct, smul_eq_mul]

lemma inv_smul_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  calc
    (c • A) * (c⁻¹ • A⁻¹) = c • (A * (c⁻¹ • A⁻¹)) := by rw [Matrix.smul_mul]
    _ = c • (c⁻¹ • (A * A⁻¹)) := by rw [Matrix.mul_smul]
    _ = (c * c⁻¹) • (A * A⁻¹) := by rw [smul_smul]
    _ = 1 := by
      have hc' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
      rw [Matrix.mul_nonsing_inv A hc']
      rw [mul_inv_cancel₀ hc]
      simp

lemma transpose_smul' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (c • A).transpose = c • A.transpose := by
  ext i j
  rfl

lemma det_smul_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (s : ℝ)
    (hs : s ≠ 0) : ((s⁻¹) • A).det ≠ 0 := by
  rw [Matrix.det_smul]
  rw [show Fintype.card (Fin n) = n by simp]
  exact mul_ne_zero (pow_ne_zero n (inv_ne_zero hs)) hA

lemma abs_det_inv_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (hs : 0 < s) :
    |((s⁻¹) • A).det|⁻¹ = s ^ n / |A.det| := by
  have hs' : s ≠ 0 := ne_of_gt hs
  rw [Matrix.det_smul]
  rw [show Fintype.card (Fin n) = n by simp]
  rw [abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hs) n)]
  rw [mul_inv]
  congr 1
  rw [inv_pow, inv_inv]

lemma dual_scaled {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (s : ℝ) (hs : s ≠ 0) :
    (((s⁻¹) • A)⁻¹).transpose = s • (A⁻¹).transpose := by
  calc
    (((s⁻¹) • A)⁻¹).transpose = (((s⁻¹) • A).transpose)⁻¹ := by
      exact Matrix.transpose_nonsing_inv ((s⁻¹) • A)
    _ = ((s⁻¹) • A.transpose)⁻¹ := by rw [transpose_smul']
    _ = (s⁻¹)⁻¹ • (A.transpose)⁻¹ := by
      exact inv_smul_matrix A.transpose (by simpa [Matrix.det_transpose] using hA) (s⁻¹) (inv_ne_zero hs)
    _ = s • (A⁻¹).transpose := by
      rw [inv_inv]
      rw [Matrix.transpose_nonsing_inv A]

lemma sum_sq_scaled_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (hs : s ≠ 0)
    (k : Fin n → ℤ) :
    (∑ i, ((((s⁻¹) • A).mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2) =
      (∑ i, ((A.mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2) / s ^ 2 := by
  calc
    (∑ i, ((((s⁻¹) • A).mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2)
        = ∑ i, (((A.mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2 / s ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [smul_mulVec_apply A (s⁻¹) (fun j : Fin n => (k j : ℝ)) i]
          rw [smul_eq_mul, mul_pow, inv_pow]
          field_simp [hs]
    _ = (∑ i, ((A.mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2) / s ^ 2 := by
          rw [Finset.sum_div]

lemma sum_sq_scaled_dual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (s : ℝ)
    (hs : s ≠ 0) (m : Fin n → ℤ) :
    (∑ i, ((((((s⁻¹) • A)⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2) =
      s ^ 2 * (∑ i, ((((A⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2) := by
  have hdual := dual_scaled A hA s hs
  calc
    (∑ i, ((((((s⁻¹) • A)⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2)
        = ∑ i, (s • ((((A⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hdual]
          rw [smul_mulVec_apply ((A⁻¹).transpose) s (fun j : Fin n => (m j : ℝ)) i]
    _ = ∑ i, (s ^ 2 * ((((A⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [smul_eq_mul]
          ring
    _ = s ^ 2 * (∑ i, ((((A⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2) := by
          rw [Finset.mul_sum]

end GaussianPsfAssembly
open GaussianPsfAssembly

theorem gaussian_psf_matrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (s : ℝ)
    (hs : 0 < s) :
    (∑' k : Fin n → ℤ, Real.exp (-Real.pi * (∑ i, (((A.mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2)) / s ^ 2)) =
      s ^ n / |A.det| *
        (∑' m : Fin n → ℤ,
          Real.exp (-Real.pi * s ^ 2 * (∑ i, ((((A⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2))) := by
  have hs' : s ≠ 0 := ne_of_gt hs
  let C : Matrix (Fin n) (Fin n) ℝ := (s⁻¹) • A
  have hC : C.det ≠ 0 := by simpa [C] using det_smul_ne_zero A hA s hs'
  have hcore := gaussian_psf_core n C hC
  have hfac : |C.det|⁻¹ = s ^ n / |A.det| := by simpa [C] using abs_det_inv_smul A s hs
  have hsumL : (∑' k : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i, (((A.mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2)) / s ^ 2)) =
      (∑' k : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i, (((C.mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2)))) := by
    apply tsum_congr
    intro k
    congr 1
    rw [sum_sq_scaled_left A s hs' k]
    field_simp [hs']
  have hsumR : (∑' m : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i, ((((C⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2))) =
      (∑' m : Fin n → ℤ,
        Real.exp (-Real.pi * s ^ 2 * (∑ i, ((((A⁻¹).transpose).mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2))) := by
    apply tsum_congr
    intro m
    congr 1
    rw [sum_sq_scaled_dual A hA s hs' m]
    ring
  rw [hsumL, hcore, hfac, hsumR]

end Commons.Analysis.Fourier