import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.exists_conj_z
import Submission.Work.L2F.Involution.exists_inverting_z

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Involution

/-- For any `x ∈ SL(2,F)` with `x² = -1` (odd characteristic) there is `w ∈ SL(2,F)` with
`w x w⁻¹ = -x` and `w² = -1`.  Proof: `exists_conj_z` gives `P` with `P * x = z * P` (`z` the
companion matrix); take the explicit `w₀` inverting `z` with `w₀² = -1` (`exists_inverting_z`) and
set `w := P⁻¹ * w₀ * P`; conjugation by `P` maps `z` to `x` and `-z` to `-x`, and
`w² = P⁻¹ * w₀² * P = -1`. -/
theorem exists_inverting (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) F,
      w * x * w⁻¹ = Work.L2F.negOne F * x ∧ w * w = Work.L2F.negOne F := by
  -- Conjugating matrix `P` and its inverse.
  obtain ⟨P, hPd, hP⟩ := Work.L2F.Mat2.exists_conj_z F h2 x hx
  -- The explicit `w₀` inverting `z`, with `w₀² = -1`.
  obtain ⟨w0, hw0conj, hw0sq⟩ := Work.L2F.Involution.exists_inverting_z F h2
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hX
  set W0 : Matrix (Fin 2) (Fin 2) F := (w0 : Matrix (Fin 2) (Fin 2) F) with hW0
  set Z : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0] with hZ
  have hz : ((Work.L2F.z F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = Z := by
    rw [hZ]; rfl
  have hn : ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 := rfl
  have hW0det : W0.det = 1 := by rw [hW0]; exact Matrix.SpecialLinearGroup.det_coe w0
  -- `P` is invertible; both products with its nonsingular inverse are `1`, and
  -- `det P⁻¹ = (det P)⁻¹`.
  have huP : IsUnit P.det := isUnit_iff_ne_zero.mpr hPd
  have hPinvP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P huP
  have hPPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P huP
  have hdetPinv : (P⁻¹).det = (P.det)⁻¹ := by
    have h : (P⁻¹).det * P.det = 1 := by rw [← Matrix.det_mul, hPinvP, Matrix.det_one]
    exact eq_inv_of_mul_eq_one_left h
  -- The relation `P * x = z * P` in matrix form.
  have hPX : P * X = Z * P := by rw [hX, hZ]; exact hP
  -- Conjugation by `P⁻¹` is multiplicative on matrices.
  have hconj : ∀ A B : Matrix (Fin 2) (Fin 2) F,
      (P⁻¹ * A * P) * (P⁻¹ * B * P) = P⁻¹ * (A * B) * P := by
    intro A B
    have hA : ∀ M : Matrix (Fin 2) (Fin 2) F, P * (P⁻¹ * M) = M := fun M => by
      rw [← Matrix.mul_assoc, hPPinv, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hA]
  -- Consequently `x = P⁻¹ * z * P`.
  have hXeq : X = P⁻¹ * Z * P := by
    calc X = (P⁻¹ * P) * X := by rw [hPinvP, Matrix.one_mul]
      _ = P⁻¹ * (P * X) := Matrix.mul_assoc _ _ _
      _ = P⁻¹ * (Z * P) := by rw [hPX]
      _ = P⁻¹ * Z * P := (Matrix.mul_assoc _ _ _).symm
  -- `w₀` anticommutes with `z`, and `w₀² = -1`, at the matrix level.
  have hW0Z : W0 * Z = -(Z * W0) := by
    have h1 : w0 * Work.L2F.z F = Work.L2F.negOne F * Work.L2F.z F * w0 := by
      calc w0 * Work.L2F.z F = w0 * Work.L2F.z F * w0⁻¹ * w0 := by group
        _ = Work.L2F.negOne F * Work.L2F.z F * w0 := by rw [hw0conj]
    have h2 := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, hz, hn] at h2
    simpa using h2
  have hW0sq : W0 * W0 = -1 := by
    have h2 := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) hw0sq
    simpa only [Matrix.SpecialLinearGroup.coe_mul, hn, hW0] using h2
  -- `W := P⁻¹ * w₀ * P` has determinant `1`.
  have hWdet : (P⁻¹ * W0 * P).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdetPinv, hW0det, mul_one, inv_mul_cancel₀ hPd]
  -- `W² = -1` and `W` anticommutes with `x`.
  have hWW : (P⁻¹ * W0 * P) * (P⁻¹ * W0 * P) = -1 := by
    rw [hconj W0 W0, hW0sq]
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, hPinvP]
  have hWX : (P⁻¹ * W0 * P) * X =
      (-1 : Matrix (Fin 2) (Fin 2) F) * X * (P⁻¹ * W0 * P) := by
    have h1 : (P⁻¹ * W0 * P) * X = P⁻¹ * (W0 * Z) * P := by rw [hXeq, hconj W0 Z]
    have h2 : (-1 : Matrix (Fin 2) (Fin 2) F) * X * (P⁻¹ * W0 * P) =
        -(P⁻¹ * (Z * W0) * P) := by
      rw [hXeq, Matrix.mul_assoc, hconj Z W0, neg_one_mul]
    rw [h1, h2, hW0Z, Matrix.mul_neg, Matrix.neg_mul]
  -- The witness `w ∈ SL(2,F)`.
  let w : Matrix.SpecialLinearGroup (Fin 2) F := ⟨P⁻¹ * W0 * P, hWdet⟩
  refine ⟨w, ?_, ?_⟩
  · -- `w x = -x w`, hence `w x w⁻¹ = -x`.
    have hwx : w * x = Work.L2F.negOne F * x * w := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, hn]
      show (P⁻¹ * W0 * P) * X = (-1 : Matrix (Fin 2) (Fin 2) F) * X * (P⁻¹ * W0 * P)
      exact hWX
    calc w * x * w⁻¹ = (Work.L2F.negOne F * x * w) * w⁻¹ := by rw [hwx]
      _ = Work.L2F.negOne F * x := by group
  · -- `w² = -1`.
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hn]
    show (P⁻¹ * W0 * P) * (P⁻¹ * W0 * P) = -1
    exact hWW

end Work.L2F.Involution
