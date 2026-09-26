/-
# Integer Frobenius norm of `SL(2,ℤ)` and its basic API

The growth bounds for the carries are polynomial in the Frobenius norm `‖γ‖² = a² + b² + c² + d²`
of a group element `γ ∈ SL(2,ℤ)`.  For the reduction arguments it is convenient to have this
quantity as a natural number (`frobSq`), so that "the norm strictly decreases" is a statement
about `ℕ` and immediately bounds the number of reduction steps.

This file collects the elementary API: the relation with the real Frobenius norm
`Work.Asymptotics.Frob` and submultiplicativity.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateBounds.Defs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The **squared Frobenius norm** of `γ ∈ SL(2,ℤ)` as a natural number,
`frobSq γ = a² + b² + c² + d²` for `γ = !![a,b;c,d]`. -/
def frobSq (γ : SL(2,ℤ)) : ℕ :=
  (γ 0 0).natAbs ^ 2 + (γ 0 1).natAbs ^ 2 + (γ 1 0).natAbs ^ 2 + (γ 1 1).natAbs ^ 2

/-- The sum of squares of the entries of a `2 × 2` matrix, as a real number. -/
def sqsum (A : Matrix (Fin 2) (Fin 2) ℤ) : ℝ := ∑ i : Fin 2, ∑ j : Fin 2, ((A i j : ℤ) : ℝ) ^ 2

private lemma natAbs_sq_cast (z : ℤ) : ((z.natAbs : ℝ)) ^ 2 = ((z : ℝ)) ^ 2 := by
  rw [Nat.cast_natAbs]
  push_cast
  rw [sq_abs]

@[simp] lemma frobSq_neg (γ : SL(2,ℤ)) : frobSq (-γ) = frobSq γ := by
  have h : ∀ i j : Fin 2, ((-γ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = -(γ i j) :=
    fun i j => rfl
  simp only [frobSq, h, Int.natAbs_neg]

lemma frobSq_pos (γ : SL(2,ℤ)) : 0 < frobSq γ := by
  have h1 : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 := by
    have h := γ.2; rw [Matrix.det_fin_two] at h; exact h
  by_contra h
  push_neg at h
  have h0 : frobSq γ = 0 := Nat.eq_zero_of_le_zero h
  have hz : (γ 0 0) = 0 ∧ (γ 0 1) = 0 ∧ (γ 1 0) = 0 ∧ (γ 1 1) = 0 := by
    simp only [frobSq, Nat.add_eq_zero_iff, pow_eq_zero_iff (n := 2) (by norm_num),
      Int.natAbs_eq_zero] at h0
    exact ⟨h0.1.1.1, h0.1.1.2, h0.1.2, h0.2⟩
  rw [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2] at h1
  norm_num at h1

/-- The cast of `frobSq` to `ℝ` is `sqsum` of the underlying matrix. -/
lemma coe_frobSq (γ : SL(2,ℤ)) :
    (frobSq γ : ℝ) = sqsum (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  simp only [frobSq, sqsum, Fin.sum_univ_two]
  push_cast
  rw [natAbs_sq_cast, natAbs_sq_cast, natAbs_sq_cast, natAbs_sq_cast]
  ring

/-- The real Frobenius norm is the square root of `frobSq`. -/
lemma Frob_eq_sqrt_frobSq (γ : SL(2,ℤ)) : Frob γ = Real.sqrt (frobSq γ) := by
  rw [Frob, coe_frobSq γ]
  congr 1
  simp only [sqsum, Fin.sum_univ_two]
  ring

lemma one_le_Frob (γ : SL(2,ℤ)) : 1 ≤ Frob γ := by
  rw [Frob_eq_sqrt_frobSq, Real.one_le_sqrt]
  exact_mod_cast frobSq_pos γ

/-- Cauchy–Schwarz in the form needed for submultiplicativity. -/
private lemma cs (p q r s : ℝ) : (p * r + q * s) ^ 2 ≤ (p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2) := by
  nlinarith [sq_nonneg (p * s - q * r)]

/-- Submultiplicativity of the sum of squares under matrix multiplication (Cauchy–Schwarz). -/
lemma sqsum_mul_le (A B : Matrix (Fin 2) (Fin 2) ℤ) : sqsum (A * B) ≤ sqsum A * sqsum B := by
  simp only [sqsum, Fin.sum_univ_two, Matrix.mul_apply]
  push_cast
  have h1 := cs ((A 0 0 : ℤ) : ℝ) ((A 0 1 : ℤ) : ℝ) ((B 0 0 : ℤ) : ℝ) ((B 1 0 : ℤ) : ℝ)
  have h2 := cs ((A 0 0 : ℤ) : ℝ) ((A 0 1 : ℤ) : ℝ) ((B 0 1 : ℤ) : ℝ) ((B 1 1 : ℤ) : ℝ)
  have h3 := cs ((A 1 0 : ℤ) : ℝ) ((A 1 1 : ℤ) : ℝ) ((B 0 0 : ℤ) : ℝ) ((B 1 0 : ℤ) : ℝ)
  have h4 := cs ((A 1 0 : ℤ) : ℝ) ((A 1 1 : ℤ) : ℝ) ((B 0 1 : ℤ) : ℝ) ((B 1 1 : ℤ) : ℝ)
  nlinarith [h1, h2, h3, h4]

/-- Submultiplicativity of the Frobenius norm on `SL(2,ℤ)`. -/
lemma Frob_mul_le (x y : SL(2,ℤ)) : Frob (x * y) ≤ Frob x * Frob y := by
  rw [Frob_eq_sqrt_frobSq, Frob_eq_sqrt_frobSq x, Frob_eq_sqrt_frobSq y,
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hxy : ((x * y : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (x : Matrix (Fin 2) (Fin 2) ℤ) * (y : Matrix (Fin 2) (Fin 2) ℤ) := rfl
  rw [coe_frobSq, coe_frobSq x, coe_frobSq y, hxy]
  exact sqsum_mul_le _ _

end Work.Asymptotics
