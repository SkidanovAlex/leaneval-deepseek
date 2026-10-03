/-
The involution `starSkewL` on the skew Laurent polynomial ring `U[t^{±1};τ]` is a `∗`-ring
structure: it is additive, antimultiplicative, involutive, unital, and it is compatible with
the matrix star on the Toeplitz truncations.

This is the "easy" half of the statement that `U[t^{±1};τ]` carries an involution for which
`t^* = t^{-1}`; the content is that the twisting `MulSemiringAction (Multiplicative ℤ) U`
commutes with `star` (hypothesis `StarAction U`).
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs

namespace Work.ORHughesFree.NaturalExtension

section Basic

variable {U : Type} [Ring U] [StarRing U] [MulSemiringAction (Multiplicative ℤ) U]

/-- `starSkewL` is additive (it is a `Finsupp.sum` with additive values). -/
theorem starSkewL_add (p q : SkewMonoidAlgebra U (Multiplicative ℤ)) :
    starSkewL (p + q) = starSkewL p + starSkewL q := by
  simp only [starSkewL]
  exact SkewMonoidAlgebra.sum_add_index' (by simp) (by intro a b₁ b₂; simp [star_add, smul_add])

/-- `starSkewL` on a single basis element. -/
theorem starSkewL_single (m : Multiplicative ℤ) (a : U) :
    starSkewL (SkewMonoidAlgebra.single m a) = SkewMonoidAlgebra.single m⁻¹ (m⁻¹ • star a) := by
  simp only [starSkewL]
  rw [SkewMonoidAlgebra.sum_single_index (by simp)]

/-- `starSkewL` sends `0` to `0`. -/
theorem starSkewL_zero : starSkewL (0 : SkewMonoidAlgebra U (Multiplicative ℤ)) = 0 := by
  simp [starSkewL, SkewMonoidAlgebra.sum_def]

/-- `starSkewL` sends `1` to `1`. -/
theorem starSkewL_one : starSkewL (1 : SkewMonoidAlgebra U (Multiplicative ℤ)) = 1 := by
  rw [show (1 : SkewMonoidAlgebra U (Multiplicative ℤ)) = SkewMonoidAlgebra.single 1 1 from rfl,
    starSkewL_single]
  simp

/-- The coefficients of `starSkewL p`: `(starSkewL p)_g = g • star (p_{g⁻¹})`. -/
theorem starSkewL_coeff (p : SkewMonoidAlgebra U (Multiplicative ℤ)) (g : Multiplicative ℤ) :
    (starSkewL p).coeff g = g • star (p.coeff g⁻¹) := by
  induction p using SkewMonoidAlgebra.induction_on with
  | zero =>
      rw [starSkewL_zero, SkewMonoidAlgebra.coeff_zero]
      simp
  | single m a =>
      rw [starSkewL_single, SkewMonoidAlgebra.coeff_single_apply,
        SkewMonoidAlgebra.coeff_single_apply]
      by_cases h : m⁻¹ = g
      · subst h; simp
      · have h2 : ¬ (m = g⁻¹) := by rintro rfl; exact h (inv_inv g)
        simp [h, h2]
  | add p q ihp ihq =>
      simp only [starSkewL_add, SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, ihp, ihq,
        star_add, smul_add]

/-- The coefficients of `starSkewL p` in the `k`-th degree. -/
theorem starSkewL_coeffElt (p : SkewMonoidAlgebra U (Multiplicative ℤ)) (k : ℤ) :
    coeffElt (starSkewL p) k = (Multiplicative.ofAdd k) • star (coeffElt p (-k)) := by
  rw [coeffElt, starSkewL_coeff, coeffElt]
  congr 2

end Basic

section Star

variable {U : Type} [Ring U] [StarRing U] [MulSemiringAction (Multiplicative ℤ) U] [StarAction U]

/-- Antimultiplicativity, in the special case where the left factor is a single basis element.
Proved by induction on the right factor. -/
theorem starSkewL_single_mul (m : Multiplicative ℤ) (a : U)
    (q : SkewMonoidAlgebra U (Multiplicative ℤ)) :
    starSkewL (SkewMonoidAlgebra.single m a * q) =
      starSkewL q * starSkewL (SkewMonoidAlgebra.single m a) := by
  induction q using SkewMonoidAlgebra.induction_on with
  | zero => simp [starSkewL_zero]
  | single n b =>
      rw [SkewMonoidAlgebra.single_mul_single]
      simp only [starSkewL]
      rw [SkewMonoidAlgebra.sum_single_index (by simp), SkewMonoidAlgebra.sum_single_index (by simp),
        SkewMonoidAlgebra.sum_single_index (by simp)]
      rw [SkewMonoidAlgebra.single_mul_single, mul_inv_rev]
      congr 1
      rw [star_mul, StarAction.map_smul, smul_mul']
      rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
      rw [mul_smul]
  | add q₁ q₂ ih₁ ih₂ =>
      rw [mul_add, starSkewL_add, ih₁, ih₂, starSkewL_add, add_mul]

/-- `starSkewL` is antimultiplicative. -/
theorem starSkewL_mul (p q : SkewMonoidAlgebra U (Multiplicative ℤ)) :
    starSkewL (p * q) = starSkewL q * starSkewL p := by
  induction p using SkewMonoidAlgebra.induction_on with
  | zero => rw [zero_mul, starSkewL_zero, mul_zero]
  | single m a => exact starSkewL_single_mul m a q
  | add p₁ p₂ ih₁ ih₂ => rw [add_mul, starSkewL_add, ih₁, ih₂, starSkewL_add, mul_add]

/-- `starSkewL` is an involution. -/
theorem starSkewL_involutive (p : SkewMonoidAlgebra U (Multiplicative ℤ)) :
    starSkewL (starSkewL p) = p := by
  induction p using SkewMonoidAlgebra.induction_on with
  | zero => rw [starSkewL_zero, starSkewL_zero]
  | single m a =>
      rw [starSkewL_single, starSkewL_single]
      simp only [inv_inv]
      congr 1
      rw [StarAction.map_smul, star_star, ← mul_smul, mul_inv_cancel, one_smul]
  | add p₁ p₂ ih₁ ih₂ => rw [starSkewL_add, starSkewL_add, ih₁, ih₂]

/-- `starSkewL` is compatible with the matrix star on Toeplitz truncations. -/
theorem starSkewL_toeplitz (N : ℕ) (p : SkewMonoidAlgebra U (Multiplicative ℤ)) :
    toeplitz N (starSkewL p) = star (toeplitz N p) := by
  ext r s
  simp only [toeplitz, Matrix.star_apply]
  rw [starSkewL_coeffElt, StarAction.map_smul, ← mul_smul, ← ofAdd_add,
    show (((r : ℕ) : ℤ) + (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ))) = ((s : ℕ) : ℤ) from by ring,
    show -(((s : ℕ) : ℤ) - ((r : ℕ) : ℤ)) = ((r : ℕ) : ℤ) - ((s : ℕ) : ℤ) from by ring]

end Star

theorem starSkewLaurent {U : Type} [Ring U] [StarRing U] [MulSemiringAction (Multiplicative ℤ) U] [StarAction U] :
    (∀ p q : SkewMonoidAlgebra U (Multiplicative ℤ), starSkewL (p * q) = starSkewL q * starSkewL p) ∧
    (∀ p : SkewMonoidAlgebra U (Multiplicative ℤ), starSkewL (starSkewL p) = p) ∧
    (∀ p q : SkewMonoidAlgebra U (Multiplicative ℤ), starSkewL (p + q) = starSkewL p + starSkewL q) ∧
    starSkewL (1 : SkewMonoidAlgebra U (Multiplicative ℤ)) = 1 ∧
    (∀ (k : ℤ) (a : U), starSkewL (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) a) =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd k)⁻¹ ((Multiplicative.ofAdd k)⁻¹ • star a)) ∧
    (∀ (N : ℕ) (p : SkewMonoidAlgebra U (Multiplicative ℤ)), toeplitz N (starSkewL p) = star (toeplitz N p)) :=
  ⟨starSkewL_mul, starSkewL_involutive, starSkewL_add, starSkewL_one,
    fun _ _ => starSkewL_single _ _, starSkewL_toeplitz⟩

end Work.ORHughesFree.NaturalExtension
