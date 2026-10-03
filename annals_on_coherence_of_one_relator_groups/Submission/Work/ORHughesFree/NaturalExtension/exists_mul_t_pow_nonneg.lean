import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs

namespace Work.ORHughesFree.NaturalExtension

universe u

section PowT

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- Normal form for the powers of the variable `t` of `R[t^{±1};τ]`: `t ^ k = single (ofAdd k) 1`. -/
theorem skewLaurentT_pow_eq_single (k : ℕ) :
    (skewLaurentT (R := R)) ^ k = SkewMonoidAlgebra.single (Multiplicative.ofAdd (k : ℤ)) 1 := by
  rw [skewLaurentT]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, SkewMonoidAlgebra.single_mul_single, ← ofAdd_add]
    simp

/-- Multiplying on the right by `t ^ k` shifts the coefficients by `k`:
the coefficient of `t ^ l` in `a * t ^ k` is the coefficient of `t ^ (l - k)` in `a`. -/
theorem coeffElt_mul_t_pow (a : SkewL R) (k : ℕ) (l : ℤ) :
    coeffElt (a * (skewLaurentT : SkewL R) ^ k) l = coeffElt a (l - (k : ℤ)) := by
  have h1 : (Multiplicative.ofAdd l : Multiplicative ℤ) * (Multiplicative.ofAdd (k : ℤ))⁻¹
      = Multiplicative.ofAdd (l - (k : ℤ)) := by
    rw [← ofAdd_neg, ← ofAdd_add, sub_eq_add_neg]
  rw [skewLaurentT_pow_eq_single k, coeffElt,
    SkewMonoidAlgebra.coeff_mul_single, h1,
    MulSemiringAction.smul_one, mul_one]
  rfl

end PowT

/-- For any matrix `A` over `R[t^{±1};τ]` there is an exponent `k` such that, after multiplying
every column on the right by `t ^ k`, all coefficients of the resulting matrix have non-negative
degree.  Explicitly, `k = lowerDeg A` works: the coefficient of `t ^ l` with `l < 0` in the
`(i,j)` entry becomes the coefficient of `t ^ (l - k)` of `A i j`, which vanishes because
`l - k < -k = -lowerDeg A`. -/
theorem exists_mul_t_pow_nonneg {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL R)) : ∃ k : ℕ, ∀ i j, ∀ l : ℤ, l < 0 → coeffElt ((A * Matrix.diagonal (fun _ : Fin m => (skewLaurentT : SkewL R) ^ k)) i j) l = 0 := by
  refine ⟨lowerDeg A, ?_⟩
  intro i j l hl
  rw [Matrix.mul_diagonal, coeffElt_mul_t_pow]
  exact coeffElt_eq_zero_of_lt_lowerDeg A i j (by omega)

end Work.ORHughesFree.NaturalExtension
