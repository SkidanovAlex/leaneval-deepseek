import Mathlib.Analysis.Polynomial.Norm

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial

/-- The sup norm of a polynomial is invariant under multiplication by a scalar `C a`,
up to the factor `‖a‖`. -/
lemma supNorm_C_mul {A : Type*} [NormedField A] (a : A) (Q : A[X]) :
    (Polynomial.C a * Q).supNorm = ‖a‖ * Q.supNorm := by
  apply le_antisymm
  · rcases (Polynomial.C a * Q).exists_eq_supNorm with ⟨i, hi⟩
    rw [hi, Polynomial.coeff_C_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (Polynomial.le_supNorm Q i) (norm_nonneg a)
  · rcases Q.exists_eq_supNorm with ⟨i, hi⟩
    calc
      ‖a‖ * Q.supNorm = ‖a‖ * ‖Q.coeff i‖ := by rw [hi]
      _ = ‖a * Q.coeff i‖ := by rw [norm_mul]
      _ = ‖(Polynomial.C a * Q).coeff i‖ := by rw [Polynomial.coeff_C_mul]
      _ ≤ (Polynomial.C a * Q).supNorm := Polynomial.le_supNorm _ i

theorem int_poly_supNorm_C_mul (c : ℤ) (P : Polynomial ℤ) :
    ((Polynomial.C c * P).map (Int.castRingHom ℝ)).supNorm =
      ‖(c : ℝ)‖ * ((P.map (Int.castRingHom ℝ)).supNorm) := by
  rw [Polynomial.map_mul, Polynomial.map_C]
  exact supNorm_C_mul (c : ℝ) (P.map (Int.castRingHom ℝ))

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree