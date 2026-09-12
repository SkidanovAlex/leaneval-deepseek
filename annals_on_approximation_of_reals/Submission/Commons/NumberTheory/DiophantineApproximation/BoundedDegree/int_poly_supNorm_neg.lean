import Mathlib.Analysis.Polynomial.Norm

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial

/-- The sup norm of a polynomial is invariant under negation of the polynomial. -/
lemma supNorm_neg {A : Type*} [SeminormedRing A] (p : Polynomial A) :
    (-p).supNorm = p.supNorm := by
  apply le_antisymm
  · rcases (-p).exists_eq_supNorm with ⟨i, hi⟩
    rw [hi]
    calc
      ‖(-p).coeff i‖ = ‖p.coeff i‖ := by rw [Polynomial.coeff_neg, norm_neg]
      _ ≤ p.supNorm := Polynomial.le_supNorm p i
  · rcases p.exists_eq_supNorm with ⟨i, hi⟩
    rw [hi]
    calc
      ‖p.coeff i‖ = ‖(-p).coeff i‖ := by
        rw [← norm_neg (p.coeff i), Polynomial.coeff_neg]
      _ ≤ (-p).supNorm := Polynomial.le_supNorm (-p) i

theorem int_poly_supNorm_neg (P : Polynomial ℤ) :
    ((-P).map (Int.castRingHom ℝ)).supNorm = (P.map (Int.castRingHom ℝ)).supNorm := by
  rw [Polynomial.map_neg]
  exact supNorm_neg (P.map (Int.castRingHom ℝ))

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree
