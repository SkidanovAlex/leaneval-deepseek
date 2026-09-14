import Mathlib
import Submission.Commons.NumberTheory.Height.MahlerMeasure.rootMultiplicity_mul_logHeight_one
import Submission.Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_uniqueAlgEquiv

namespace Commons.NumberTheory.Height.MahlerMeasure

/-- Naturality of `MvPolynomial.uniqueAlgEquiv` with respect to base change `ℤ → ℚ`:
identifying a univariate `MvPolynomial` with a `Polynomial` commutes with the coefficient
extension. -/
lemma uniqueAlgEquiv_map_cast {P : MvPolynomial (Fin 1) ℤ} (m : ℕ) :
    ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) (P.map (Int.castRingHom ℚ))).coeff m =
      (((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)) P).coeff m : ℚ) := by
  rw [MvPolynomial.coeff_uniqueAlgEquiv, MvPolynomial.coeff_uniqueAlgEquiv,
    MvPolynomial.coeff_map]
  rfl

/-- **Root multiplicity and Mahler height in one variable.**

Let `P ∈ ℤ[X₁]` be nonzero and let `β ∈ ℚ` be a root of `P` viewed as a polynomial over `ℚ`.
Then `l · h(β) ≤ h_M(P)`, where `l` is the multiplicity of `β` and `h_M` is the logarithmic
height of the coefficient tuple `(1, coeffs)`. -/
theorem rootMultiplicity_mvFin1_mul_logHeight_one {P : MvPolynomial (Fin 1) ℤ} (hP : P ≠ 0)
    {β : ℚ}
    (hβ : (Polynomial.map (Int.castRingHom ℚ)
      (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1) P)).IsRoot β) :
    (Polynomial.rootMultiplicity β (Polynomial.map (Int.castRingHom ℚ)
        (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1) P)) : ℝ) * Height.logHeight₁ β ≤
      Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP
        (P.map (Int.castRingHom ℚ))) := by
  have hQ : MvPolynomial.uniqueAlgEquiv ℤ (Fin 1) P ≠ 0 := fun h =>
    hP ((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).injective (by rw [h, map_zero]))
  have hcoe : (fun o : Option ℕ => o.elim (1 : ℚ) (fun m =>
        ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) (P.map (Int.castRingHom ℚ))).coeff m)) =
      fun o : Option ℕ => o.elim (1 : ℚ) (fun m =>
        (((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)) P).coeff m : ℚ)) := by
    funext o
    cases o with
    | none => rfl
    | some m => simpa using uniqueAlgEquiv_map_cast (P := P) m
  rw [Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_uniqueAlgEquiv
    (P.map (Int.castRingHom ℚ)), hcoe]
  exact rootMultiplicity_mul_logHeight_one hQ hβ

end Commons.NumberTheory.Height.MahlerMeasure
