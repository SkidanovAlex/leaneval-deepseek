import Mathlib
import Submission.Work.WilE4.CAD.Proj

namespace Work.WilE4.CAD

/-- The resultant commutes with the specialisation `x ↦ eval x`: this is the general
compatibility of `Polynomial.resultant` with a ring homomorphism, read through the defining
identity `spec P x = (F P).map (eval x)`. -/
theorem resultant_spec {m : ℕ} (P Q : MvPolynomial (Fin (m + 1)) ℝ) (x : Fin m → ℝ) (a b : ℕ) :
    MvPolynomial.eval x (Polynomial.resultant (CAD.F P) (CAD.F Q) a b)
      = Polynomial.resultant (spec P x) (spec Q x) a b := by
  simp only [spec_eq_map]
  exact (Polynomial.resultant_map_map (f := CAD.F P) (g := CAD.F Q) (m := a) (n := b)
    (MvPolynomial.eval x)).symm

end Work.WilE4.CAD
