import Mathlib

namespace Work.Q44Geom

open MvPolynomial in
/-- The product of a list of homogeneous polynomials is homogeneous, of degree the sum of the degrees. -/
theorem list_prod_isHomogeneous {σ : Type*} {R : Type*} [CommSemiring R]
    (l : List (MvPolynomial σ R)) (n : MvPolynomial σ R → ℕ)
    (h : ∀ p ∈ l, p.IsHomogeneous (n p)) :
    l.prod.IsHomogeneous (l.map n).sum := by
  induction l with
  | nil => simpa using (MvPolynomial.isHomogeneous_one (σ := σ) (R := R))
  | cons p t ih =>
      simp only [List.prod_cons, List.map_cons, List.sum_cons]
      exact (h p (by simp)).mul (ih (fun q hq => h q (by simp [hq])))

end Work.Q44Geom
