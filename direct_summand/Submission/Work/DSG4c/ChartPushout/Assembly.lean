import Submission.Work.DSG4c.ChartPushout.DefsT

/-!
# Chart pushout (area DSG4c): assembly

The `MvPolynomial` pushout square (base change of the dehomogenized polynomial ring) and the
coherence of the dehomogenization isomorphisms with coefficient extension.
-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open Work.DSG4c.ChartPushout

namespace Work.DSG4c.ChartPushout

universe u

/-- The pushout square of polynomial rings cut out by the charts: base change of
`A[x_j : j ≠ i]` along `A → A'`. -/
theorem isPushout_poly (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A') (N : ℕ)
    (i : Fin (N+1)) :
    IsPushout (CommRingCat.ofHom ψ)
      (CommRingCat.ofHom (MvPolynomial.C : A →+* MvPolynomial (chartIdx N i) A))
      (CommRingCat.ofHom (MvPolynomial.C : A' →+* MvPolynomial (chartIdx N i) A'))
      (CommRingCat.ofHom (MvPolynomial.map ψ)) := by
  letI : Algebra A A' := ψ.toAlgebra
  letI : Algebra (MvPolynomial (chartIdx N i) A) (MvPolynomial (chartIdx N i) A') :=
    MvPolynomial.algebraMvPolynomial
  haveI : Algebra.IsPushout A A' (MvPolynomial (chartIdx N i) A)
      (MvPolynomial (chartIdx N i) A') := MvPolynomial.instIsPushout
  simpa using CommRingCat.isPushout_of_isPushout A A'
    (MvPolynomial (chartIdx N i) A) (MvPolynomial (chartIdx N i) A')

end Work.DSG4c.ChartPushout
