import Mathlib

namespace Work.Q44Geom

/-- A nonzero homogeneous polynomial of degree `0` over `ℚ` is a unit (it is a nonzero
constant).  Proof: `MvPolynomial.totalDegree_eq_zero_iff_eq_C` gives `P = C (P.coeff 0)` and
`MvPolynomial.isUnit_iff_eq_C_of_isReduced` finishes (the coefficient is nonzero as `P ≠ 0`). -/
theorem isUnit_of_isHomogeneous_zero {P : MvPolynomial (Fin 5) ℚ}
    (hP : P.IsHomogeneous 0) (hne : P ≠ 0) : IsUnit P := by
  have hdeg : P.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 5)).mpr hP
  have hC : P = MvPolynomial.C (P.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨P.coeff 0, isUnit_iff_ne_zero.mpr ?_, hC⟩
  intro h0
  exact hne (by rw [hC, h0, map_zero])

end Work.Q44Geom
