import Mathlib
import Mathlib.Algebra.MvPolynomial.Nilpotent

set_option autoImplicit false

namespace Work.Q44Geom

open MvPolynomial in
/-- A unit of a multivariate polynomial ring over a reduced commutative ring is homogeneous of degree `0` (it is a nonzero constant). -/
theorem isHomogeneous_of_isUnit {σ : Type*} {R : Type*} [CommRing R] [IsReduced R]
    {u : MvPolynomial σ R} (hu : IsUnit u) : u.IsHomogeneous 0 := by
  obtain ⟨r, _, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hu
  exact MvPolynomial.isHomogeneous_C σ r

end Work.Q44Geom
