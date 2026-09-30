import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Complex conjugation permutes the complex roots (with multiplicity) of a polynomial
with integer coefficients: if `z` is a root of `P` then so is `conj z`, and conversely. -/
theorem roots_map_conj_eq (P : Polynomial ℤ) :
    ((P.map (Int.castRingHom ℂ)).roots).map (starRingEnd ℂ)
      = (P.map (Int.castRingHom ℂ)).roots := by
  -- Conjugation fixes the integer cast, so conjugating the complexified polynomial
  -- gives back the same polynomial.
  have hcomp : (starRingEnd ℂ : ℂ →+* ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ := by
    ext n
    simp
  -- Over the algebraically closed field `ℂ` the polynomial splits, so `roots_map`
  -- computes the roots of the conjugated polynomial as the conjugated roots.
  have hsplit := IsAlgClosed.splits (P.map (Int.castRingHom ℂ))
  rw [← hsplit.roots_map (starRingEnd ℂ : ℂ →+* ℂ), Polynomial.map_map, hcomp]

end Work.BW
