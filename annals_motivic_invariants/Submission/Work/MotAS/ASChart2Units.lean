import Mathlib
import Submission.Work.MotAS.ASChart2Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASChart2Units` — the unit bookkeeping of the corrected AS chart

The two divisors of the corrected AS chart are

* `FdivAS2 a b g = GambAS2 a b g * fwVecAS2 a b g 0`   (source),
* `GdivAS2 a b g = FambAS2 a b g * bwVecAS2 a b g 4`   (target),

with `GambAS2 = linAS2 · sAS2` and `FambAS2 = cubAS2 · sdualAS2`.  This file collects the
*definitional* unit facts (no value lemma needed): the four factors
`linAS2, sAS2` (on the source side) and `cubAS2, sdualAS2` (on the target side), the two chart
denominators `fwVecAS2 · 0`, `bwVecAS2 · 4`, the two inverses `invG4AS2`, `invF0AS2`, and the two
factorisations of the divisors.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K]

/-- The two divisors, as products of the equation and of the chart denominator. -/
theorem FdivAS2_eq (a b g : K) : FdivAS2 a b g = GambAS2 a b g * fwVecAS2 a b g 0 := rfl

theorem GdivAS2_eq (a b g : K) : GdivAS2 a b g = FambAS2 a b g * bwVecAS2 a b g 4 := rfl

theorem GambAS2_eq' (a b g : K) : GambAS2 a b g = linAS2 a b * sAS2 a b g := rfl

theorem FambAS2_eq' (a b g : K) : FambAS2 a b g = cubAS2 a b g * sdualAS2 a b g := rfl

/-- `FambAS2` is a unit of `A[1/GdivAS2]`. -/
theorem isUnit_alg_FambAS2 (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
      (FambAS2 a b g)) :=
  IsLocalization.Away.isUnit_of_dvd (GdivAS2 a b g)
    ⟨bwVecAS2 a b g 4, rfl⟩

/-- `GambAS2` is a unit of `A[1/FdivAS2]`. -/
theorem isUnit_alg_GambAS2 (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
      (GambAS2 a b g)) :=
  IsLocalization.Away.isUnit_of_dvd (FdivAS2 a b g)
    ⟨fwVecAS2 a b g 0, rfl⟩

/-- `cubAS2` is a unit of `A[1/GdivAS2]`. -/
theorem isUnit_alg_cubAS2 (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
      (cubAS2 a b g)) :=
  IsLocalization.Away.isUnit_of_dvd (GdivAS2 a b g)
    ⟨sdualAS2 a b g * bwVecAS2 a b g 4, by rw [GdivAS2_eq, FambAS2_eq']; ring⟩

/-- `sdualAS2` is a unit of `A[1/GdivAS2]`. -/
theorem isUnit_alg_sdualAS2 (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
      (sdualAS2 a b g)) :=
  IsLocalization.Away.isUnit_of_dvd (GdivAS2 a b g)
    ⟨cubAS2 a b g * bwVecAS2 a b g 4, by
      rw [GdivAS2_eq, FambAS2_eq']; ring⟩

/-- `bwVecAS2 · 4` is a unit of `A[1/GdivAS2]`. -/
theorem isUnit_alg_bwVecAS2_four (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
      (bwVecAS2 a b g 4)) :=
  IsLocalization.Away.isUnit_of_dvd (GdivAS2 a b g)
    ⟨FambAS2 a b g, by rw [GdivAS2_eq]; ring⟩

/-- `linAS2` is a unit of `A[1/FdivAS2]`. -/
theorem isUnit_alg_linAS2 (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
      (linAS2 a b)) :=
  IsLocalization.Away.isUnit_of_dvd (FdivAS2 a b g)
    ⟨sAS2 a b g * fwVecAS2 a b g 0, by rw [FdivAS2_eq, GambAS2_eq']; ring⟩

/-- `sAS2` is a unit of `A[1/FdivAS2]`. -/
theorem isUnit_alg_sAS2 (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
      (sAS2 a b g)) :=
  IsLocalization.Away.isUnit_of_dvd (FdivAS2 a b g)
    ⟨linAS2 a b * fwVecAS2 a b g 0, by
      rw [FdivAS2_eq, GambAS2_eq']; ring⟩

/-- `fwVecAS2 · 0` is a unit of `A[1/FdivAS2]`. -/
theorem isUnit_alg_fwVecAS2_zero (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
      (fwVecAS2 a b g 0)) :=
  IsLocalization.Away.isUnit_of_dvd (FdivAS2 a b g)
    ⟨GambAS2 a b g, by rw [FdivAS2_eq, mul_comm]⟩

/-- `1/ǧ₄` is a unit of `A[1/GdivAS2]`. -/
theorem isUnit_invG4AS2 (a b g : K) : IsUnit (invG4AS2 a b g) :=
  isUnit_of_dvd_unit ⟨algebraMap _ _ (GdivAS2 a b g), (invG4AS2_spec a b g).symm⟩
    (isUnit_alg_FambAS2 a b g)

/-- `1/f̂₀` is a unit of `A[1/FdivAS2]`. -/
theorem isUnit_invF0AS2 (a b g : K) : IsUnit (invF0AS2 a b g) :=
  isUnit_of_dvd_unit ⟨algebraMap _ _ (FdivAS2 a b g), (invF0AS2_spec a b g).symm⟩
    (isUnit_alg_GambAS2 a b g)

/-- `Phi0AS2` commutes with the source factorisation of `FdivAS2`. -/
theorem Phi0AS2_FdivAS2 (a b g : K) :
    Phi0AS2 a b g (FdivAS2 a b g)
      = Phi0AS2 a b g (GambAS2 a b g) * Phi0AS2 a b g (fwVecAS2 a b g 0) := by
  rw [FdivAS2_eq, map_mul]

/-- `Psi0AS2` commutes with the target factorisation of `GdivAS2`. -/
theorem Psi0AS2_GdivAS2 (a b g : K) :
    Psi0AS2 a b g (GdivAS2 a b g)
      = Psi0AS2 a b g (FambAS2 a b g) * Psi0AS2 a b g (bwVecAS2 a b g 4) := by
  rw [GdivAS2_eq, map_mul]

end Work.MotAS
