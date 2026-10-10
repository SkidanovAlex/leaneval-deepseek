import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

/-!
# `F` is relatively algebraically closed in the fraction field of `F[x₁,…,x_m]`

`Work.MotV.isAlgebraic_mem_base`: an element of the fraction field
`Frac F[x₁,…,x_m] = FractionRing (MvPolynomial (Fin m) F)` which is algebraic over `F`
(embedded in the constants) is already a constant.

Route.  Since `F` is a field, algebraic over `F` means *integral* over `F`
(`IsAlgebraic.isIntegral`), hence integral over `R := MvPolynomial (Fin m) F`
(`IsIntegral.tower_top`).  A polynomial ring over a field is a GCD domain, hence integrally
closed in its fraction field, so `a = algebraMap R K y` for some `y : R`
(`IsIntegrallyClosed.isIntegral_iff`).  Transporting integrality back along the injective
structure map gives that `y` is integral over `F`; then the crux, `isIntegral_eq_C`: a nonzero
element of `R` integral over the field `F` is a unit of `R` (`IsIntegral.isUnit` — `F[y]` is a
finite-dimensional domain over `F`, hence a field), and the units of a multivariate polynomial
ring over a reduced ring are exactly the nonzero constants
(`MvPolynomial.isUnit_iff_eq_C_of_isReduced`).  Hence `y = C c` and `a` is that constant.
-/

namespace Work.MotV

/-- **The crux.**  An element of `MvPolynomial (Fin m) F`, over a field `F`, which is integral
over `F` is a constant: `F` is relatively algebraically closed in `F[x₁,…,x_m]`.

A nonzero element `y` integral over the field `F` satisfies `[F[y] : F] < ∞`, and `F[y]` is a
domain (a subring of the polynomial ring), hence a field; so `y` is a unit of `R`
(`IsIntegral.isUnit`).  By `MvPolynomial.isUnit_iff_eq_C_of_isReduced` the units of `R` are the
constants `C r` with `r` a unit of `F`. -/
theorem isIntegral_eq_C {F : Type} [Field F] (m : ℕ)
    (y : MvPolynomial (Fin m) F) (h : IsIntegral F y) :
    ∃ c : F, y = MvPolynomial.C c := by
  rcases eq_or_ne y 0 with h0 | h0
  · exact ⟨0, by rw [h0, map_zero]⟩
  · obtain ⟨c, -, hc⟩ :=
      (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := y)).mp (h.isUnit h0)
    exact ⟨c, hc⟩

theorem isAlgebraic_mem_base {F : Type} [Field F] (m : ℕ)
    (a : FractionRing (MvPolynomial (Fin m) F)) (ha : IsAlgebraic F a) :
    ∃ c : F, a = algebraMap F (FractionRing (MvPolynomial (Fin m) F)) c := by
  -- A field is integrally closed in itself, so `algebraic = integral` over `F`.
  have hint : IsIntegral F a := ha.isIntegral
  -- Integrality is preserved under the tower `F → R → Frac R`.
  have hintR : IsIntegral (MvPolynomial (Fin m) F) a := hint.tower_top
  -- `R = MvPolynomial (Fin m) F` is a GCD domain, hence integrally closed in its fraction field.
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := MvPolynomial (Fin m) F)).mp hintR
  -- `hy : algebraMap R K y = a`.
  -- Integrality descends back to `y` along the injective structure map `R → K`.
  have hyint : IsIntegral F y := by
    have h1 : IsIntegral F ((IsScalarTower.toAlgHom F (MvPolynomial (Fin m) F)
        (FractionRing (MvPolynomial (Fin m) F))) y) := hy ▸ hint
    exact (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom F (MvPolynomial (Fin m) F) (FractionRing (MvPolynomial (Fin m) F)))
      (IsFractionRing.injective (MvPolynomial (Fin m) F)
        (FractionRing (MvPolynomial (Fin m) F)))).mp h1
  obtain ⟨c, hc⟩ := isIntegral_eq_C m y hyint
  refine ⟨c, ?_⟩
  rw [← hy, hc, ← MvPolynomial.algebraMap_eq,
    IsScalarTower.algebraMap_apply F (MvPolynomial (Fin m) F)
      (FractionRing (MvPolynomial (Fin m) F))]

end Work.MotV
