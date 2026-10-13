import Mathlib
import Submission.Work.DSSER.Basic

universe u

namespace Work.DSSER

/-- `R' = R[Z]/(Z_i^p - z_i)` is a finite `R`-module (for `p > 0`): every variable is integral over `R`
(`Z_i^p = z_i`).
Suggested route: `Algebra.IsIntegral.finite` (`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`),
i.e. `Algebra.FiniteType R R'` (surjectivity of the quotient map plus `Algebra.FiniteType.of_surjective`
and the `MvPolynomial` finite-type instance) and `Algebra.IsIntegral R R'` (`integralClosure_eq_top_iff`;
the generators `serZ p z i` are integral by `IsIntegral.of_pow` with `Basic.serZ_pow`, then
`Algebra.IsIntegral.adjoin` and `isIntegral_algebraMap_iff`).  Alternatively prove that the `R`-span of
the images of the monomials `X^a`, `a : Fin d → Fin p`, is `⊤` (use `Basic.serZpow_div_mod` to reduce an
arbitrary monomial). -/
theorem moduleFinite_serRing (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p) {d : ℕ} (z : Fin d → R) :
    Module.Finite R (Work.DSSER.serRing R p z) := by
  -- The quotient map `MvPolynomial (Fin d) R → R'`.
  let q : MvPolynomial (Fin d) R →ₐ[R] serRing R p z := Ideal.Quotient.mkₐ R (serRel R p z)
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R (serRel R p z)
  -- The variables `Z i` generate `R'` as an `R`-algebra.
  have hgen : Algebra.adjoin R (Set.range (serZ p z)) = ⊤ := by
    have hX : Algebra.adjoin R (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)) = ⊤ :=
      MvPolynomial.adjoin_range_X
    have hcomp : (serZ p z : Fin d → serRing R p z) =
        q ∘ (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R) := by
      funext i; rfl
    rw [hcomp, Set.range_comp,
      ← AlgHom.map_adjoin q (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)),
      hX, Algebra.map_top]
    exact (AlgHom.range_eq_top q).mpr hq
  -- Each generator `Z i` is integral over `R`, since `Z i ^ p = z i`.
  have hInt : Algebra.IsIntegral R (serRing R p z) := by
    rw [← integralClosure_eq_top_iff]
    refine eq_top_iff.mpr ?_
    rw [← hgen]
    refine Algebra.adjoin_le_iff.mpr ?_
    rintro x ⟨i, rfl⟩
    exact IsIntegral.of_pow hp (by rw [serZ_pow i]; exact isIntegral_algebraMap)
  -- Integral + finite type ⟹ finite as a module.
  exact @Algebra.IsIntegral.finite R (serRing R p z) _ _ _ hInt _

end Work.DSSER
