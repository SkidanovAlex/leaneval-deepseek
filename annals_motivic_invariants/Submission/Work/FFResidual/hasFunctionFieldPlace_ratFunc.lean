import Mathlib
import Submission.Work.FFResidual.Defs

set_option linter.unusedVariables false -- v435-speed

namespace Work.FFResidual

set_option linter.style.haveILetI false

/-- **The rational function field `𝔽(t)` has a place over `𝔽`**: the localization `𝔽[t]_(t)` of
`𝔽[t]` at the prime `(t)` is a discrete valuation ring with fraction field `𝔽(t)` containing the
constants, with uniformizer `t` — this is the hypothesis `FunctionFieldPlace 𝔽 𝕜` of the area at
`𝕜 = 𝔽(t)`, and it shows that the sub-residual `HasFunctionFieldPlace 𝔽 𝕜` is not vacuous (and
hence that the residual `FunctionFieldResidual 𝔽 (RatFunc 𝔽)` follows from the local theory of
`Submission/Work/FFResidual/Kummer`, independently of the `ConstantsOnly` route of
`Work.ClassBCD.RatFunc`). -/
theorem hasFunctionFieldPlace_ratFunc (𝔽 : Type) [Field 𝔽] :
    Work.FFResidual.HasFunctionFieldPlace 𝔽 (RatFunc 𝔽) := by
  -- The origin of the affine line: the prime ideal `(X)` of `𝔽[X]`.
  let p : Ideal (Polynomial 𝔽) := Ideal.span {Polynomial.X}
  have hp : p.IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  letI : p.IsPrime := hp
  -- The local ring of `𝔸¹` at the origin is a discrete valuation ring...
  let R := Localization.AtPrime p
  have hne : p ≠ ⊥ := by
    show Ideal.span {Polynomial.X} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_ne_zero
  have hdv : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial 𝔽) hne R
  haveI : IsDiscreteValuationRing R := hdv
  -- ... whose residue/valuation structure is fed by the structure map `𝔽 → R → 𝔽(t)`.
  -- The constants map into `R` through `𝔽[X]`, so that the tower `𝔽 → R → 𝔽(t)` is the
  -- tower `𝔽 → 𝔽[X] → 𝔽(t)`.
  letI hAlgF : Algebra 𝔽 R :=
    RingHom.toAlgebra ((algebraMap (Polynomial 𝔽) R).comp (algebraMap 𝔽 (Polynomial 𝔽)))
  -- The map `R → 𝔽(t)` is the composite of the canonical map `R → 𝔽(X)` to the fraction field of
  -- `𝔽[X]` with the canonical identification `𝔽(X) ≃+* 𝔽(t)` (`RatFunc 𝔽` is a one-field wrapper
  -- around `FractionRing 𝔽[X]`).
  letI hAlgR : Algebra R (RatFunc 𝔽) :=
    RingHom.toAlgebra
      (((RatFunc.toFractionRingRingEquiv 𝔽).symm : FractionRing (Polynomial 𝔽) →+* RatFunc 𝔽).comp
        (algebraMap R (FractionRing (Polynomial 𝔽))))
  -- `𝔽[X] → R → 𝔽(t)` is the tower of algebras, by construction of the two algebra structures.
  haveI htow1 : @IsScalarTower (Polynomial 𝔽) R (RatFunc 𝔽)
      (Algebra.toSMul) (Algebra.toSMul) (Algebra.toSMul) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap (Polynomial 𝔽) (RatFunc 𝔽) x =
      (RatFunc.toFractionRingRingEquiv 𝔽).symm
        (algebraMap R (FractionRing (Polynomial 𝔽)) (algebraMap (Polynomial 𝔽) R x))
    rw [← IsScalarTower.algebraMap_apply (Polynomial 𝔽) R (FractionRing (Polynomial 𝔽)) x]
    exact (RatFunc.ofFractionRing_algebraMap x).symm
  -- `R` is a localization of `𝔽[X]` at a nonzero prime, hence its fraction field is `𝔽(t)`
  -- (the constants are integral at the place, as the structure map factors through `𝔽[X]`).
  haveI hfr : IsFractionRing R (RatFunc 𝔽) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl R (RatFunc 𝔽)
  -- Consequently `𝔽 → R → 𝔽(t)` is a tower of algebras as well.
  haveI htow2 : @IsScalarTower 𝔽 R (RatFunc 𝔽)
      (Algebra.toSMul) (Algebra.toSMul) (Algebra.toSMul) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    calc algebraMap 𝔽 (RatFunc 𝔽) x
        = algebraMap (Polynomial 𝔽) (RatFunc 𝔽) (algebraMap 𝔽 (Polynomial 𝔽) x) :=
            IsScalarTower.algebraMap_apply 𝔽 (Polynomial 𝔽) (RatFunc 𝔽) x
      _ = algebraMap R (RatFunc 𝔽)
            (algebraMap (Polynomial 𝔽) R (algebraMap 𝔽 (Polynomial 𝔽) x)) :=
            IsScalarTower.algebraMap_apply (Polynomial 𝔽) R (RatFunc 𝔽) _
      _ = algebraMap R (RatFunc 𝔽) (algebraMap 𝔽 R x) := rfl
  -- Finally, `t = X` generates the maximal ideal of the local ring of the origin.
  let P : FunctionFieldPlace 𝔽 (RatFunc 𝔽) :=
    { R := R, π := algebraMap (Polynomial 𝔽) R Polynomial.X,
      isUniformizer := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_span,
          Set.image_singleton] }
  exact ⟨P⟩

end Work.FFResidual
