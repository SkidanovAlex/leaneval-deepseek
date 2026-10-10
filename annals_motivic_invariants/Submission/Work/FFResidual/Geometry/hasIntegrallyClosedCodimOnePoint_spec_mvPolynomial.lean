import Mathlib
import Submission.Work.FFResidual.Geometry.Reduction
import Submission.Work.FFResidual.Geometry.isDiscreteValuationRing_localization_AtPrime_of_span_singleton
import Submission.Work.FFResidual.Geometry.height_span_mvPolynomial_X

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.FFResidual.Geometry

open AlgebraicGeometry CategoryTheory

-- Please declare this in namespace `Work.FFResidual.Geometry`.
-- The witness is the prime `z := (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial (Fin (n+1)) 𝔽))`
-- of `Spec (MvPolynomial (Fin (n+1)) 𝔽)` (the generic point of the hyperplane `X 0 = 0`).
-- `Order.coheight z = 1` comes from `AlgebraicGeometry.idealHeight_eq_coheight` and
-- `Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors` (prove the height inline; a sibling
-- lemma `Work.FFResidual.Geometry.height_span_mvPolynomial_X` may or may not be available).
-- `IsIntegrallyClosed (X.presheaf.stalk z)`: the stalk is a localization of `A := MvPolynomial (Fin (n+1)) 𝔽`
-- at `z.asIdeal` (`IsLocalization.AtPrime (X.presheaf.stalk z) z.asIdeal`), while
-- `Localization.AtPrime z.asIdeal` is a discrete valuation ring
-- (`Work.FFResidual.Geometry.isDiscreteValuationRing_localization_AtPrime_of_span_singleton`); a DVR is
-- integrally closed (`IsDiscreteValuationRing.TFAE`, item 0 ⇒ item 3, indices 1-based), and
-- `IsIntegrallyClosed` transfers across the ring isomorphism between the two localizations
-- (`IsLocalization.algEquiv`; `IsIntegrallyClosed` unfolds to `IsIntegrallyClosedIn R (FractionRing R)`,
-- so `isIntegrallyClosed_iff`/`IsIntegrallyClosedIn`-transport is the way).
theorem hasIntegrallyClosedCodimOnePoint_spec_mvPolynomial (𝔽 : Type) [Field 𝔽] (n : ℕ) :
    Work.FFResidual.HasIntegrallyClosedCodimOnePoint
      (AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) 𝔽))) := by
  -- The polynomial ring `A = 𝔽[X₀,…,Xₙ]` and the height-one prime `p = (X₀)`.
  let A := MvPolynomial (Fin (n+1)) 𝔽
  let p : Ideal A := Ideal.span {MvPolynomial.X (0 : Fin (n+1))}
  have hx : (MvPolynomial.X (0 : Fin (n+1)) : A) ≠ 0 := MvPolynomial.X_ne_zero _
  have hp : p.IsPrime := (Ideal.span_singleton_prime hx).mpr (MvPolynomial.X_prime (R := 𝔽))
  letI : p.IsPrime := hp
  -- The witness: the generic point of the hyperplane `X₀ = 0`.
  refine ⟨(⟨p, hp⟩ : PrimeSpectrum A), ?_, ?_⟩
  · -- `coheight z = 1` since the height of `z.asIdeal = (X₀)` is one.
    rw [← AlgebraicGeometry.idealHeight_eq_coheight (CommRingCat.of A)
      (⟨p, hp⟩ : PrimeSpectrum A)]
    haveI : IsNoetherianRing A := MvPolynomial.isNoetherianRing
    have hprime : Prime (MvPolynomial.X (0 : Fin (n+1)) : A) := MvPolynomial.X_prime
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hprime.ne_zero)
      (fun hunit => hprime.not_isUnit hunit)
  · -- `IsIntegrallyClosed` of the stalk, transported along the canonical isomorphism with the
    -- local ring `Localization.AtPrime (X₀)`, which is a discrete valuation ring.
    haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime p) :=
      isDiscreteValuationRing_localization_AtPrime_of_span_singleton hx
    -- A discrete valuation ring is integrally closed (`IsDiscreteValuationRing.TFAE`, `0 ⇒ 3`).
    have hconj : IsIntegrallyClosed (Localization.AtPrime p) ∧
        ∃! P : Ideal (Localization.AtPrime p), P ≠ ⊥ ∧ P.IsPrime :=
      ((IsDiscreteValuationRing.TFAE (Localization.AtPrime p)
        (IsDiscreteValuationRing.not_isField (Localization.AtPrime p))).out 1 4).mp hDVR
    haveI hIC : IsIntegrallyClosed (Localization.AtPrime p) := hconj.1
    refine IsIntegrallyClosed.of_equiv (h := hIC) ?_
    exact (Iso.commRingCatIsoToRingEquiv
      (Spec.stalkIso (CommRingCat.of A) (⟨p, hp⟩ : PrimeSpectrum A))).symm

end Work.FFResidual.Geometry
