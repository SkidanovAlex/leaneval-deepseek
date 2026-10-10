import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FFResidual.Eisenstein

/-- **The Eisenstein extension of a discrete valuation ring is a domain.**
Let `R` be a discrete valuation ring and let `f ∈ R[X]` be monic of positive degree, Eisenstein at
the maximal ideal.  Then `R[X]/(f)` is a domain (the Eisenstein criterion, transported over the
fraction field of `R`). -/
theorem isDomain_adjoinRoot_of_isEisensteinAt {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {f : Polynomial R} (hmon : f.Monic) (hdeg : 0 < f.natDegree)
    (heis : Polynomial.IsEisensteinAt f (IsLocalRing.maximalIdeal R)) :
    IsDomain (AdjoinRoot f) := by
  -- The maximal ideal of a discrete valuation ring is prime.
  have hprime : (IsLocalRing.maximalIdeal R).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  -- The Eisenstein criterion: a monic Eisenstein polynomial is irreducible over `R`.
  have hirr : Irreducible f := heis.irreducible hprime hmon.isPrimitive hdeg
  -- A discrete valuation ring is a principal ideal ring, hence a unique factorization domain,
  -- and so is `R[X]`; in a unique factorization domain irreducible elements are prime.
  have hufd : UniqueFactorizationMonoid (Polynomial R) := inferInstance
  exact AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)

end Work.FFResidual.Eisenstein
