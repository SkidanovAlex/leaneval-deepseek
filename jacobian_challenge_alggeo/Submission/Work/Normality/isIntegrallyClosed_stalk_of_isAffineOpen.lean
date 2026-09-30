import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

set_option linter.style.haveILetI false

namespace Work.Normality

/-- Let `U ⊆ X` be an affine open subscheme whose ring of sections is a domain and is
integrally closed.  Then the local ring of `X` at every point of `U` is integrally closed.

Proof sketch: for `x : X` with `hx : x ∈ U` the stalk `X.presheaf.stalk x` is the localisation
of `Γ(X, U) = X.presheaf.obj (Opposite.op U)` at the prime ideal `hU.primeIdealOf ⟨x, hx⟩`
(Mathlib: `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), so
`isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl`
applies — its elements are non-zero, hence non-zero-divisors, in the domain `Γ(X, U)`. -/
theorem isIntegrallyClosed_stalk_of_isAffineOpen {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U)
    [IsDomain (X.presheaf.obj (Opposite.op U))]
    (h : IsIntegrallyClosed (X.presheaf.obj (Opposite.op U))) {x : X} (hx : x ∈ U) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  -- The stalk at `x` is the localisation of the section ring at the prime ideal
  -- `hU.primeIdealOf ⟨x, hx⟩`; we package the point as an element of the subtype `U` so that the
  -- canonical `Algebra Γ(X, U) (X.presheaf.stalk _)` instance is found by instance search.
  let x' : U := ⟨x, hx⟩
  letI : Algebra (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk x'.1) :=
    X.presheaf.algebra_section_stalk x'
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x'.1) (hU.primeIdealOf x').asIdeal :=
    hU.isLocalization_stalk x'
  -- A localisation of an integrally closed domain at a submonoid of non-zero-divisors is
  -- integrally closed; here the submonoid is the complement of a prime ideal, whose elements
  -- are non-zero and hence non-zero-divisors in the domain `Γ(X, U)`.
  refine isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x'.1)
    (hU.primeIdealOf x').asIdeal.primeCompl ?_
  intro a ha
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h0
  exact ha (h0 ▸ (hU.primeIdealOf x').asIdeal.zero_mem)

end Work.Normality
