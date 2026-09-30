import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Sections of a normal scheme over an affine open

If `X` is an integral scheme all of whose local rings (stalks) are integrally closed, and
`U ⊆ X` is a nonempty affine open, then the ring of sections `Γ(X, U)` is integrally closed.

This is the "local-to-global" half of the local nature of normality: `IsIntegrallyClosed` is a
local property of a domain, so it suffices to check it at the localizations at maximal ideals.
For an affine open `U = Spec Γ(X, U)` the localizations of `Γ(X, U)` at prime ideals are exactly
the stalks of `X` at the points of `U` (`IsAffineOpen.isLocalization_stalk`), and these are
integrally closed by hypothesis.

Mathlib provides exactly the needed local-global statement,
`IsIntegrallyClosed.of_localization_maximal`, so the work is to identify the localizations of the
coordinate ring with the stalks of `X`.
-/

open CategoryTheory

namespace Work.Domain.Engine

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
theorem isIntegrallyClosed_section {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed (X.presheaf.obj (Opposite.op U)) := by
  -- `X` integral gives that `Γ(X, U)` is a domain, as required by the local-global criterion.
  haveI : IsDomain (X.presheaf.obj (Opposite.op U)) := inferInstance
  -- It suffices to check integral closedness at the localizations at maximal ideals.
  refine IsIntegrallyClosed.of_localization_maximal (fun p hp hmax => ?_)
  -- The point of `U` whose local ring is the localization of `Γ(X, U)` at `p`.
  let y : PrimeSpectrum (X.presheaf.obj (Opposite.op U)) := ⟨p, hmax.isPrime⟩
  let x : U := hU.isoSpec.inv y
  -- `primeIdealOf` is the homeomorphism `U ≃ Spec Γ(X, U)` underlying `hU.isoSpec`, so `x`
  -- indeed corresponds to `p`.
  have hy : hU.primeIdealOf x = y := by
    show hU.isoSpec.hom x = y
    rw [show x = hU.isoSpec.inv y from rfl, ← AlgebraicGeometry.Scheme.Hom.comp_apply,
      Iso.inv_hom_id]
    rfl
  have hAsIdeal : (hU.primeIdealOf x).asIdeal = p := by rw [hy]
  -- `hU.isLocalization_stalk` identifies the stalk at `x` with the localization of `Γ(X, U)`
  -- at `(hU.primeIdealOf x).asIdeal = p`.
  have hsub : p.primeCompl = ((hU.primeIdealOf x).asIdeal).primeCompl := by
    ext a
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hAsIdeal]
  have hloc : IsLocalization p.primeCompl (X.presheaf.stalk x.1) :=
    hsub.symm ▸ hU.isLocalization_stalk x
  haveI : IsLocalization p.primeCompl (X.presheaf.stalk x.1) := hloc
  -- The stalk is integrally closed by hypothesis, hence so is the isomorphic localization.
  haveI : IsIntegrallyClosed (X.presheaf.stalk x.1) := hX x.1
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x.1) (Localization.AtPrime p)).toRingEquiv

end Work.Domain.Engine
