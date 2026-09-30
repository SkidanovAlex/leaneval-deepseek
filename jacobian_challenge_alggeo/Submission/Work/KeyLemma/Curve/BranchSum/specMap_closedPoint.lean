import Mathlib
import Submission.Work.KeyLemma.Curve.BranchSum.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve.BranchSum

open CategoryTheory AlgebraicGeometry Limits
open scoped Classical

universe u

/-- A ring hom `φ : R →+* k` from a local ring `R` to a field `k` whose kernel is the maximal
ideal of `R` is a local ring homomorphism. -/
theorem isLocalHom_of_ker_eq_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    {k : Type u} [Field k] (φ : R →+* k)
    (hker : RingHom.ker φ = IsLocalRing.maximalIdeal R) : IsLocalHom φ := by
  refine ((IsLocalRing.local_hom_TFAE φ).out 5 1).mp ?_
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]

/-- **The closed point of `Spec k` maps to the closed point of `Spec R`** along `Spec.map φ`, for a
ring hom `φ : R →+* k` whose kernel is the maximal ideal of the local ring `R` (the case
`φ = e ∘ residue` for `e : ResidueField R ≃+* k`). -/
theorem specMap_closedPoint {R : Type u} [CommRing R] [IsLocalRing R] {k : Type u} [Field k]
    (φ : R →+* k) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal R) :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint k)
      = IsLocalRing.closedPoint R := by
  haveI : IsLocalHom φ := isLocalHom_of_ker_eq_maximalIdeal φ hker
  exact Spec_closedPoint

end Work.KeyLemma.Curve.BranchSum
