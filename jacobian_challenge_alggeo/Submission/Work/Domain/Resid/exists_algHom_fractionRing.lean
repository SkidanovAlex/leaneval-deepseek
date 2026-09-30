import Mathlib
import Submission.Work.Domain.Resid.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Domain.Resid

theorem exists_algHom_fractionRing {K : Type _} [Field K] {X : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsIntegral X.left] (x : X.left)
    {A : Type _} [CommRing A] [Algebra K A] [Algebra A X.left.functionField]
    [IsScalarTower K A X.left.functionField]
    (ρ : X.left.presheaf.stalk x →+* A)
    (hρ : (algebraMap A X.left.functionField).comp ρ =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField)
    (hfrac : IsFractionRing A X.left.functionField) :
    ∃ e : X.left.functionField →ₐ[K] FractionRing A,
      e.comp (IsScalarTower.toAlgHom K A X.left.functionField) =
        IsScalarTower.toAlgHom K A (FractionRing A) := by
  -- `hfrac` exhibits the function field as the fraction ring of `A`, i.e. as the
  -- localization of `A` at its non-zero-divisors; `FractionRing A` is the same
  -- localization.  Two localizations of the same ring at the same submonoid
  -- are isomorphic, and the isomorphism is canonically `A`-linear.
  haveI : IsLocalization (nonZeroDivisors A) X.left.functionField := hfrac
  refine ⟨AlgEquiv.restrictScalars K (IsLocalization.algEquiv (nonZeroDivisors A)
      X.left.functionField (FractionRing A)), ?_⟩
  -- Both sides are `K`-algebra maps `A →ₐ[K] FractionRing A`; they agree on `A`
  -- because the equivalence is an `A`-algebra equivalence.
  ext a
  simp [IsScalarTower.toAlgHom]

end Work.Domain.Resid
