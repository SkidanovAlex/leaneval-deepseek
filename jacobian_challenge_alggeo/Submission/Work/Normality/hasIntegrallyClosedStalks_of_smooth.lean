import Mathlib
import Submission.Work.Normality.Basic
import Submission.Work.Normality.Scheme

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

set_option autoImplicit false

universe u

namespace Work.Normality

/-- A smooth, integral scheme over a field has integrally closed local rings at all of its
points.

Suggested route.  It suffices to produce, for each `x : X`, an affine chart `V ∋ x` together with
a ring homomorphism `K →+* Γ(X, V)` that is `RingHom.IsStandardSmooth`, because
`Work.Normality.hasIntegrallyClosedStalks_of_isStandardSmooth_charts` then finishes (using that
`X` is integral to know that `Γ(X, V)` is a domain).  Such a chart is produced by
`AlgebraicGeometry.Smooth.exists_isStandardSmooth f x`, which gives `U` affine open in `Spec K`,
`V ∋ x` affine open, `e : V ≤ f ⁻¹ᵁ U` and
`hstd : (Scheme.Hom.appLE f U V e).hom.IsStandardSmooth`.

To turn `hstd` (a standard smoothness statement over `Γ(Spec K, U)`) into one over `K`, note:

* `Spec K` is a subsingleton (K is a field) and `f x ∈ U`, so `U = ⊤` and hence
  `Γ(Spec K, U)` is (isomorphic to) `K`; see `Work.Normality.isField_sections_spec` for the
  statement that `Γ(Spec K, U)` is a field, and `Scheme.ΓSpecIso : Γ(Spec R, ⊤) ≅ R` for the
  isomorphism with `K`.
* So the ring homomorphism `K →+* Γ(X, V)` obtained as
  `K ≅ Γ(Spec K, ⊤) → Γ(Spec K, U) → Γ(X, V)` is standard smooth if
  `(Scheme.Hom.appLE f U V e).hom` is: this is
  `RingHom.isStandardSmooth_respectsIso : RingHom.RespectsIso @RingHom.IsStandardSmooth`
  (see `Mathlib/RingTheory/RingHom/StandardSmooth.lean`; `RingHom.RespectsIso P` states that
  `P` is stable under composing with ring isomorphisms on either side), together with the fact
  that the restriction `Γ(Spec K, ⊤) → Γ(Spec K, U)` is an isomorphism (as `U = ⊤`).

Caveat: do not introduce a `Field` instance on `Γ(Spec K, U)` obtained by transporting the field
structure of `K` along an isomorphism, because the resulting `CommRing` structure on
`Γ(Spec K, U)` is not the ambient one measured by `Scheme.Hom.appLE`, and the algebra structures
will not match.  It is cleaner to produce the standard smooth ring homomorphism `K →+* Γ(X, V)`
directly as above. -/
theorem hasIntegrallyClosedStalks_of_smooth {K : Type u} [Field K] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) [AlgebraicGeometry.Smooth f]
    [AlgebraicGeometry.IsIntegral X] : HasIntegrallyClosedStalks X := by
  refine hasIntegrallyClosedStalks_of_isStandardSmooth_charts (K := K) ?_
  intro x
  obtain ⟨U, hU, V, hV, hxV, eUV, hf⟩ := Smooth.exists_isStandardSmooth f x
  -- `Spec K` has a single point, so any open of it containing `f x` is everything.
  have hUtop : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    rw [Subsingleton.elim y (f x)]
    exact eUV hxV
  subst hUtop
  refine ⟨V, hV, hxV, ?_, ?_⟩
  · exact (f.appLE ⊤ V eUV).hom.comp
      (((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv).symm :
        K →+* Γ(Spec (CommRingCat.of K), ⊤))
  · exact hf.comp
      (RingHom.IsStandardSmoothOfRelativeDimension.equiv
        (((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv).symm)).isStandardSmooth

end Work.Normality
