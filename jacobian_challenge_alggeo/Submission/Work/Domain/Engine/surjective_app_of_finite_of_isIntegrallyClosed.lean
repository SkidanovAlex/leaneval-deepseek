import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Domain.Engine

/-- Commutative-algebra heart of the engine lemma.

Let `A` be a domain that is integrally closed in a field of fractions `K`, let `f : A →+* B` be a
finite ring homomorphism, and let `φ : B →+* K` be an injective ring homomorphism compatible with
the structure maps (`φ (f r) = algebraMap A K r`).  Then `f` is surjective.

Indeed any `b : B` is integral over `A` because `f` is finite; its image `φ b ∈ K` is therefore
integral over `A` as well, hence lies in the image of `A` since `A` is integrally closed in `K`;
injectivity of `φ` then lifts this to `b`. -/
theorem surjective_of_finite_of_isIntegrallyClosed {A B K : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [CommRing K] [Algebra A K] [IsFractionRing A K] (hR : IsIntegrallyClosed A)
    (f : A →+* B) (φ : B →+* K) (hφ : Function.Injective φ)
    (hφ' : ∀ r, φ (f r) = algebraMap A K r) (hfin : RingHom.Finite f) :
    Function.Surjective f := by
  intro b
  have hint : IsIntegral A (φ b) := by
    have h : f.IsIntegralElem b := hfin.to_isIntegral b
    have h2 := h.map φ
    rwa [show φ.comp f = algebraMap A K from RingHom.ext hφ'] at h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, ?_⟩
  apply hφ
  rw [← ha, hφ']

theorem surjective_app_of_finite_of_isIntegrallyClosed {G X : AlgebraicGeometry.Scheme}
    (p : G ⟶ X) {U : X.Opens} [IrreducibleSpace X] [Nonempty U]
    [IsDomain (X.presheaf.obj (Opposite.op U))]
    (hR : IsIntegrallyClosed (X.presheaf.obj (Opposite.op U)))
    [IsFractionRing (X.presheaf.obj (Opposite.op U)) X.functionField]
    (φ : (G.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U))) →+*
      X.functionField)
    (hφ : Function.Injective φ)
    (hφ' : ∀ r : X.presheaf.obj (Opposite.op U),
      φ ((p.app U).hom r) = algebraMap (X.presheaf.obj (Opposite.op U)) X.functionField r)
    (hfin : RingHom.Finite (p.app U).hom) :
    Function.Surjective ((p.app U).hom) :=
  surjective_of_finite_of_isIntegrallyClosed hR (p.app U).hom φ hφ hφ' hfin

end Work.Domain.Engine
