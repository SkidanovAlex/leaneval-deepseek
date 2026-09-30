import Mathlib
import Submission.Work.Descent.QuotientSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Descent

universe u

theorem flat_surjective_specMap_tensorProduct {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (A : Type u) [CommRing A] [Algebra k A] :
    AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap A (TensorProduct k A k')))) ∧
      AlgebraicGeometry.Surjective (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap A (TensorProduct k A k')))) := by
  -- Both flatness and surjectivity of `Spec (A ⊗_k k') ⟶ Spec A` are equivalent to
  -- faithful flatness of the ring map `A ⟶ A ⊗_k k'`.
  rw [AlgebraicGeometry.flat_and_surjective_SpecMap_iff]
  -- The extension `k ⟶ k'` of fields is faithfully flat (a nonzero vector space over `k`),
  have h : (algebraMap k k').FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  -- and faithful flatness is stable under base change.
  exact RingHom.IsStableUnderBaseChange.tensorProduct
    RingHom.FaithfullyFlat.isStableUnderBaseChange A h

end Work.Descent
