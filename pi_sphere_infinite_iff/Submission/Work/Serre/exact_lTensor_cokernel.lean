import Mathlib
import Submission.Work.Kunneth.Chapter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Right exactness of `M ⊗ -` at the cokernel of a chain map

For a chain map `φ : D' ⟶ D` of chain complexes of `ℤ`-modules, the cokernel projection
`cokernel.π φ` is computed degreewise: in degree `q` the short complex
`D'.X q --(φ.f q)--> D.X q --((cokernel.π φ).f q)--> (cokernel φ).X q`
is exact (it is the `q`-th component of the exact short complex `ShortComplex.cokernelSequence φ`,
by `HomologicalComplex.exact_iff_degreewise_exact`), and `(cokernel.π φ).f q` is an epimorphism.

Hence we may apply the right exactness of the tensor product,
`lTensor_exact : Exact f g → Surjective g → Exact (lTensor Q f) (lTensor Q g)`,
to conclude that `M ⊗ -` preserves this exactness.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Serre

theorem exact_lTensor_cokernel (D' D : ChainComplex (ModuleCat ℤ) ℕ) (φ : D' ⟶ D)
    (M : ModuleCat ℤ) (q : ℕ) :
    Function.Exact (LinearMap.lTensor ↥M (φ.f q).hom)
      (LinearMap.lTensor ↥M ((CategoryTheory.Limits.cokernel.π φ).f q).hom) := by
  -- The `q`-th component of the exact short complex `D' ⟶ D ⟶ cokernel φ` is exact.
  have hq : ((ShortComplex.cokernelSequence φ).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) q)).Exact :=
    (HomologicalComplex.exact_iff_degreewise_exact (ShortComplex.cokernelSequence φ)).1
      (ShortComplex.cokernelSequence_exact φ) q
  -- Its `f` and `g` are `(φ.f q).hom` and `((cokernel.π φ).f q).hom`, so the pair is exact.
  have hrange : (φ.f q).hom.range = ((CategoryTheory.Limits.cokernel.π φ).f q).hom.ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker hq
  have hex : Function.Exact (φ.f q).hom ((CategoryTheory.Limits.cokernel.π φ).f q).hom :=
    LinearMap.exact_iff.mpr hrange.symm
  -- The cokernel projection is an epimorphism, hence surjective.
  have hsurj : Function.Surjective ((CategoryTheory.Limits.cokernel.π φ).f q).hom :=
    (ModuleCat.epi_iff_surjective _).1
      (inferInstance : Epi ((CategoryTheory.Limits.cokernel.π φ).f q))
  -- Right exactness of the tensor product.
  exact lTensor_exact ↥M hex hsurj

end Work.Serre
