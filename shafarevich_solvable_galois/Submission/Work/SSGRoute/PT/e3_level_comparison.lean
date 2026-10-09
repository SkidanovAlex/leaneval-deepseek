import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_defs
import Submission.Work.SSGRoute.classIncl_isCanonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **The level comparison for the `H⁰`-slot of the cup product.**

For a `Gal(K/k)`-map `φ : ℤ → C_K` and a finite Galois level `L` of `K`, the composite
`res φ` followed by `classIncl` — the coefficient map `ℤ → C_L` at the level `L` — is exactly
`powHomCls` of the element `classIncl (φ 1) ∈ C_L`, i.e. the map `1 ↦ image of φ(1)`.  This is the
small computation which puts the coefficient map produced by `E3Ext.phiAt_pushClass_eq` into the
shape required by the cyclic norm criterion `CFTSide.cyclicNormCriterion_classesK` (node `E3`).

`hafix` is the `Gal(L/k)`-fixedness of the image of `φ(1)` (which holds because `φ` is equivariant);
it is taken as a hypothesis only to keep the statement free of a proof term. -/
theorem e3_level_comparison (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (φ : SSGRoute.PTExt.unitRep (K ≃ₐ[k] K) ⟶ SSGRoute.PTExt.classesK k K)
    (hafix : ∀ σ : L ≃ₐ[k] L,
      (SSGRoute.PTExt.classesK k L).ρ σ
          ((SSGRoute.PTExt.classIncl k K L) ((Rep.Hom.hom φ) 1))
        = (SSGRoute.PTExt.classIncl k K L) ((Rep.Hom.hom φ) 1)) :
    CategoryTheory.CategoryStruct.comp
        ((Rep.resFunctor (SSGRoute.PTExt.galRes k K L)).map φ)
        (SSGRoute.PTExt.classIncl k K L)
      = Work.SSGRoute.Phi1.powHomCls k L
          ((SSGRoute.PTExt.classIncl k K L) ((Rep.Hom.hom φ) 1)) hafix := by
  -- both sides are morphisms of `Gal(L/k)`-representations `ℤ → C_L`; compare their underlying
  -- `ℤ`-linear maps on the generator-shaped input `x : ℤ`
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  -- put the right-hand side in the definitional shape `(powHomCls …) x`, so that the defining
  -- equation `powHomCls_apply` fires without any instance ambiguity
  show (Rep.Hom.hom (SSGRoute.PTExt.classIncl k K L)) ((Rep.Hom.hom φ) x)
    = (Rep.Hom.hom (Work.SSGRoute.Phi1.powHomCls k L
        ((Rep.Hom.hom (SSGRoute.PTExt.classIncl k K L)) ((Rep.Hom.hom φ) 1)) hafix)) x
  rw [Work.SSGRoute.Phi1.powHomCls_apply]
  -- `x` is `x • 1` in the coefficient ring
  have h1 : x • (1 : SSGRoute.PTExt.Coeff) = x := by simp [smul_eq_mul]
  -- the equivariant map `φ` is `Coeff`-linear, so it is determined by its value at `1`
  have hφ : (Rep.Hom.hom φ) x = x • ((Rep.Hom.hom φ) 1) := by
    have h2 := LinearMap.map_smul (Rep.Hom.hom φ).toLinearMap x (1 : SSGRoute.PTExt.Coeff)
    rw [h1] at h2
    exact h2
  rw [hφ]
  -- and `classIncl`, being a morphism of representations, is `Coeff`-linear as well
  exact LinearMap.map_smul (Rep.Hom.hom (SSGRoute.PTExt.classIncl k K L)).toLinearMap x _

end Work.SSGRoute.PT
