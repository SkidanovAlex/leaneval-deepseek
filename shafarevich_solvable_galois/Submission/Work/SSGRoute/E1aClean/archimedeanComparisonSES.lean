import Mathlib
import Submission.Work.SSGRoute.E1aClean.ArchCompare
import Submission.Work.SSGRoute.E1aClean.ArchSeam
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.E1cGeneric.freeCoverCompat_comp
import Submission.Work.SSGRoute.E1cGeneric.freeCoverCompat_single
import Submission.Work.SSGRoute.PT.freeCoverCompatKernel
import Submission.Work.SSGRoute.PT.freeCoverSES_res_comparison
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean comparison square of the `E1a` landing clause

This module proves `archimedeanComparisonSES`: the place-change `SES`-morphism from the restriction
to `⟨σ⟩` of the global dualised canonical resolution to the local one at the archimedean datum
`(ℝ, ℂ, ⊤)`, whose three components are the *seam* coefficient change `seamCoeff φ`
(`E1aClean/ArchCompare.lean`) composed with the comparison of the canonical covers
(`PT/freeCoverSES_res_comparison.lean`, `PT/freeCoverCompatKernel.lean`).

The local group is `localGroup = ↥⊤ ≃ₐ[ℝ] ↥⊤` and the global one is `↥K ≃ₐ[k] ↥K`; the two are
related by the composite `archCompareHom` of the local group identification `Φ`, the inclusion
`⟨σ⟩ ≤ Gal(Ω/k)` and the restriction `res k K`.  The first variable of the local dictionary,
`localX σ X Φ`, is *definitionally* the restriction `Rep.res (archCompareHom K σ Φ) X`, so the
comparison of the canonical presentations along `archCompareHom` (`freeCoverSES_res_comparison`)
supplies both the middle component `u₂` and the syzygy component `u₃`; the two squares are then the
two commutation squares of that morphism of short complexes, evaluated on the underlying functions.
-/

open Work.SSGRoute Work.SSGRoute.E1aClean
open CategoryTheory

set_option maxHeartbeats 1000000

-- The carrier of a representation carries two candidate `AddCommGroup`/`Module` instances; the
-- resulting diamond shows up as a failure of the *elaborator* to see two `AddMonoidHom`-types as
-- equal at the `implicit` transparency level used when checking applications.
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute.E1aClean

noncomputable section

-- instance priorities as in `homCoindDefs.lean`: the carrier of a representation carries two
-- candidate `AddCommGroup`/`Module` instances (`Rep.hV1`, `Rep.hV2` and the ones coming from the
-- underlying type); the diamond then shows up as non-defeq `AddMonoidHom`-types.
attribute [local instance 10000] Rep.hV1 Rep.hV2

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- The comparison group homomorphism `localGroup →* Gal(K/k)`: the local group identification
`Φ : ↥⟨σ⟩ ≃* localGroup`, the inclusion `⟨σ⟩ ≤ Gal(Ω/k)` and the restriction to `K`. -/
noncomputable def archCompareHom (σ : Ω ≃ₐ[k] Ω) (Φ : ↥(Subgroup.zpowers σ) ≃* localGroup) :
    localGroup →* (↥K ≃ₐ[k] ↥K) :=
  (SSGRoute.res k K).comp ((Subgroup.zpowers σ).subtype.comp Φ.symm.toMonoidHom)

omit [IsAlgClosure k Ω] [NumberField ↥K] in
/-- The first variable of the local dictionary is the restriction of `X` along `archCompareHom`. -/
theorem localX_eq_res_archCompareHom (σ : Ω ≃ₐ[k] Ω)
    (Φ : ↥(Subgroup.zpowers σ) ≃* localGroup)
    (X : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)) :
    localX (k := k) (Ω := Ω) (K := K) σ X Φ = Rep.res (archCompareHom K σ Φ) X := rfl

/-- **(Left square, pointwise)** The syzygy comparison of `freeCoverSES_res_comparison` intertwines
the two kernel inclusions with the comparison of the middle terms. -/
theorem freeCoverSES_res_comparison_kernel_apply {G H : Type} [Group G] [Group H] (ω : H →* G)
    (X : Rep.{0} SSGRoute.PTExt.Coeff G)
    (Φh : CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES (Rep.res ω X))
      ((Work.SSGRoute.freeCoverSES X).map (Rep.resFunctor ω)))
    (r : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res ω X))).V) :
    (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X)))
        (Rep.Hom.hom Φh.τ₁ r)
      = (Rep.Hom.hom Φh.τ₂)
          ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι
            (Work.SSGRoute.freeCover (Rep.res ω X)))) r) := by
  have hs : Φh.τ₁ ≫ ((Work.SSGRoute.freeCoverSES X).map (Rep.resFunctor ω)).f
      = (Work.SSGRoute.freeCoverSES (Rep.res ω X)).f ≫ Φh.τ₂ := Φh.comm₁₂
  have h := congrArg (fun m => (Rep.Hom.hom m) r) hs
  rw [Rep.comp_apply, Rep.comp_apply] at h
  exact h

/-- **(Middle square, pointwise)** For a comparison `Φh` of the canonical presentations along
`ω : H →* G` whose third component is the identity, the two canonical covers agree after the
comparison of the middle terms. -/
theorem freeCoverSES_res_comparison_comp_apply {G H : Type} [Group G] [Group H] (ω : H →* G)
    (X : Rep.{0} SSGRoute.PTExt.Coeff G)
    (Φh : CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES (Rep.res ω X))
      ((Work.SSGRoute.freeCoverSES X).map (Rep.resFunctor ω)))
    (hτ₃ : CategoryTheory.ConcreteCategory.hom Φh.τ₃
      = CategoryTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.id (Rep.res ω X)))
    (t : (Rep.free SSGRoute.PTExt.Coeff H X.V).V) :
    (Rep.Hom.hom (Work.SSGRoute.freeCover X)) (Rep.Hom.hom Φh.τ₂ t)
      = (Rep.Hom.hom (Work.SSGRoute.freeCover (Rep.res ω X))) t := by
  have hs : Φh.τ₂ ≫ ((Work.SSGRoute.freeCoverSES X).map (Rep.resFunctor ω)).g
      = (Work.SSGRoute.freeCoverSES (Rep.res ω X)).g ≫ Φh.τ₃ := Φh.comm₂₃
  have h := congrArg (fun m => (Rep.Hom.hom m) t) hs
  rw [Rep.comp_apply, Rep.comp_apply] at h
  rw [hτ₃] at h
  exact h

theorem archimedeanComparisonSES {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)))
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hres : SSGRoute.res k K σ = (τ : ↥K ≃ₐ[k] ↥K))
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)) [Finite X.V]
    [IsAlgClosure ℝ ℂ]
    [FiniteDimensional ℝ Work.SSGRoute.E1aClean.localLevel]
    [IsGalois ℝ Work.SSGRoute.E1aClean.localLevel]
    (Φ : ↥(Subgroup.zpowers σ) ≃* Work.SSGRoute.E1aClean.localGroup) :
    ∃ (u₂ : (Rep.free SSGRoute.PTExt.Coeff Work.SSGRoute.E1aClean.localGroup X.V).V →+
              (Rep.free SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K) X.V).V)
      (u₃ : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
              (Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ))).V →+
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).V),
      (∀ x : Work.SSGRoute.homCoind k Ω K X,
        (Work.SSGRoute.PT.e1aSESgen (k := ℝ) (Ω := ℂ) (K := Work.SSGRoute.E1aClean.localLevel)
            (Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ)).iota
            ((Work.SSGRoute.E1aClean.seamCoeff φ) x)
          = (Work.SSGRoute.E1aClean.seamCoeff φ)
              (((Work.SSGRoute.ExtChain.restrictSES
                  (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) X)
                  (Subgroup.zpowers σ)).iota x).comp u₂)) ∧
      (∀ y : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K X.V,
        (Work.SSGRoute.PT.e1aSESgen (k := ℝ) (Ω := ℂ) (K := Work.SSGRoute.E1aClean.localLevel)
            (Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ)).pi
            ((Work.SSGRoute.E1aClean.seamCoeff φ) (y.comp u₂))
          = (Work.SSGRoute.E1aClean.seamCoeff φ)
              (((Work.SSGRoute.ExtChain.restrictSES
                  (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) X)
                  (Subgroup.zpowers σ)).pi y).comp u₃)) := by
  classical
  obtain ⟨Φh, hτ₂, hτ₃⟩ :=
    Work.SSGRoute.PT.freeCoverSES_res_comparison (G := ↥K ≃ₐ[k] ↥K) (H := localGroup)
      (archCompareHom K σ Φ) X
  have hτ₃hom : CategoryTheory.ConcreteCategory.hom Φh.τ₃
      = CategoryTheory.ConcreteCategory.hom
          (CategoryTheory.CategoryStruct.id (Rep.res (archCompareHom K σ Φ) X)) :=
    congrArg (fun m => CategoryTheory.ConcreteCategory.hom m) hτ₃
  -- the two squares of the morphism of short complexes `Φh`, read on the underlying functions
  have hmap : (Rep.Hom.hom (Work.SSGRoute.freeCover X)).toAddMonoidHom.comp
        Φh.τ₂.hom.toAddMonoidHom
      = (Rep.Hom.hom (Work.SSGRoute.freeCover
          (Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ))).toAddMonoidHom := by
    refine AddMonoidHom.ext (fun t => ?_)
    simp only [AddMonoidHom.comp_apply]
    exact freeCoverSES_res_comparison_comp_apply (archCompareHom K σ Φ) X Φh hτ₃hom t
  have hker : Φh.τ₂.hom.toAddMonoidHom.comp (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι
        (Work.SSGRoute.freeCover
          (Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ)))).toAddMonoidHom
      = (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι
          (Work.SSGRoute.freeCover X))).toAddMonoidHom.comp Φh.τ₁.hom.toAddMonoidHom := by
    refine AddMonoidHom.ext (fun r => ?_)
    simp only [AddMonoidHom.comp_apply]
    exact (freeCoverSES_res_comparison_kernel_apply (archCompareHom K σ Φ) X Φh r).symm
  refine ⟨Φh.τ₂.hom.toAddMonoidHom, Φh.τ₁.hom.toAddMonoidHom, ?_, ?_⟩
  · intro x
    rw [Work.SSGRoute.PT.e1aSESgen_iota (Work.SSGRoute.E1aClean.localX
          (k := k) (Ω := Ω) (K := K) σ X Φ),
        Work.SSGRoute.ExtChain.restrictSES_iota,
        Work.SSGRoute.PT.e1aSESgen_iota X,
        Work.SSGRoute.precompAddHom_apply, Work.SSGRoute.precompAddHom_apply]
    simp only [Work.SSGRoute.E1aClean.seamCoeff_precomp, AddMonoidHom.comp_assoc, hmap]
  · intro y
    rw [Work.SSGRoute.PT.e1aSESgen_pi (Work.SSGRoute.E1aClean.localX
          (k := k) (Ω := Ω) (K := K) σ X Φ),
        Work.SSGRoute.ExtChain.restrictSES_pi,
        Work.SSGRoute.PT.e1aSESgen_pi X,
        Work.SSGRoute.precompAddHom_apply, Work.SSGRoute.precompAddHom_apply]
    simp only [Work.SSGRoute.E1aClean.seamCoeff_precomp, AddMonoidHom.comp_assoc, hker]

end

end Work.SSGRoute.E1aClean
