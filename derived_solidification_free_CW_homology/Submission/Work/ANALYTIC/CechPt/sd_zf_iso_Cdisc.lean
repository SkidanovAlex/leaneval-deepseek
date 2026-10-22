import Mathlib
import Submission.Work.ANALYTIC.CechPt.DoubleDual
import Submission.Work.ANALYTIC.CechPt.SdPrelude
import Submission.Work.ANALYTIC.CechPt.exists_sdPhiLinear

/-!
# The single dual of `ℤ[T]` is `C(T,ℤ)_disc`

The main result of this file is `sd_zf_iso_Cdisc`: for a light profinite set `T`, the single dual

  `sd (ℤ[T]) = (ℤ[T] ⟹ 𝟙)`

of the free light condensed abelian group on `T` is the discrete light condensed abelian group
`Cdisc T = LC(-, ℤ)` of locally constant `ℤ`-valued functions on `T`.

The proof is section-wise: for a light profinite set `S`, both sides have sections canonically
identified with the locally constant functions on `S × T` — for `sd (ℤ[T])` this is
`Work.DISC.sdPhi` (currying the closed structure of `LightCondAb`, `ℤ[S] ⊗ ℤ[T] ≅ ℤ[S × T]` and
`Hom(ℤ[W], A) ≅ A(W)`), and for `Cdisc T` it is the currying of locally constant functions
(`lcCurryEquiv`).  Both identifications are natural in `S` (`sdPhi_natural`,
`lcCurryEquiv_comap`), so they assemble into an isomorphism of sheaves.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite

noncomputable section

namespace Work.ANALYTIC.CechPt

/-! ## A ℤ-linear form of `sdPhi` -/

/-- The section identification `(ℤ[S] ⟹ ΔM)(T) ≅ C(S × T, M)` as a ℤ-linear equivalence. -/
noncomputable def sdPhiLin (M : ModuleCat.{0} ℤ) (S T : LightProfinite.{0}) :
    (Work.DISC.zfree T ⟶ (CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)) ≃ₗ[ℤ]
      LocallyConstant (↥S.toTop × ↥T.toTop) ↥M :=
  Classical.choose (exists_sdPhiLinear M S T)

theorem sdPhiLin_apply (M : ModuleCat.{0} ℤ) (S T : LightProfinite.{0})
    (g : Work.DISC.zfree T ⟶ (CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)) :
    sdPhiLin M S T g = Work.DISC.sdPhi M S T g :=
  congrFun (Classical.choose_spec (exists_sdPhiLinear M S T)) g

/-! ## Naturality of `homFreeEquiv`, in the inverse direction -/

theorem homFreeLinearEquiv_symm_apply (S : LightProfinite.{0}) (A : LightCondAb)
    (x : ↥(A.obj.obj (Opposite.op S))) :
    (homFreeLinearEquiv S A).symm x = (Work.DISC.homFreeEquiv S A).symm x := rfl

/-- Restriction in the sections of `A` corresponds, under `homFreeEquiv`, to precomposition with
`zmap`. -/
theorem homFreeLinearEquiv_symm_map {T T' : LightProfinite.{0}} (π : T' ⟶ T) (A : LightCondAb)
    (x : ↥(A.obj.obj (Opposite.op T))) :
    (homFreeLinearEquiv T' A).symm (A.obj.map π.op x) =
      Work.DISC.zfreeFunctor.map π ≫ (homFreeLinearEquiv T A).symm x := by
  apply (homFreeLinearEquiv T' A).injective
  rw [LinearEquiv.apply_symm_apply, homFreeLinearEquiv_symm_apply]
  rw [show ⇑(homFreeLinearEquiv T' A) = ⇑(Work.DISC.homFreeEquiv T' A) from
    funext (homFreeLinearEquiv_apply T' A)]
  rw [Work.DISC.homFreeEquiv_naturality T' T π A ((Work.DISC.homFreeEquiv T A).symm x),
    Equiv.apply_symm_apply]

/-! ## The comparison of section functors -/

/-- The component of the comparison at a light profinite set `T`, as a linear map. -/
noncomputable def sdComp (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) (T : LightProfinite.{0}) :
    ↥(((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)).obj.obj (op T)) →ₗ[ℤ]
      ↥((Work.DISC.lcDisc (ModuleCat.of ℤ (LocallyConstant ↥S.toTop ↥M))).obj.obj (op T)) :=
  ((lcCurryEquiv S T M).toLinearMap).comp
    (((sdPhiLin M S T).toLinearMap).comp
      ((homFreeLinearEquiv T
        ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M))).symm.toLinearMap))

theorem sdComp_apply (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) (T : LightProfinite.{0})
    (x : ↥(((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)).obj.obj (op T))) :
    sdComp S M T x = lcCurryEquiv S T M (sdPhiLin M S T
      ((homFreeLinearEquiv T
        ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M))).symm x)) := rfl

theorem sdComp_bijective (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) (T : LightProfinite.{0}) :
    Function.Bijective (⇑(sdComp S M T)) := by
  rw [show ⇑(sdComp S M T) =
      ⇑(lcCurryEquiv S T M) ∘ (⇑(sdPhiLin M S T) ∘ ⇑((homFreeLinearEquiv T
        ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M))).symm)) from rfl]
  exact (lcCurryEquiv S T M).bijective.comp
    ((sdPhiLin M S T).bijective.comp
      (homFreeLinearEquiv T
        ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M))).symm.bijective)

/-- **The comparison of the section functors of `ℤ[S] ⟹ ΔM` and of the discrete module of
locally constant `M`-valued functions on `S`.** -/
noncomputable def sdNatTrans (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) :
    ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)).obj ⟶
      (Work.DISC.lcDisc (ModuleCat.of ℤ (LocallyConstant ↥S.toTop ↥M))).obj :=
  NatTrans.mk (fun X => ModuleCat.ofHom (sdComp S M X.unop)) (fun {X Y} f => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨T⟩ := X
    obtain ⟨T'⟩ := Y
    rw [show f = (f.unop).op from (Quiver.Hom.op_unop f).symm]
    simp only [Opposite.unop_op]
    show sdComp S M T' (ConcreteCategory.hom
        (((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)).obj.map
          (f.unop).op) x) =
      ConcreteCategory.hom
        ((Work.DISC.lcDisc (ModuleCat.of ℤ (LocallyConstant ↥S.toTop ↥M))).obj.map
          (f.unop).op) (sdComp S M T x)
    rw [sdComp_apply, sdComp_apply,
      homFreeLinearEquiv_symm_map (T := T) (T' := T') (f.unop)
        ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)) x]
    simp only [sdPhiLin_apply]
    rw [sdPhi_natural M S T' T (f.unop)
        ((homFreeLinearEquiv T
          ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M))).symm x),
      lcCurryEquiv_comap (S := S) (M := M) (T := T') (T' := T) (f.unop)
        (Work.DISC.sdPhi M S T ((homFreeLinearEquiv T
          ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M))).symm x)),
      Work.DISC.lcDisc_map])

/-- The comparison of section functors is an isomorphism. -/
theorem sdNatTrans_isIso (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) :
    IsIso (sdNatTrans S M) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [show (sdNatTrans S M).app X = ModuleCat.ofHom (sdComp S M X.unop) from rfl]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (by
    rw [show ⇑(ModuleCat.ofHom (sdComp S M X.unop)) = ⇑(sdComp S M X.unop) from
      funext (ModuleCat.ofHom_apply (sdComp S M X.unop))]
    exact sdComp_bijective S M X.unop)

/-- The comparison of section functors, as a morphism of sheaves. -/
noncomputable def sdIsoHom (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) :
    (CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M) ⟶
      Work.DISC.lcDisc (ModuleCat.of ℤ (LocallyConstant ↥S.toTop ↥M)) :=
  (sheafToPresheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ)).preimage (sdNatTrans S M)

theorem sdIsoHom_isIso (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) : IsIso (sdIsoHom S M) := by
  have h : (sheafToPresheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ)).map
      (sdIsoHom S M) = sdNatTrans S M := Functor.map_preimage _ _
  haveI : IsIso ((sheafToPresheaf (coherentTopology LightProfinite.{0})
      (ModuleCat.{0} ℤ)).map (sdIsoHom S M)) := by
    rw [h]
    exact sdNatTrans_isIso S M
  exact isIso_of_reflects_iso (sdIsoHom S M)
    (sheafToPresheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ))

/-- **The main comparison**: for a light profinite set `S` and a `ℤ`-module `M`, the internal hom
`ℤ[S] ⟹ ΔM` out of the free module is the discrete module of locally constant `M`-valued functions
on `S`. -/
theorem ihom_zfree_lcDisc_iso (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) :
    Nonempty ((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M) ≅
      Work.DISC.lcDisc (ModuleCat.of ℤ (LocallyConstant ↥S.toTop ↥M))) :=
  haveI := sdIsoHom_isIso S M
  ⟨asIso (sdIsoHom S M)⟩

theorem sd_zf_iso_Cdisc (T : LightProfinite.{0}) :
    Nonempty (Work.ANALYTIC.CechPt.sd ((LightCondensed.free (R := ℤ)).obj T.toCondensed) ≅
      Work.ANALYTIC.Cdisc T) := by
  obtain ⟨e⟩ := ihom_zfree_lcDisc_iso T (ModuleCat.of ℤ ℤ)
  exact ⟨(CategoryTheory.ihom (Work.DISC.zfree T)).mapIso lcDiscIntIso.symm ≪≫ e⟩

end Work.ANALYTIC.CechPt
