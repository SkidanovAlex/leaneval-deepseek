import Mathlib
import Submission.Work.ANALYTIC.primedFamily
import Submission.Work.ANALYTIC.exists_tower_F_EAdata
import Submission.Work.ANALYTIC.gSetup
import Submission.Work.ANALYTIC.qElem_cBounded
import Submission.Work.REFL.pre_app_points
import Submission.Work.ANALYTIC.genPointsExt
import Submission.Work.ANALYTIC.EApp_idTensorHom_cBounded_truncF
import Submission.Work.ANALYTIC.truncDataElem_ns2_deltaElem

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

/-!
# The coefficient-extraction map `G : P ⊗ ∏^bnd ℤ ⟶ P`, together with `h₁` and `h₄`

The map `G` of REFS/03 §2 is the null family `(k,x) ↦ x_k·e_k`, i.e.
`MonoidalClosed.uncurry (gTheta qElem_cBounded)`, where `gTheta : ∏^bnd ℤ ⟶ (P ⟹ P)` has
`S`-points `x ↦ gPsi qElem_cBounded S x`, the descent of the element `qElem S x ∈ P((ℕ∪∞) ⊗ S)`
(see `Submission/Work/ANALYTIC/gSetup.lean`).

The two identities proved here are

* `h₁ : T ≫ F = G ≫ cBounded`, with `F = truncF` the truncation family and
  `T = tensorOneMinusShift ∏^bnd ℤ = (1-S) ⊗ id`: this is `gPsi_point` moved through currying;
* `h₄ : (id_P ⊗ cBounded) ≫ G = ((1-S) ⊗ id_P) ≫ F'`, with `F' = FP` the primed family of
  `Submission/Work/ANALYTIC/primedFamily.lean`.

Since `cBounded` is a monomorphism, `h₄` is a *formal* consequence of `h₁` and of the third
identity `h₃ : (id_P ⊗ cBounded) ≫ F = F' ≫ cBounded`: after postcomposition with `cBounded`,
`whisker_exchange` moves `(1-S) ⊗ id` past `id ⊗ cBounded` and `h₃` cancels the two `F`'s.
The identity `h₃` is proved by cancelling the epimorphism `EApp : ℤ[(ℕ∪∞)²] ⟶ P ⊗ P` and
comparing the two classified elements of `∏^bnd ℤ((ℕ∪∞) ⊗ (ℕ∪∞))` pointwise.

This module deliberately does NOT import `Submission.Work.ANALYTIC.cBounded_solidEquiv` (hence
also not `exists_unprimedTower.lean`, which imports it), so that the final assembly can use the
statement without an import cycle; the construction of `Gtower` and the proof of `h₁` are
therefore restated here (they are the same content as in `exists_unprimedTower.lean`).
-/

/-- The `S`-points of the internal hom `∏^bnd ℤ` and of `P ⊗ ℤ[S]` are related by
`LightCondensed.ihomPoints`; this is Mathlib's `ihom_map_val_app` in the `ihomPoints`-form:
postcomposition with `cBounded` becomes postcomposition of the evaluated morphism with
`cBounded`. -/
theorem ihomPoints_ihom_map_cBounded (S : LightProfinite.{0})
    (y : ↥(((ihom LightCondensed.P).obj LightCondensed.P).obj.obj (op S))) :
    LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
        (((ihom LightCondensed.P).map Work.ANALYTIC.cBounded).hom.app (op S) y) =
      LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P S y ≫
        Work.ANALYTIC.cBounded := by
  rw [show (((ihom LightCondensed.P).map Work.ANALYTIC.cBounded).hom.app (op S) y : _)
      = (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S).symm
          (LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P S y ≫
            Work.ANALYTIC.cBounded) from
    LightCondensed.ihom_map_val_app ℤ LightCondensed.P boundedSeq LightCondensed.P S
      Work.ANALYTIC.cBounded y]
  exact Equiv.apply_symm_apply _ _

/-- The point description of `pre oneMinusShift` (`Work.REFL.ihomPoints_pre`) in the form used
here: on `S`-points, precomposition with `oneMinusShift` corresponds to precomposition of the
evaluated morphism `P ⊗ ℤ[S] ⟶ M` with `oneMinusShift ▷ ℤ[S]`. -/
theorem ihomPoints_pre_oneMinusShift (S : LightProfinite.{0})
    (y : ↥(((ihom LightCondensed.P).obj boundedSeq).obj.obj (op S))) :
    LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
        (((pre LightCondensed.oneMinusShift).app boundedSeq).hom.app (op S) y) =
      (LightCondensed.oneMinusShift ▷ Work.ATOM.zfree S) ≫
        LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S y := by
  rw [show (((pre LightCondensed.oneMinusShift).app boundedSeq).hom.app (op S) y : _)
      = (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S).symm
          (LightCondensed.oneMinusShift ▷ Work.ATOM.zfree S ≫
            LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S y) from
    Work.REFL.ihomPoints_pre ℤ LightCondensed.P LightCondensed.P boundedSeq
      LightCondensed.oneMinusShift S y]
  exact Equiv.apply_symm_apply _ _

/-! ## The natural transformation `θG = curry G` and the morphism `G` -/

section Assembly

variable (hQ : QElemCBounded)

/-- The `S`-component of `θG`, as a linear map: `x ↦ gPsi hQ S x`, transported across the
identification of the points of the internal hom with the uncurried morphisms. -/
noncomputable def gThetaComp (S : (LightProfinite.{0})ᵒᵖ) :
    ↥(boundedSeq.obj.obj S) →ₗ[ℤ]
      ↥(((ihom LightCondensed.P).obj LightCondensed.P).obj.obj S) where
  toFun := fun x =>
    (LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P S.unop).symm
      (gPsi hQ S.unop x)
  map_add' := fun x y => by rw [gPsi_add, ihomPoints_symm_add_aux]
  map_smul' := fun c x => by
    rw [gPsi_smul, ihomPoints_symm_zsmul_aux]
    exact (int_smul_eq_zsmul
      ((((ihom LightCondensed.P).obj LightCondensed.P).obj.obj S).isModule) c _).symm

/-- The `S`-point of `θG` is the `ihomPoints`-transport of `gPsi hQ S x`. -/
theorem gThetaComp_apply (S : (LightProfinite.{0})ᵒᵖ)
    (x : ↥(boundedSeq.obj.obj S)) :
    gThetaComp hQ S x = (LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P
      S.unop).symm (gPsi hQ S.unop x) := rfl

/-- **The natural transformation `θG`.**  Its `S`-point sends `x ∈ ∏^bnd ℤ(S)` to the morphism
`P ⊗ ℤ[S] ⟶ P` whose null family is `(k,x) ↦ x_k·e_k`; its naturality is `gPsi_nat`. -/
noncomputable def gTheta : boundedSeq ⟶ (ihom LightCondensed.P).obj LightCondensed.P :=
  ObjectProperty.homMk
    { app := fun S => ModuleCat.ofHom (gThetaComp hQ S)
      naturality := by
        intro S T g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have key : gPsi hQ T.unop (boundedSeq.obj.map g x)
            = (LightCondensed.P ◁ Work.ATOM.zmap g.unop) ≫ gPsi hQ S.unop x :=
          (gPsi_nat hQ T.unop S.unop g.unop x).symm
        rw [show (ModuleCat.Hom.hom (boundedSeq.obj.map g ≫ ModuleCat.ofHom (gThetaComp hQ T))) x
            = (gThetaComp hQ T) ((boundedSeq.obj.map g) x) from rfl]
        rw [show (ModuleCat.Hom.hom (ModuleCat.ofHom (gThetaComp hQ S) ≫
              ((ihom LightCondensed.P).obj LightCondensed.P).obj.map g)) x
            = (((ihom LightCondensed.P).obj LightCondensed.P).obj.map g) ((gThetaComp hQ S) x)
          from rfl]
        rw [show (gThetaComp hQ T) ((boundedSeq.obj.map g) x)
            = (LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P T.unop).symm
                (gPsi hQ T.unop (boundedSeq.obj.map g x)) from rfl]
        rw [show (gThetaComp hQ S) x
            = (LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P S.unop).symm
                (gPsi hQ S.unop x) from rfl]
        rw [show (((ihom LightCondensed.P).obj LightCondensed.P).obj.map g)
              ((LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P S.unop).symm
                (gPsi hQ S.unop x))
            = (((ihom LightCondensed.P).obj LightCondensed.P).obj.map (g.unop).op)
                ((LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P S.unop).symm
                  (gPsi hQ S.unop x)) from rfl]
        rw [key]
        exact LightCondensed.ihomPoints_symm_comp ℤ LightCondensed.P LightCondensed.P T.unop
          S.unop g.unop (gPsi hQ S.unop x) }

/-- The `ihomPoints`-value of the `S`-point of `θG` is `gPsi hQ S x`. -/
theorem ihomPoints_gTheta (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    LightCondensed.ihomPoints ℤ LightCondensed.P LightCondensed.P S
        ((gTheta hQ).hom.app (Opposite.op S) x) = gPsi hQ S x :=
  Equiv.apply_symm_apply _ _

/-- **The map `G : P ⊗ ∏^bnd ℤ ⟶ P` of REFS/03 §2**, the uncurrying of `θG`: its null family is
`(k,x) ↦ x_k·e_k`. -/
noncomputable def Gtower : LightCondensed.P ⊗ boundedSeq ⟶ LightCondensed.P :=
  MonoidalClosed.uncurry (gTheta hQ)

/-- **The identity `h₁` of REFS/03 §1, `T ≫ F = G ≫ cBounded`.**  For any `F` whose null family
is the family of truncations (`IsTruncEAdata F`), the morphism `Gtower` above satisfies
`tensorOneMinusShift boundedSeq ≫ F = G ≫ cBounded`.

Proof: curry both sides (`MonoidalClosed.curry_injective`, `curry_natural_right`, `curry_pre_app`,
`curry_uncurry`), reducing to the identity of natural transformations
`θG ≫ (ihom P).map cBounded = curry F ≫ (pre oneMinusShift).app boundedSeq`, which is checked on
generalized points (`Work.ANALYTIC.hom_eq_of_zfree_comp_eq`) and then, via `ihomPoints`, is
exactly `gPsi_point`. -/
theorem uncurry_gTheta_comp_cBounded
    (F : LightCondensed.P ⊗ boundedSeq ⟶ boundedSeq) (hF : IsTruncEAdata F) :
    tensorOneMinusShift boundedSeq ≫ F = Gtower hQ ≫ Work.ANALYTIC.cBounded := by
  apply MonoidalClosed.curry_injective
  rw [show MonoidalClosed.curry (Gtower hQ ≫ Work.ANALYTIC.cBounded)
      = MonoidalClosed.curry (Gtower hQ) ≫
          (ihom LightCondensed.P).map Work.ANALYTIC.cBounded from
    MonoidalClosed.curry_natural_right (Gtower hQ) Work.ANALYTIC.cBounded]
  rw [show MonoidalClosed.curry (Gtower hQ) = gTheta hQ from
    MonoidalClosed.curry_uncurry (gTheta hQ)]
  rw [show MonoidalClosed.curry (tensorOneMinusShift boundedSeq ≫ F)
      = MonoidalClosed.curry F ≫
          (pre LightCondensed.oneMinusShift).app boundedSeq from
    (MonoidalClosed.curry_pre_app LightCondensed.oneMinusShift F).symm]
  apply hom_eq_of_zfree_comp_eq
  intro S g
  apply (Work.ATOM.homFreeEquiv S ((ihom LightCondensed.P).obj boundedSeq)).injective
  rw [Work.ATOM.homFreeEquiv_naturality_target S
      (gTheta hQ ≫ (ihom LightCondensed.P).map Work.ANALYTIC.cBounded) g,
    Work.ATOM.homFreeEquiv_naturality_target S
      (MonoidalClosed.curry F ≫
        (pre LightCondensed.oneMinusShift).app boundedSeq) g]
  rw [show ((gTheta hQ ≫ (ihom LightCondensed.P).map Work.ANALYTIC.cBounded).hom.app (op S))
        ((Work.ATOM.homFreeEquiv S boundedSeq) g)
      = ((ihom LightCondensed.P).map Work.ANALYTIC.cBounded).hom.app (op S)
          ((gTheta hQ).hom.app (op S) ((Work.ATOM.homFreeEquiv S boundedSeq) g)) from rfl]
  rw [show ((MonoidalClosed.curry F ≫
          (pre LightCondensed.oneMinusShift).app boundedSeq).hom.app (op S))
        ((Work.ATOM.homFreeEquiv S boundedSeq) g)
      = ((pre LightCondensed.oneMinusShift).app boundedSeq).hom.app (op S)
          ((MonoidalClosed.curry F).hom.app (op S) ((Work.ATOM.homFreeEquiv S boundedSeq) g))
      from rfl]
  apply (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S).injective
  rw [ihomPoints_ihom_map_cBounded, ihomPoints_gTheta, ihomPoints_pre_oneMinusShift]
  exact (gPsi_point hQ F hF S _).symm

end Assembly

/-! ## The identity `h₃`

`h₃` is `(id_P ⊗ cBounded) ≫ F = F' ≫ cBounded`, i.e. `(P ◁ cBounded) ≫ truncF = FP ≫ cBounded`.
Both sides are morphisms `ℤ[(ℕ∪∞)²] ⟶ ∏^bnd ℤ` after precomposition with the epimorphism
`EApp : ℤ[(ℕ∪∞)²] ⟶ P ⊗ P`; there, the two sides are the `homFreeEquiv`-classifications of
concrete elements of `∏^bnd ℤ((ℕ∪∞) ⊗ (ℕ∪∞))`:

* the left hand side is classified by `truncDataElem (ℕ∪∞) deltaElem` (this is
  `isTruncEAdata_truncF` at the test object `ℕ∪∞` and the section `deltaElem`, using that
  `EApp = EA (ℕ∪∞) ≫ (P ◁ P_proj)` and that `P_proj ≫ cBounded` is classified by `deltaElem`);
* the right hand side is classified by the pullback of `deltaElem` along `pairMor`
  (`FP_spec` together with the naturality of `zmap`);
* and those two elements agree pointwise: at `(k,j)` in level `m` both are `[j = m]·[k ≤ m]`. -/

/-- The epimorphism `E_{A'} = EApp : ℤ[(ℕ∪∞)²] ⟶ P ⊗ P`. -/
theorem epi_EApp : Epi Work.ATOM.EApp := by
  have hP : Epi LightCondensed.P_proj :=
    inferInstanceAs (Epi (cokernel.π LightCondensed.P_map))
  haveI h1 : Epi (LightCondensed.P_proj ▷ Work.ATOM.zfree LightProfinite.NatUnionInfty) := by
    haveI := hP
    exact Functor.map_epi (MonoidalCategory.tensorRight
      (Work.ATOM.zfree LightProfinite.NatUnionInfty)) LightCondensed.P_proj
  haveI h2 : Epi (LightCondensed.P ◁ LightCondensed.P_proj) := by
    haveI := hP
    exact Functor.map_epi (MonoidalCategory.tensorLeft LightCondensed.P) LightCondensed.P_proj
  haveI h3 : Epi (Work.ATOM.EA LightProfinite.NatUnionInfty) := by
    rw [Work.ATOM.EA]
    exact epi_comp _ _
  rw [show Work.ATOM.EApp = Work.ATOM.EA LightProfinite.NatUnionInfty ≫
      (LightCondensed.P ◁ LightCondensed.P_proj) from rfl]
  exact epi_comp _ _

/-- **The right hand side of `h₃`, computed.**  After applying `EApp`, the composite
`FP ≫ cBounded` becomes the morphism classified by the pullback of `deltaElem` along `pairMor`. -/
theorem EApp_FP_comp_cBounded_aux :
    Work.ATOM.EApp ≫ (Work.ANALYTIC.FP ≫ Work.ANALYTIC.cBounded) =
      (Work.ATOM.homFreeEquiv Work.ATOM.NS2 Work.ANALYTIC.boundedSeq).symm
        ((Work.ANALYTIC.boundedSeq.obj.map (Work.ANALYTIC.pairMor).op)
          Work.ANALYTIC.deltaElem) := by
  rw [← Category.assoc, Work.ANALYTIC.FP_spec]
  rw [show Work.ANALYTIC.chi = Work.ATOM.zmap Work.ANALYTIC.pairMor ≫
      LightCondensed.P_proj from rfl]
  rw [Category.assoc]
  rw [show LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded =
      (Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq).symm
        Work.ANALYTIC.deltaElem from Work.ANALYTIC.P_proj_cBounded]
  exact Work.ANALYTIC.zmapSymm Work.ANALYTIC.boundedSeq Work.ATOM.NS2
    LightProfinite.NatUnionInfty Work.ANALYTIC.pairMor Work.ANALYTIC.deltaElem

/-- **The identity `h₃` of REFS/03 §1**: `(id_P ⊗ cBounded) ≫ F = F' ≫ cBounded`, i.e.
`(P ◁ cBounded) ≫ truncF = FP ≫ cBounded`.  The two composites with `EApp` are the morphisms
classified by `truncDataElem (ℕ∪∞) deltaElem` (the delegated lemma
`Work.ANALYTIC.EApp_idTensorHom_cBounded_truncF`) and by the pullback of `deltaElem` along
`pairMor` (`EApp_FP_comp_cBounded_aux`); these two elements agree pointwise (the delegated lemma
`Work.ANALYTIC.truncDataElem_ns2_deltaElem`), and `EApp` is an epimorphism. -/
theorem h3_truncF_FP :
    (LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫ Work.ANALYTIC.truncF =
      Work.ANALYTIC.FP ≫ Work.ANALYTIC.cBounded := by
  haveI := epi_EApp
  refine (cancel_epi Work.ATOM.EApp).mp ?_
  rw [EApp_idTensorHom_cBounded_truncF, truncDataElem_ns2_deltaElem,
    ← EApp_FP_comp_cBounded_aux]

/-- **The identity `h₄` of REFS/03 §1**: `(id_P ⊗ cBounded) ≫ G = ((1-S) ⊗ id) ≫ F'`, i.e.
`(P ◁ cBounded) ≫ Gtower = tensorOneMinusShift P ≫ FP`.  This follows from `h₁`, `h₃` and the
fact that `cBounded` is a monomorphism (postcompose both sides with `cBounded` and use
`whisker_exchange`). -/
theorem h4_Gtower (hQ : QElemCBounded) :
    (LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫ Gtower hQ =
      tensorOneMinusShift LightCondensed.P ≫ Work.ANALYTIC.FP := by
  haveI : Mono Work.ANALYTIC.cBounded := Work.ANALYTIC.mono_cBounded
  refine (cancel_mono Work.ANALYTIC.cBounded).mp ?_
  calc ((LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫ Gtower hQ) ≫ Work.ANALYTIC.cBounded
      = (LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫
          (Gtower hQ ≫ Work.ANALYTIC.cBounded) := Category.assoc _ _ _
    _ = (LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫
          (tensorOneMinusShift boundedSeq ≫ Work.ANALYTIC.truncF) := by
        rw [uncurry_gTheta_comp_cBounded hQ Work.ANALYTIC.truncF isTruncEAdata_truncF]
    _ = ((LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫
          tensorOneMinusShift boundedSeq) ≫ Work.ANALYTIC.truncF := (Category.assoc _ _ _).symm
    _ = (tensorOneMinusShift LightCondensed.P ≫
          (LightCondensed.P ◁ Work.ANALYTIC.cBounded)) ≫ Work.ANALYTIC.truncF := by
        rw [show (LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫
              tensorOneMinusShift boundedSeq =
              tensorOneMinusShift LightCondensed.P ≫
                (LightCondensed.P ◁ Work.ANALYTIC.cBounded) from
          whisker_exchange LightCondensed.oneMinusShift Work.ANALYTIC.cBounded]
    _ = tensorOneMinusShift LightCondensed.P ≫
          (Work.ANALYTIC.FP ≫ Work.ANALYTIC.cBounded) := by
        rw [Category.assoc, h3_truncF_FP]
    _ = (tensorOneMinusShift LightCondensed.P ≫ Work.ANALYTIC.FP) ≫
          Work.ANALYTIC.cBounded := (Category.assoc _ _ _).symm

/-- **The coefficient-extraction map `G : P ⊗ ∏^bnd ℤ ⟶ P` of REFS/03 §2 together with the two
identities of the scheme of REFS/03 §1 that involve it.**  Take `G` to be the null family
`(k,x) ↦ x_k·e_k`, i.e. `MonoidalClosed.uncurry (gTheta qElem_cBounded)` (defined in
`Submission/Work/ANALYTIC/exists_unprimedTower.lean`, whose statement imports
`Submission.Work.ANALYTIC.cBounded_solidEquiv`; the present claim is the same content in a module
that does *not*, so that the final assembly can use it without an import cycle).  The two
identities are `h₁ : T ≫ F = G ≫ cBounded` and `h₄ : (id_P ⊗ cBounded) ≫ G = ((1-S) ⊗ id_P) ≫ F'`,
where `F = truncF` is the truncation family and `F' = Work.ANALYTIC.FP` is the primed family. -/
theorem exists_Gtower_h1_h4 :
    ∃ G : LightCondensed.P ⊗ Work.ANALYTIC.boundedSeq ⟶ LightCondensed.P,
      (Work.ANALYTIC.tensorOneMinusShift Work.ANALYTIC.boundedSeq ≫
          Work.ANALYTIC.truncF = G ≫ Work.ANALYTIC.cBounded) ∧
        ((LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫ G =
          Work.ANALYTIC.tensorOneMinusShift LightCondensed.P ≫ Work.ANALYTIC.FP) :=
  ⟨Gtower qElem_cBounded,
    uncurry_gTheta_comp_cBounded qElem_cBounded Work.ANALYTIC.truncF isTruncEAdata_truncF,
    h4_Gtower qElem_cBounded⟩

end Work.ANALYTIC
