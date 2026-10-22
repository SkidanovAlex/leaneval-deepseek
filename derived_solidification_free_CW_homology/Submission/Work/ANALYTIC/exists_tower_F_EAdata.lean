import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.EA_natural
import Submission.Work.ANALYTIC.exists_realNullSeq
import Submission.Work.ANALYTIC.coordTimesDelta_mem_range
import Submission.Work.ANALYTIC.towerFEAsetup
import Submission.Work.REFL.pre_app_points
import Submission.Work.ATOM.zdesc
import Submission.Work.ATOM.projective_P
import Submission.Work.ATOM.Toolkit.PS_desc
import Submission.Work.ATOM.Toolkit.MonoidalPreadditive
import Submission.Work.ANALYTIC.truncDataElemNat
import Submission.Work.ANALYTIC.truncDataElemZeroSlice
import Submission.Work.ANALYTIC.zmapSymm
import Submission.Work.ANALYTIC.eaZeroSlice
import Submission.Work.ANALYTIC.genPointsExt
import Submission.Work.ANALYTIC.ihomPointsEval

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-!
## Structure of the proof

The map `F = truncF : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ` is `MonoidalClosed.uncurry` of the natural
transformation `truncTheta : ∏^bnd ℤ ⟶ (P ⟹ ∏^bnd ℤ)` whose `S`-points are the maps
`x ↦ truncPsi S x` of `Submission/Work/ANALYTIC/towerFEAsetup.lean` (the `PS_desc`-descent of the
morphism `truncPhi S x` classified by the truncation data `truncDataElem S x`, itself an element of
`∏^bnd ℤ((ℕ∪{∞}) × S)`).

* `truncThetaComp` is the `S`-component of `truncTheta`, exhibited as a linear map; its additivity
  and `ℤ`-linearity follow from the corresponding properties of `truncPsi` and of the point
  identification `LightCondensed.ihomPoints` (the lemmas `*_aux` in
  `Submission/Work/ANALYTIC/towerFEAsetup.lean`).
* Naturality of `truncTheta` in `S` is `Work.ANALYTIC.EA_natural` (moving `EA` past the induced
  map of free modules) together with the uniqueness in `Work.ATOM.Toolkit.PS_desc` and the
  compatibility of the truncation data with restriction (`Work.ANALYTIC.truncDataElemNat`).
* `IsTruncEAdata truncF` is then `PS_desc`'s characterizing identity `EA S ≫ ψ = φ`.
* `IsRetraction truncF` (the `k = 0` case of the truncation data) is `comp_sBoundedZ_truncF`,
  which combines `Work.ANALYTIC.EAZeroSlice` (the `0`-slice of `(ℕ∪{∞}) × S` descends to
  `e_0 ⊗ ℤ[S]`), `Work.ANALYTIC.truncDataElemZeroSlice` (the `0`-slice of `truncDataElem S x` is
  `x`), `Work.ANALYTIC.IhomPointsEval` (the value of an internal-hom point at a section is the
  uncurrying of the composite) and `Work.ANALYTIC.GenPointsExt` (endomorphisms of `∏^bnd ℤ` are
  detected by the generalized points `ℤ[S] ⟶ ∏^bnd ℤ`).
-/

/-! ## The morphism `θF : ∏^bnd ℤ ⟶ (P ⟹ ∏^bnd ℤ)`

Its `S`-points are the maps `x ↦ truncPsi S x` (the descent of `truncPhi S x` along `EA S`), i.e.
the family of truncations in the form of a null family indexed by `ℕ∪{∞}`. -/

/-- The `S`-component of `θF`, as a linear map: `x ↦ truncPsi S x`, transported across the
identification of the points of the internal hom with the uncurried morphisms. -/
noncomputable def truncThetaComp (S : (LightProfinite.{0})ᵒᵖ) :
    ↥(boundedSeq.obj.obj S) →ₗ[ℤ]
      ↥(((ihom LightCondensed.P).obj boundedSeq).obj.obj S) where
  toFun := fun x =>
    (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S.unop).symm (truncPsi S.unop x)
  map_add' := fun x y => by rw [truncPsi_add, ihomPoints_symm_add_aux]
  map_smul' := fun c x => by
    rw [truncPsi_smul, ihomPoints_symm_zsmul_aux]
    exact (int_smul_eq_zsmul
      ((((ihom LightCondensed.P).obj boundedSeq).obj.obj S).isModule) c _).symm
/-- **The natural transformation `θF`.**  Its `S`-point sends `x ∈ ∏^bnd ℤ(S)` to the morphism
`P ⊗ ℤ[S] ⟶ ∏^bnd ℤ` whose null family is the family of truncations `π_{≥k}`. -/
noncomputable def truncTheta : boundedSeq ⟶ (ihom LightCondensed.P).obj boundedSeq :=
  ObjectProperty.homMk
    { app := fun S => ModuleCat.ofHom (truncThetaComp S)
      naturality := by
        intro S T g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have key : truncPsi T.unop (boundedSeq.obj.map g x)
            = MonoidalCategory.whiskerLeft LightCondensed.P (Work.ATOM.zmap g.unop)
              ≫ truncPsi S.unop x := by
          have h : Work.ATOM.EA T.unop
              ≫ (MonoidalCategory.whiskerLeft LightCondensed.P (Work.ATOM.zmap g.unop)
                  ≫ truncPsi S.unop x) = truncPhi T.unop (boundedSeq.obj.map g x) := by
            rw [← Category.assoc, EA_natural g.unop, Category.assoc, truncPsi_spec]
            rw [show truncPhi S.unop x
                = (Work.ATOM.homFreeEquiv (Work.ATOM.NS S.unop) boundedSeq).symm
                    (truncDataElem S.unop x) from rfl]
            rw [zmapSymm boundedSeq (Work.ATOM.NS T.unop) (Work.ATOM.NS S.unop)
              (MonoidalCategory.whiskerLeft (ℕ∪{∞}) g.unop) (truncDataElem S.unop x)]
            rw [truncDataElemNat T.unop S.unop g.unop x]
            rfl
          exact (eq_truncPsi T.unop (boundedSeq.obj.map g x) h).symm
        rw [show (ModuleCat.Hom.hom (boundedSeq.obj.map g ≫ ModuleCat.ofHom (truncThetaComp T))) x
            = (truncThetaComp T) ((boundedSeq.obj.map g) x) from rfl]
        rw [show (ModuleCat.Hom.hom (ModuleCat.ofHom (truncThetaComp S)
              ≫ ((ihom LightCondensed.P).obj boundedSeq).obj.map g)) x
            = (((ihom LightCondensed.P).obj boundedSeq).obj.map g) ((truncThetaComp S) x)
          from rfl]
        rw [show (truncThetaComp T) ((boundedSeq.obj.map g) x)
            = (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq T.unop).symm
                (truncPsi T.unop (boundedSeq.obj.map g x)) from rfl]
        rw [show (truncThetaComp S) x
            = (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S.unop).symm
                (truncPsi S.unop x) from rfl]
        rw [show (((ihom LightCondensed.P).obj boundedSeq).obj.map g)
              ((LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S.unop).symm
                (truncPsi S.unop x))
            = (((ihom LightCondensed.P).obj boundedSeq).obj.map (g.unop).op)
                ((LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S.unop).symm
                  (truncPsi S.unop x)) from rfl]
        rw [key]
        exact LightCondensed.ihomPoints_symm_comp ℤ boundedSeq LightCondensed.P T.unop S.unop
          g.unop (truncPsi S.unop x) }

/-- The `S`-point of `θF` at `x`, in the form used downstream. -/
theorem truncTheta_app (S : (LightProfinite.{0})ᵒᵖ) (x : ↥(boundedSeq.obj.obj S)) :
    truncTheta.hom.app S x
      = (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S.unop).symm
          (truncPsi S.unop x) :=
  rfl

/-! ## The map `F = uncurry θF` and its truncation data -/

/-- **The truncation tower `F : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ`** of REFS/03 §2, as the uncurrying of
`truncTheta`. -/
noncomputable def truncF : Work.ATOM.tmul LightCondensed.P boundedSeq ⟶ boundedSeq :=
  MonoidalClosed.uncurry truncTheta

/-- `curry truncF = truncTheta`. -/
theorem curry_truncF : MonoidalClosed.curry truncF = truncTheta :=
  MonoidalClosed.curry_uncurry _

/-- **The truncation data of `truncF` in the `EA`-form.** -/
theorem isTruncEAdata_truncF : IsTruncEAdata truncF := by
  intro S x
  have h : (MonoidalClosed.curry truncF).hom.app (Opposite.op S) x
      = (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S).symm (truncPsi S x) := by
    rw [curry_truncF, truncTheta_app]
  rw [h, Equiv.apply_symm_apply, truncPsi_spec]
  rfl

/-! ## `truncF` is a retraction of `s = e_0 ⊗ -` -/

/-- **The key computation of the retraction.**  For every generalized point `g : ℤ[S] ⟶ ∏^bnd ℤ`,
the composite `g ≫ s ≫ F` is `g`: this is the `k = 0` case of the truncation data, combined with
the coherence `Work.ANALYTIC.EAZeroSlice` (the `0`-slice `ℤ[S] ⟶ ℤ[(ℕ∪{∞}) × S]` descends to
`e_0 ⊗ ℤ[S]`). -/
theorem comp_sBoundedZ_truncF (S : LightProfinite.{0})
    (g : Work.ATOM.zfree S ⟶ boundedSeq) :
    g ≫ (sBoundedZ ≫ truncF) = g := by
  set x : ↥(boundedSeq.obj.obj (Opposite.op S)) :=
    Work.ATOM.homFreeEquiv S boundedSeq g with hx
  have hg : (Work.ATOM.homFreeEquiv S boundedSeq).symm x = g := by
    rw [hx, Equiv.symm_apply_apply]
  have h1 : g ≫ (λ_ boundedSeq).inv = (λ_ (Work.ATOM.zfree S)).inv ≫ (𝟙_ LightCondAb ◁ g) := by
    rw [id_whiskerLeft, Iso.inv_hom_id_assoc]
  have h2 : (𝟙_ LightCondAb ◁ g) ≫ ((ePointZ 0 ▷ boundedSeq) ≫ MonoidalClosed.uncurry truncTheta)
      = (ePointZ 0 ▷ Work.ATOM.zfree S)
        ≫ ((LightCondensed.P ◁ g) ≫ MonoidalClosed.uncurry truncTheta) := by
    rw [← Category.assoc, whisker_exchange (ePointZ 0) g, Category.assoc]
  have h3 : (LightCondensed.P ◁ g) ≫ MonoidalClosed.uncurry truncTheta
      = MonoidalClosed.uncurry (g ≫ truncTheta) :=
    (MonoidalClosed.uncurry_natural_left g truncTheta).symm
  have h4 : MonoidalClosed.uncurry (g ≫ truncTheta) = truncPsi S x := by
    rw [← ihomPointsEval LightCondensed.P boundedSeq boundedSeq truncTheta S g, ← hx,
      truncTheta_app]
    exact Equiv.apply_symm_apply _ _
  calc g ≫ (sBoundedZ ≫ truncF)
      = (g ≫ (λ_ boundedSeq).inv)
          ≫ ((ePointZ 0 ▷ boundedSeq) ≫ MonoidalClosed.uncurry truncTheta) := by
        rw [sBoundedZ, truncF]
        simp only [Category.assoc]
    _ = ((λ_ (Work.ATOM.zfree S)).inv ≫ (𝟙_ LightCondAb ◁ g))
          ≫ ((ePointZ 0 ▷ boundedSeq) ≫ MonoidalClosed.uncurry truncTheta) := by
        rw [h1]
    _ = (λ_ (Work.ATOM.zfree S)).inv
          ≫ ((𝟙_ LightCondAb ◁ g)
            ≫ ((ePointZ 0 ▷ boundedSeq) ≫ MonoidalClosed.uncurry truncTheta)) := by
        simp only [Category.assoc]
    _ = (λ_ (Work.ATOM.zfree S)).inv
          ≫ ((ePointZ 0 ▷ Work.ATOM.zfree S)
            ≫ ((LightCondensed.P ◁ g) ≫ MonoidalClosed.uncurry truncTheta)) := by
        rw [h2]
    _ = (λ_ (Work.ATOM.zfree S)).inv
          ≫ ((ePointZ 0 ▷ Work.ATOM.zfree S) ≫ MonoidalClosed.uncurry (g ≫ truncTheta)) := by
        rw [h3]
    _ = (λ_ (Work.ATOM.zfree S)).inv
          ≫ ((ePointZ 0 ▷ Work.ATOM.zfree S) ≫ truncPsi S x) := by
        rw [h4]
    _ = ((λ_ (Work.ATOM.zfree S)).inv ≫ (ePointZ 0 ▷ Work.ATOM.zfree S)) ≫ truncPsi S x := by
        simp only [Category.assoc]
    _ = (Work.ATOM.zmap (zeroSlice S) ≫ Work.ATOM.EA S) ≫ truncPsi S x := by
        rw [eaZeroSlice S]
    _ = Work.ATOM.zmap (zeroSlice S) ≫ (Work.ATOM.EA S ≫ truncPsi S x) := by
        simp only [Category.assoc]
    _ = Work.ATOM.zmap (zeroSlice S) ≫ truncPhi S x := by
        rw [truncPsi_spec]
    _ = (Work.ATOM.homFreeEquiv S boundedSeq).symm
          (boundedSeq.obj.map (zeroSlice S).op (truncDataElem S x)) :=
        zmapSymm boundedSeq S (Work.ATOM.NS S) (zeroSlice S) (truncDataElem S x)
    _ = (Work.ATOM.homFreeEquiv S boundedSeq).symm x := by
        rw [truncDataElemZeroSlice S x]
    _ = g := hg

/-- **`truncF` is a retraction of `s = e_0 ⊗ -`.** -/
theorem isRetraction_truncF : IsRetraction truncF :=
  genPointsExt _ _ comp_sBoundedZ_truncF

/-- **Existence of `F` in the `EA`-form of the truncation data.**  There is
`F : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ` which is a retraction of `s = e_0 ⊗ -`
(`Work.ANALYTIC.IsRetraction F`) and whose null family is the family of truncations in the
`EA`-form `Work.ANALYTIC.IsTruncEAdata F`: for every light profinite `S` and every
`x ∈ ∏^bnd ℤ(S)`, the composite `EA S ≫ θF_S(x)` (where `θF = curry F` and `θF_S(x)` is the
`S`-point, i.e. the map `P ⊗ ℤ[S] ⟶ ∏^bnd ℤ` obtained by `ihomPoints`) equals the morphism
`ℤ[(ℕ∪∞) × S] ⟶ ∏^bnd ℤ` corresponding to the element `Work.ANALYTIC.truncDataElem S x`, whose
`m`-th component is `(k,s) ↦ x_m(s)·[k ≤ m]`.

This is the shape in which `F` is used to assemble `(ii)` (`T ≫ F = G ≫ cBounded`):
applying `EA S` turns the `S`-points of `T = (1-S) ⊗ id` composed with `F` into the element
`(m,(k,s)) ↦ x_m(s)·[k = m]`, which is `Work.ANALYTIC.coordTimesDeltaAt` for the test object
`(ℕ∪∞) × S`, the pullback of `x` and `f = pr₁`, and that element lies in the image of `cBounded`
(`Work.ANALYTIC.coordTimesDeltaAt_mem_range`), supplying the required `G`.

Route: define, for each `S` and `x`, the map `ψ_S(x) : P ⊗ ℤ[S] ⟶ ∏^bnd ℤ` as the `PS_desc`
descent of the map classified by `truncDataElem S x` (its `m`-th component vanishes at `k = ∞`);
naturality in `S` follows from `EA_natural` + the uniqueness in `PS_desc`, and additivity in `x`
from linearity, so `x ↦ ψ_S(x)` is the `S`-point of `θF : ∏^bnd ℤ ⟶ (P ⟹ ∏^bnd ℤ)`, and
`F := MonoidalClosed.uncurry θF`.  Then `IsTruncEAdata F` is `PS_desc`'s identity
`EA S ≫ ψ = φ`.  (`IsTruncTower F` is the sibling statement `Work.ANALYTIC.exists_tower_F`; the
two are inter-derivable, so prove the `EA`-form here and do not fund both independently.  A
partial result that delivers only the construction of `F` and `IsTruncEAdata F` is still useful:
report such a state in the file's documentation rather than leaving `sorry`.) -/
theorem exists_tower_F_EAdata :
    ∃ F : Work.ATOM.tmul LightCondensed.P Work.ANALYTIC.boundedSeq ⟶ Work.ANALYTIC.boundedSeq,
      Work.ANALYTIC.IsRetraction F ∧ Work.ANALYTIC.IsTruncEAdata F :=
  ⟨truncF, isRetraction_truncF, isTruncEAdata_truncF⟩

end

end Work.ANALYTIC
