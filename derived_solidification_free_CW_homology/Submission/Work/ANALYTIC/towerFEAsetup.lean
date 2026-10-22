import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.EA_natural
import Submission.Work.ANALYTIC.exists_realNullSeq
import Submission.Work.ANALYTIC.coordTimesDelta_mem_range
import Submission.Work.REFL.pre_app_points
import Submission.Work.ATOM.zdesc
import Submission.Work.ATOM.projective_P
import Submission.Work.ATOM.Toolkit.PS_desc
import Submission.Work.ATOM.Toolkit.MonoidalPreadditive

/-!
# Setup for the `EA`-form of the truncation tower `F` (`Work.ANALYTIC.exists_tower_F_EAdata`)

The target is the existence of `F : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ` which is a retraction of
`s = e_0 ⊗ -` and whose "null family" is the family of truncations, stated in the `EA`-form
`Work.ANALYTIC.IsTruncEAdata`.

This file collects the definitions used by the proof (and by the lemmas delegated for it):

* `zeroSlice S : S ⟶ (ℕ∪{∞}) × S`, the slice `s ↦ (0,s)`;
* `truncPhi S x`, the morphism `ℤ[(ℕ∪{∞}) × S] ⟶ ∏^bnd ℤ` classified by `truncDataElem S x`
  (`Work.ANALYTIC.truncDataElem` of `Submission/Work/ANALYTIC/unprimedSetup.lean`);
* `truncPhi_infty`, the vanishing of `truncPhi S x` on the `∞`-slice `{∞} × S` — this is what
  makes it descend along `EA S`;
* `truncPsi S x`, the descent of `truncPhi S x` to `P ⊗ ℤ[S] ⟶ ∏^bnd ℤ` (obtained from
  `Work.ATOM.Toolkit.PS_desc`), with its two characterizing properties `truncPsi_spec` (the
  identity `EA S ≫ truncPsi S x = truncPhi S x`) and `eq_truncPsi` (uniqueness);

and the `Prop`-valued statements of the auxiliary lemmas delegated for the proof:

* `TruncDataElemNat` — compatibility of `truncDataElem` with restriction in the light profinite
  variable;
* `TruncDataElemZeroSlice` — the zero slice of `truncDataElem S x` is `x`;
* `ZmapSymm` — naturality of the inverse of `homFreeEquiv` under `zmap`;
* `FreeHomEquivSmul` — `ℤ`-linearity of `homFreeEquiv`;
* `EAZeroSlice` — the coherence `(λ_ ℤ[S])⁻¹ ≫ (e_0 ▷ ℤ[S]) = zmap (zeroSlice S) ≫ EA S`;
* `IhomPointsEval` — `ihomPoints` applied to the value of a morphism into an internal hom at a
  section is the uncurrying of the composite;
* `GenPointsExt` — morphisms `∏^bnd ℤ ⟶ ∏^bnd ℤ` are determined by their values on the
  generalized points `ℤ[S] ⟶ ∏^bnd ℤ`.

The mathematical route of the main proof is recorded in
`Submission/Work/ANALYTIC/exists_tower_F_EAdata.lean`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-! ## Wrappers for the `freeHomEquiv` API in the `Work.ATOM.homFreeEquiv` flavour

The two functions are definitionally equal, but rewriting is fragile under the transparency option
below, so the versions used in the statements are recorded here explicitly.  The pointwise
evaluation lemmas (`boundedSeq_map_apply`, `coe_add_apply`, `coe_smul_apply`, `coe_zero_apply`,
`coe_add_eq`, `coe_smul_eq`, `coe_zero_eq`) and `freeHomEquiv_zsmul` are imported from
`Submission/Work/ANALYTIC/coordTimesDelta_mem_range.lean`. -/

/-- Wrapper for `Work.ANALYTIC.freeHomEquiv_zero`. -/
theorem homFreeEquiv_zero' (S : LightProfinite.{0}) (A : LightCondAb) :
    Work.ATOM.homFreeEquiv S A 0 = 0 :=
  Work.ANALYTIC.freeHomEquiv_zero S A

/-- Wrapper for `Work.ANALYTIC.freeHomEquiv_add`. -/
theorem homFreeEquiv_add' (S : LightProfinite.{0}) (A : LightCondAb)
    (a b : Work.ATOM.zfree S ⟶ A) :
    Work.ATOM.homFreeEquiv S A (a + b)
      = Work.ATOM.homFreeEquiv S A a + Work.ATOM.homFreeEquiv S A b :=
  Work.ANALYTIC.freeHomEquiv_add S A a b

/-- Wrapper for `Work.ANALYTIC.freeHomEquiv_zsmul`. -/
theorem homFreeEquiv_zsmul' (S : LightProfinite.{0}) (A : LightCondAb) (c : ℤ)
    (g : Work.ATOM.zfree S ⟶ A) :
    Work.ATOM.homFreeEquiv S A (c • g) = c • Work.ATOM.homFreeEquiv S A g :=
  Work.ANALYTIC.freeHomEquiv_zsmul S A c g

/-! ## The zero slice `s ↦ (0,s)` -/

/-- The slice `S ⟶ (ℕ∪{∞}) ⊗ S`, `s ↦ (0,s)`. -/
def zeroSlice (S : LightProfinite.{0}) : S ⟶ Work.ATOM.NS S :=
  (λ_ S).inv ≫ (Work.ATOM.ptAt (S := (ℕ∪{∞})) (((0 : ℕ) : ℕ∪{∞})) ▷ S)

/-- The zero slice is `s ↦ (0,s)` on points. -/
theorem zeroSlice_apply (S : LightProfinite.{0}) (s : ↥S) :
    zeroSlice S s = ((((0 : ℕ) : ℕ∪{∞})), s) := by
  have h : (λ_ S).hom ((λ_ S).inv s) = s := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  have h2 : ((λ_ S).inv s).2 = s := by
    simpa only [show ∀ q : ↥(𝟙_ LightProfinite ⊗ S), (λ_ S).hom q = q.2 from fun q => rfl] using h
  show (Work.ATOM.ptAt (S := (ℕ∪{∞})) (((0 : ℕ) : ℕ∪{∞})) ▷ S) ((λ_ S).inv s) = _
  have hp : (λ_ S).inv s = (((λ_ S).inv s).1, s) := Prod.ext rfl h2
  rw [hp]
  rfl

/-! ## The morphism `ℤ[(ℕ∪{∞}) × S] ⟶ ∏^bnd ℤ` classified by `truncDataElem` -/

/-- The morphism `ℤ[(ℕ∪{∞}) × S] ⟶ ∏^bnd ℤ` whose section over `(ℕ∪{∞}) × S` is
`truncDataElem S x`, i.e. whose `m`-th component is `(k,s) ↦ x_m(s)·[k ≤ m]`. -/
noncomputable def truncPhi (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zfree (Work.ATOM.NS S) ⟶ boundedSeq :=
  (Work.ATOM.homFreeEquiv (Work.ATOM.NS S) boundedSeq).symm (truncDataElem S x)

/-- `truncPhi` is classified by `truncDataElem`. -/
theorem homFreeEquiv_truncPhi (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.homFreeEquiv (Work.ATOM.NS S) boundedSeq (truncPhi S x) = truncDataElem S x :=
  Equiv.apply_symm_apply _ _

/-! ### Additivity of the `truncDataElem` family

These are pointwise computations on the concrete sections of `∏^bnd ℤ`. -/

theorem truncDataElem_add (S : LightProfinite.{0})
    (x y : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    truncDataElem S (x + y) = truncDataElem S x + truncDataElem S y := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  rw [coe_add_apply (Work.ATOM.NS S) (truncDataElem S x) (truncDataElem S y) m p, truncDataElem_val,
    truncDataElem_val, truncDataElem_val,
    coe_add_apply S x y m p.2]
  ring

theorem truncDataElem_smul (S : LightProfinite.{0}) (c : ℤ)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    truncDataElem S (c • x) = c • truncDataElem S x := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  rw [coe_smul_apply (Work.ATOM.NS S) c (truncDataElem S x) m p, truncDataElem_val, truncDataElem_val,
    coe_smul_apply S c x m p.2]
  ring

theorem truncDataElem_zero (S : LightProfinite.{0}) :
    truncDataElem S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) = 0 := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  rw [coe_zero_apply (Work.ATOM.NS S) m p, truncDataElem_val, coe_zero_apply S m p.2]
  ring

/-! ### The `∞`-slice of `truncDataElem` -/

/-- The element `truncDataElem S x` vanishes on the `∞`-slice `{∞} × S` (its `m`-th component is
`x_m(s)·[k ≤ m]`, and `[∞ ≤ m] = 0`). -/
theorem map_whiskerRight_iota_truncDataElem (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    boundedSeq.obj.map (MonoidalCategory.whiskerRight LightCondensed.ι S).op
      (truncDataElem S x) = 0 := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  rw [boundedSeq_map_apply,
    show (MonoidalCategory.whiskerRight LightCondensed.ι S) p
      = (((∞ : ℕ∪{∞})), p.2) from rfl,
    truncDataElem_val, coe_zero_apply]
  have hprod : (∏ i ∈ Finset.range (m + 1), (1 - deltaFun i (∞ : ℕ∪{∞}))) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rw [deltaFun_infty]
    ring
  rw [hprod]
  ring

/-- **Vanishing of `truncPhi` on the `∞`-slice**: this is the hypothesis of
`Work.ATOM.Toolkit.PS_desc` which makes `truncPhi S x` descend to `P ⊗ ℤ[S]`. -/
theorem truncPhi_infty (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫ truncPhi S x = 0 := by
  apply (Work.ATOM.homFreeEquiv (Work.ATOM.pt ⊗ S) boundedSeq).injective
  rw [Work.ATOM.homFreeEquiv_naturality, homFreeEquiv_truncPhi,
    map_whiskerRight_iota_truncDataElem]
  exact (Work.ANALYTIC.freeHomEquiv_zero (Work.ATOM.pt ⊗ S) boundedSeq).symm

/-! ## The descent `truncPsi S x : P ⊗ ℤ[S] ⟶ ∏^bnd ℤ` -/

/-- The descent of `truncPhi S x` along `EA S`, i.e. the `S`-point of `curry F` at `x`
(at the level of morphisms). -/
noncomputable def truncPsi (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ boundedSeq :=
  (Work.ATOM.Toolkit.PS_desc S (truncPhi S x) (truncPhi_infty S x)).choose

/-- The characterizing property of `truncPsi`. -/
theorem truncPsi_spec (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.EA S ≫ truncPsi S x = truncPhi S x :=
  (Classical.choose_spec (Work.ATOM.Toolkit.PS_desc S (truncPhi S x) (truncPhi_infty S x))).1

/-- Uniqueness of the descent: a morphism whose composite with `EA S` is `truncPhi S x` equals
`truncPsi S x`. -/
theorem eq_truncPsi (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S)))
    {ψ : Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ boundedSeq}
    (h : Work.ATOM.EA S ≫ ψ = truncPhi S x) : ψ = truncPsi S x :=
  (Classical.choose_spec (Work.ATOM.Toolkit.PS_desc S (truncPhi S x) (truncPhi_infty S x))).2 ψ h

/-! ## Linearity of `truncPhi` and `truncPsi` -/

theorem truncPhi_add (S : LightProfinite.{0})
    (x y : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    truncPhi S (x + y) = truncPhi S x + truncPhi S y := by
  apply (Work.ATOM.homFreeEquiv (Work.ATOM.NS S) boundedSeq).injective
  rw [homFreeEquiv_truncPhi, truncDataElem_add, homFreeEquiv_add', homFreeEquiv_truncPhi,
    homFreeEquiv_truncPhi]

theorem truncPhi_smul (S : LightProfinite.{0}) (c : ℤ)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    truncPhi S (c • x) = c • truncPhi S x := by
  apply (Work.ATOM.homFreeEquiv (Work.ATOM.NS S) boundedSeq).injective
  rw [homFreeEquiv_truncPhi, truncDataElem_smul, homFreeEquiv_zsmul', homFreeEquiv_truncPhi]

theorem truncPhi_zero (S : LightProfinite.{0}) :
    truncPhi S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) = 0 := by
  apply (Work.ATOM.homFreeEquiv (Work.ATOM.NS S) boundedSeq).injective
  rw [homFreeEquiv_truncPhi, truncDataElem_zero, homFreeEquiv_zero']

theorem truncPsi_add (S : LightProfinite.{0})
    (x y : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    truncPsi S (x + y) = truncPsi S x + truncPsi S y := by
  have h : Work.ATOM.EA S ≫ (truncPsi S x + truncPsi S y) = truncPhi S (x + y) := by
    rw [Preadditive.comp_add, truncPsi_spec, truncPsi_spec, truncPhi_add]
  exact (eq_truncPsi S (x + y) h).symm

theorem truncPsi_smul (S : LightProfinite.{0}) (c : ℤ)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    truncPsi S (c • x) = c • truncPsi S x := by
  have h : Work.ATOM.EA S ≫ (c • truncPsi S x) = truncPhi S (c • x) := by
    rw [Preadditive.comp_zsmul, truncPsi_spec, truncPhi_smul]
  exact (eq_truncPsi S (c • x) h).symm

theorem truncPsi_zero (S : LightProfinite.{0}) :
    truncPsi S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) = 0 := by
  have h : Work.ATOM.EA S ≫ (0 : Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S)
      ⟶ boundedSeq) = truncPhi S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) := by
    rw [comp_zero, truncPhi_zero]
  exact (eq_truncPsi S 0 h).symm

/-! ## The statements of the auxiliary lemmas delegated for the proof -/

/-- **Compatibility of `truncDataElem` with restriction.**  For `f : T ⟶ S` and `x ∈ ∏^bnd ℤ(S)`,
the pullback of `truncDataElem S x` along `(ℕ∪{∞}) × f` is `truncDataElem T (x|_T)`. -/
def TruncDataElemNat : Prop :=
  ∀ (T S : LightProfinite.{0}) (f : T ⟶ S)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))),
    boundedSeq.obj.map (MonoidalCategory.whiskerLeft (ℕ∪{∞}) f).op
        (truncDataElem S x)
      = truncDataElem T (boundedSeq.obj.map f.op x)

/-- **The zero slice of `truncDataElem S x` is `x`.**  The `m`-th component of `truncDataElem S x`
at `(0,s)` is `x_m(s)·[0 ≤ m] = x_m(s)`. -/
def TruncDataElemZeroSlice : Prop :=
  ∀ (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (Opposite.op S))),
    boundedSeq.obj.map (zeroSlice S).op (truncDataElem S x) = x

/-- **Naturality of the inverse of `homFreeEquiv`.**  Pulling back the morphism classified by `a`
along `zmap f` gives the morphism classified by the pullback of `a`. -/
def ZmapSymm : Prop :=
  ∀ (M : LightCondAb) (T S : LightProfinite.{0}) (f : T ⟶ S)
    (a : ↥(M.obj.obj (Opposite.op S))),
    Work.ATOM.zmap f ≫ (Work.ATOM.homFreeEquiv S M).symm a
      = (Work.ATOM.homFreeEquiv T M).symm (M.obj.map f.op a)

/-- **`ℤ`-linearity of `homFreeEquiv`.**  (Additivity is a special case of this together with the
fact that the two sides of the equivalence are `ℤ`-modules.) -/
def FreeHomEquivSmul : Prop :=
  ∀ (M : LightCondAb) (S : LightProfinite.{0}) (c : ℤ)
    (g : Work.ATOM.zfree S ⟶ M),
    Work.ATOM.homFreeEquiv S M (c • g) = c • Work.ATOM.homFreeEquiv S M g

/-- **The `EA`-coherence of the zero slice with the point `e_0` of `P`.**  Descending the zero
slice `ℤ[S] ⟶ ℤ[(ℕ∪{∞}) × S]` along `EA S` gives the point `e_0` of `P` tensored with the
identity: the free module `ℤ[S]` sits in `P ⊗ ℤ[S]` as `e_0 ⊗ ℤ[S]`. -/
def EAZeroSlice : Prop :=
  ∀ S : LightProfinite.{0},
    (λ_ (Work.ATOM.zfree S)).inv ≫ (ePointZ 0 ▷ Work.ATOM.zfree S)
      = Work.ATOM.zmap (zeroSlice S) ≫ Work.ATOM.EA S

/-- **The evaluation of the points of an internal hom.**  For `u : X ⟶ ihom A M`, a light
profinite set `S` and `g : ℤ[S] ⟶ X`, the `S`-point of `u` at the section classified by `g` is
the uncurrying of `g ≫ u`. -/
def IhomPointsEval : Prop :=
  ∀ (A M X : LightCondAb) (u : X ⟶ (ihom A).obj M) (S : LightProfinite.{0})
    (g : Work.ATOM.zfree S ⟶ X),
    LightCondensed.ihomPoints ℤ A M S
        (u.hom.app (Opposite.op S) (Work.ATOM.homFreeEquiv S X g))
      = MonoidalClosed.uncurry (g ≫ u)

/-- **Extensionality along generalized points.**  A morphism `∏^bnd ℤ ⟶ ∏^bnd ℤ` is determined by
its values on the generalized points `ℤ[S] ⟶ ∏^bnd ℤ` (`S` light profinite). -/
def GenPointsExt : Prop :=
  ∀ (u v : boundedSeq ⟶ boundedSeq),
    (∀ (S : LightProfinite.{0}) (g : Work.ATOM.zfree S ⟶ boundedSeq), g ≫ u = g ≫ v) → u = v

/-! ## Linearity of `curry`/`uncurry` and of the point identification

The `S`-points of the internal hom `P ⟹ ∏^bnd ℤ` are the morphisms `P ⊗ ℤ[S] ⟶ ∏^bnd ℤ`
(`LightCondensed.ihomPoints`); this section collects the (elementary) linearity of the two
comparison isomorphisms involved, which is what makes the family `x ↦ truncPsi S x` into a morphism
of sheaves of modules. -/

/-- Pointwise evaluation of the scalar multiple of a morphism of light condensed abelian groups
(using the canonical `ℤ`-module structure on the target). -/
theorem hom_zsmul_apply_aux {M N : LightCondAb} (c : ℤ) (f : M ⟶ N)
    (S : (LightProfinite.{0})ᵒᵖ) (x : ↥(M.obj.obj S)) :
    ((c • f).hom.app S) x = c • (f.hom.app S x) := by
  rw [show (c • f).hom.app S = c • f.hom.app S from rfl]
  rfl

/-- Uncurrying is additive. -/
theorem uncurry_add_aux {A X Y : LightCondAb} (f g : X ⟶ (ihom A).obj Y) :
    MonoidalClosed.uncurry (f + g) = MonoidalClosed.uncurry f + MonoidalClosed.uncurry g := by
  rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]

/-- Uncurrying commutes with integer scalar multiples. -/
theorem uncurry_zsmul_aux {A X Y : LightCondAb} (c : ℤ) (f : X ⟶ (ihom A).obj Y) :
    MonoidalClosed.uncurry (c • f) = c • MonoidalClosed.uncurry f := by
  rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq]
  have h : A ◁ (c • f) = c • (A ◁ f) := (tensorLeft A).map_zsmul
  rw [h, Preadditive.zsmul_comp]

/-- Currying is additive. -/
theorem curry_add_aux {A X Y : LightCondAb} (f g : A ⊗ X ⟶ Y) :
    MonoidalClosed.curry (f + g) = MonoidalClosed.curry f + MonoidalClosed.curry g :=
  MonoidalClosed.uncurry_injective (by
    rw [MonoidalClosed.uncurry_curry, uncurry_add_aux, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_curry])

/-- Currying commutes with integer scalar multiples. -/
theorem curry_zsmul_aux {A X Y : LightCondAb} (c : ℤ) (f : A ⊗ X ⟶ Y) :
    MonoidalClosed.curry (c • f) = c • MonoidalClosed.curry f :=
  MonoidalClosed.uncurry_injective (by
    rw [MonoidalClosed.uncurry_curry, uncurry_zsmul_aux, MonoidalClosed.uncurry_curry])

/-- Currying the zero morphism gives zero. -/
theorem curry_zero_aux {A X Y : LightCondAb} :
    MonoidalClosed.curry (0 : A ⊗ X ⟶ Y) = 0 := by
  rw [MonoidalClosed.curry_eq]
  simp

/-- Uncurrying the zero morphism gives zero. -/
theorem uncurry_zero_aux {A X Y : LightCondAb} :
    MonoidalClosed.uncurry (0 : X ⟶ (ihom A).obj Y) = 0 := by
  rw [MonoidalClosed.uncurry_eq, MonoidalPreadditive.whiskerLeft_zero, zero_comp]

/-- The inverse of `Work.ATOM.homFreeEquiv` is additive. -/
theorem homFreeEquiv_symm_add_aux (M : LightCondAb) (S : LightProfinite.{0})
    (a b : ↥(M.obj.obj (Opposite.op S))) :
    (Work.ATOM.homFreeEquiv S M).symm (a + b)
      = (Work.ATOM.homFreeEquiv S M).symm a + (Work.ATOM.homFreeEquiv S M).symm b := by
  apply (Work.ATOM.homFreeEquiv S M).injective
  rw [Equiv.apply_symm_apply, homFreeEquiv_add', Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- The inverse of `Work.ATOM.homFreeEquiv` commutes with integer scalar multiples. -/
theorem homFreeEquiv_symm_zsmul_aux (M : LightCondAb) (S : LightProfinite.{0}) (c : ℤ)
    (a : ↥(M.obj.obj (Opposite.op S))) :
    (Work.ATOM.homFreeEquiv S M).symm (c • a)
      = c • (Work.ATOM.homFreeEquiv S M).symm a := by
  apply (Work.ATOM.homFreeEquiv S M).injective
  rw [Equiv.apply_symm_apply, homFreeEquiv_zsmul', Equiv.apply_symm_apply]

/-- **The `S`-point of the internal hom, as a function of the uncurried morphism.**  The inverse
of `LightCondensed.ihomPoints` at a morphism `w : A ⊗ ℤ[S] ⟶ B` is obtained by currying `w` and
evaluating the result at the `S`-section `secUnit S` of `ℤ[S]`. -/
theorem ihomPoints_symm_apply_aux {A B : LightCondAb} (S : LightProfinite.{0})
    (w : A ⊗ Work.ATOM.zfree S ⟶ B) :
    (LightCondensed.ihomPoints ℤ A B S).symm w
      = (MonoidalClosed.curry w).hom.app (Opposite.op S) (secUnit S) := by
  rw [LightCondensed.ihomPoints_symm_apply]
  exact Work.ANALYTIC.freeHomEquiv_eq S ((ihom A).obj B) (MonoidalClosed.curry w)

/-- Additivity of the inverse of `LightCondensed.ihomPoints`. -/
theorem ihomPoints_symm_add_aux {A B : LightCondAb} (S : LightProfinite.{0})
    (x y : A ⊗ Work.ATOM.zfree S ⟶ B) :
    (LightCondensed.ihomPoints ℤ A B S).symm (x + y)
      = (LightCondensed.ihomPoints ℤ A B S).symm x
        + (LightCondensed.ihomPoints ℤ A B S).symm y := by
  rw [ihomPoints_symm_apply_aux, ihomPoints_symm_apply_aux, ihomPoints_symm_apply_aux,
    curry_add_aux, Sheaf.Hom.add_app]
  exact moduleCat_hom_add_apply _ _ (secUnit S)

/-- Compatibility of the inverse of `LightCondensed.ihomPoints` with integer scalar multiples. -/
theorem ihomPoints_symm_zsmul_aux {A B : LightCondAb} (S : LightProfinite.{0}) (c : ℤ)
    (x : A ⊗ Work.ATOM.zfree S ⟶ B) :
    (LightCondensed.ihomPoints ℤ A B S).symm (c • x)
      = c • (LightCondensed.ihomPoints ℤ A B S).symm x := by
  rw [ihomPoints_symm_apply_aux, ihomPoints_symm_apply_aux, curry_zsmul_aux]
  exact hom_zsmul_apply_aux c _ (Opposite.op S) (secUnit S)

/-- The inverse of `LightCondensed.ihomPoints` at zero is zero. -/
theorem ihomPoints_symm_zero_aux {A B : LightCondAb} (S : LightProfinite.{0}) :
    (LightCondensed.ihomPoints ℤ A B S).symm (0 : A ⊗ Work.ATOM.zfree S ⟶ B) = 0 := by
  rw [ihomPoints_symm_apply_aux, curry_zero_aux]
  rfl

end Work.ANALYTIC
