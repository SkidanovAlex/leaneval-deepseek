import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.towerFSetup
import Submission.Work.ANALYTIC.towerFEAsetup
import Submission.Work.ANALYTIC.coordTimesDelta_mem_range
import Submission.Work.ANALYTIC.EA_shift
import Submission.Work.ANALYTIC.unitor_zfreeTensorIso
import Submission.Work.ANALYTIC.ihomPointsAddEquiv
import Submission.Work.ANALYTIC.ihomPoints_homFreeEquiv
import Submission.Work.ANALYTIC.truncDataElemNat
import Submission.Work.ANALYTIC.genPointsExt
import Submission.Work.ATOM.zdesc

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

/-! ## The coefficient `1 - ∏_{i ≤ m}(1 - δ_i n)` is the characteristic function of `{n ≤ m}` -/

theorem one_sub_prod_deltaFun (m n : ℕ) :
    1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i ((n : ℕ) : ℕ∪{∞})) =
      (if n ≤ m then 1 else 0) := by
  by_cases hn : n ≤ m
  · rw [if_pos hn, Finset.prod_eq_single (a := n)]
    · rw [deltaFun_at]; ring
    · intro b hb hbn
      rw [deltaFun_eq,
        if_neg (fun h : ((n : ℕ) : ℕ∪{∞}) = ((b : ℕ) : ℕ∪{∞}) =>
          hbn (OnePoint.coe_eq_coe.mp h).symm), sub_zero]
    · intro hn'
      exact absurd (Finset.mem_range.mpr (by omega)) hn'
  · rw [if_neg hn]
    have h : (∏ i ∈ Finset.range (m + 1), (1 - deltaFun i ((n : ℕ) : ℕ∪{∞}))) = 1 :=
      Finset.prod_eq_one fun i hi => by
        rw [deltaFun_eq,
          if_neg (fun h : ((n : ℕ) : ℕ∪{∞}) = ((i : ℕ) : ℕ∪{∞}) => ?_), sub_zero]
        have hin : n = i := OnePoint.coe_eq_coe.mp h
        have hi' : i < m + 1 := Finset.mem_range.mp hi
        omega
    rw [h]; ring

/-! ## The `k`-slice of `truncDataElem` is the `k`-th truncation -/

/-- Pointwise value of the truncation data at a point `(k,s)` of `(ℕ∪∞) × S`. -/
lemma truncDataElem_at (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (m : ℕ) (k : ↥(ℕ∪{∞})) (s : ↥S) :
    ((truncDataElem S x).1 m) (k, s)
      = x.1 m s * (1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i k)) := rfl

theorem map_cSlice_truncDataElem (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (k : ℕ) :
    boundedSeq.obj.map (cSlice S k).op (truncDataElem S x) =
      (truncZ k).hom.app (Opposite.op S) x := by
  refine Subtype.ext (funext fun m => ContinuousMap.ext fun s => ?_)
  rw [truncZ_val, boundedSeq_map_apply, cSlice_apply]
  show ((truncDataElem S x).1 m) ((((k : ℕ) : ℕ∪{∞})), s) =
    x.1 m s * (if k ≤ m then (1 : ℤ) else 0)
  rw [truncDataElem_at, one_sub_prod_deltaFun]

/-! ## The slice identity `(λ_ ℤ[S])⁻¹ ≫ (e_k ▷ ℤ[S]) ≫ T = ℤ[(k,-)] ≫ EA S ≫ T` -/

theorem ePointZ_EA_slice_comp (S : LightProfinite.{0}) (k : ℕ)
    (T : Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ boundedSeq) :
    (λ_ (Work.ATOM.zfree S)).inv ≫ (ePointZ k ▷ Work.ATOM.zfree S) ≫ T =
      Work.ATOM.zmap (cSlice S k) ≫ Work.ATOM.EA S ≫ T := by
  have hμ : (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).hom ≫ Work.ATOM.EA S =
      LightCondensed.P_proj ▷ Work.ATOM.zfree S := by
    rw [Work.ATOM.EA, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hnat : (Work.ATOM.zmap (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty)
        (((k : ℕ) : ℕ∪{∞}))) ▷ Work.ATOM.zfree S) ≫
        (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).hom =
      (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom ≫
        Work.ATOM.zmap (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty)
          (((k : ℕ) : ℕ∪{∞})) ▷ S) :=
    zmap_whiskerRight_zfreeTensorIso (Y := S)
      (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty) (((k : ℕ) : ℕ∪{∞})))
  have hnat' : ∀ U : Work.ATOM.zfree (Work.ATOM.NS S) ⟶ boundedSeq,
      (Work.ATOM.zmap (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty)
        (((k : ℕ) : ℕ∪{∞}))) ▷ Work.ATOM.zfree S) ≫
        (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).hom ≫ U =
      (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom ≫
        Work.ATOM.zmap (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty)
          (((k : ℕ) : ℕ∪{∞})) ▷ S) ≫ U := fun U => by
    rw [← Category.assoc, hnat, Category.assoc]
  have hU : ∀ V : Work.ATOM.zfree (Work.ATOM.pt ⊗ S) ⟶ boundedSeq,
      (λ_ (Work.ATOM.zfree S)).inv ≫
      (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S) ≫
      (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom ≫ V =
        Work.ATOM.zmap ((λ_ S).inv) ≫ V := fun V => by
    rw [← Category.assoc, ← Category.assoc, unitor_zfreeTensorIso]
  simp only [ePointZ, MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← hμ, Category.assoc, hnat', hU, ← Category.assoc, ← Work.ATOM.zmap_comp_zfree]
  rfl

/-! ## Naturality of `truncPhi` and `truncPsi` in the light profinite variable -/

theorem truncPhi_natural {S T : LightProfinite.{0}} (f : T ⟶ S)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) f) ≫ truncPhi S x =
      truncPhi T (boundedSeq.obj.map f.op x) := by
  apply (Work.ATOM.homFreeEquiv (Work.ATOM.NS T) boundedSeq).injective
  rw [Work.ATOM.homFreeEquiv_naturality, homFreeEquiv_truncPhi, homFreeEquiv_truncPhi]
  exact truncDataElemNat T S f x

theorem truncPsi_natural {S T : LightProfinite.{0}} (f : T ⟶ S)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    truncPsi T (boundedSeq.obj.map f.op x) =
      (LightCondensed.P ◁ Work.ATOM.zmap f) ≫ truncPsi S x := by
  refine (eq_truncPsi T (boundedSeq.obj.map f.op x) ?_).symm
  rw [← Category.assoc, EA_natural, Category.assoc, truncPsi_spec, truncPhi_natural]

/-! ## The value of `truncPsi` on the `k`-slice -/

theorem truncPsi_ePoint_slice (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (k : ℕ) :
    (λ_ (Work.ATOM.zfree S)).inv ≫ (ePointZ k ▷ Work.ATOM.zfree S) ≫ truncPsi S x =
      (Work.ATOM.homFreeEquiv S boundedSeq).symm ((truncZ k).hom.app (Opposite.op S) x) := by
  rw [ePointZ_EA_slice_comp S k (truncPsi S x), truncPsi_spec]
  apply (Work.ATOM.homFreeEquiv S boundedSeq).injective
  rw [Work.ATOM.homFreeEquiv_naturality, homFreeEquiv_truncPhi, map_cSlice_truncDataElem,
    Equiv.apply_symm_apply]

theorem truncZ_zero_app (S : LightProfiniteᵒᵖ) (x : ↥(boundedSeq.obj.obj S)) :
    (truncZ 0).hom.app S x = x := by
  refine Subtype.ext (funext fun m => ContinuousMap.ext fun s => ?_)
  rw [truncZ_val, if_pos (Nat.zero_le m), mul_one]

theorem truncZ_zero : truncZ 0 = 𝟙 boundedSeq := by
  refine hom_eq_of_zfree_comp_eq ?_
  intro S g
  rw [Category.comp_id]
  apply (Work.ATOM.homFreeEquiv S boundedSeq).injective
  rw [Work.ATOM.homFreeEquiv_naturality_target]
  exact truncZ_zero_app (Opposite.op S) ((Work.ATOM.homFreeEquiv S boundedSeq) g)

/-! ## The natural transformation `∏^bnd ℤ ⟶ (P ⟹ ∏^bnd ℤ)` -/

/-- An additive map between abelian groups is `ℤ`-linear with respect to any two `ℤ`-module
structures (there is at most one such structure on a given `AddCommGroup`). -/
lemma addMonoidHom_map_smul_module {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) (hM : Module ℤ M) (hN : Module ℤ N) (c : ℤ) (x : M) :
    f (hM.smul c x) = hN.smul c (f x) := by
  rw [int_smul_eq_zsmul hM c x, int_smul_eq_zsmul hN c (f x)]
  exact AddMonoidHom.map_zsmul f c x

/-- The map `x ↦ truncPsi S x`, as an additive homomorphism. -/
noncomputable def truncPsiHom (S : LightProfinite.{0}) :
    ↥(boundedSeqSet S) →+
      (Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ boundedSeq) where
  toFun x := truncPsi S x
  map_zero' := truncPsi_zero S
  map_add' x y := truncPsi_add S x y

/-- The `S`-points of the wanted `curry F`, as additive homomorphisms. -/
noncomputable def thetaFApp (S : LightProfinite.{0}) :
    ↥(boundedSeqSet S) →+
      ↥(((CategoryTheory.ihom LightCondensed.P).obj boundedSeq).obj.obj (Opposite.op S)) :=
  (ihomPointsSymmAddEquiv LightCondensed.P boundedSeq S).toAddMonoidHom.comp (truncPsiHom S)

theorem thetaFApp_apply (S : LightProfinite.{0})
    (x : ↥(boundedSeqSet S)) :
    thetaFApp S x =
      (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S).symm (truncPsi S x) := by
  show (ihomPointsSymmAddEquiv LightCondensed.P boundedSeq S) (truncPsiHom S x) = _
  rw [ihomPointsSymmAddEquiv_apply]
  rfl

/-- **The natural transformation `∏^bnd ℤ ⟶ (P ⟹ ∏^bnd ℤ)`** whose `S`-points are
`x ↦ truncPsi S x`; its uncurrying is the wanted `F`. -/
noncomputable def thetaF :
    boundedSeq ⟶ (CategoryTheory.ihom LightCondensed.P).obj boundedSeq :=
  ObjectProperty.homMk
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x => thetaFApp S.unop x
          map_add' := fun x y => by
            show thetaFApp S.unop (x + y) = thetaFApp S.unop x + thetaFApp S.unop y
            exact map_add (thetaFApp S.unop) x y
          map_smul' := fun c x => by
            show (thetaFApp S.unop)
                ((inferInstance : Module ℤ ↥(boundedSeqSet (Opposite.unop S))).smul c x) =
              (inferInstance : Module ℤ
                ↥(((CategoryTheory.ihom LightCondensed.P).obj boundedSeq).obj.obj S)).smul c
                ((thetaFApp S.unop) x)
            exact addMonoidHom_map_smul_module _ _ _ c x }
      naturality := by
        intro S T f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have h1 : ((CategoryTheory.ihom LightCondensed.P).obj boundedSeq).obj.map f
              ((LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S.unop).symm
                (truncPsi S.unop x)) =
            (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq T.unop).symm
              ((LightCondensed.P ◁ Work.ATOM.zmap f.unop) ≫ truncPsi S.unop x) := by
          have h := LightCondensed.ihomPoints_symm_comp ℤ boundedSeq LightCondensed.P
            T.unop S.unop f.unop (truncPsi S.unop x)
          simpa using h.symm
        show (ihomPointsSymmAddEquiv LightCondensed.P boundedSeq T.unop)
              (truncPsi T.unop (boundedSeq.obj.map f x)) =
            ((CategoryTheory.ihom LightCondensed.P).obj boundedSeq).obj.map f
              ((ihomPointsSymmAddEquiv LightCondensed.P boundedSeq S.unop)
                (truncPsi S.unop x))
        rw [ihomPointsSymmAddEquiv_apply, ihomPointsSymmAddEquiv_apply, h1,
          ← truncPsi_natural f.unop x, Quiver.Hom.op_unop f] }

theorem thetaF_app (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    thetaF.hom.app (Opposite.op S) x =
      (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S).symm (truncPsi S x) :=
  thetaFApp_apply S x

/-- **The morphism `F : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ`** of the statement: the uncurrying of `thetaF`. -/
noncomputable def towerF :
    Work.ATOM.tmul LightCondensed.P boundedSeq ⟶ boundedSeq :=
  MonoidalClosed.uncurry thetaF

/-- The `S`-points of `curry towerF` are `x ↦ truncPsi S x`. -/
theorem curry_towerF :
    MonoidalClosed.curry towerF = thetaF :=
  MonoidalClosed.curry_uncurry thetaF

/-- The coherence `(P ◁ g) ≫ towerF = truncPsi S x` for `x = homFreeEquiv S _ g`. -/
theorem whiskerLeft_towerF (S : LightProfinite.{0}) (g : Work.ATOM.zfree S ⟶ boundedSeq) :
    (LightCondensed.P ◁ g) ≫ towerF =
      truncPsi S ((Work.ATOM.homFreeEquiv S boundedSeq) g) := by
  have h := ihomPoints_homFreeEquiv LightCondensed.P boundedSeq boundedSeq thetaF S g
  rw [thetaF_app S ((Work.ATOM.homFreeEquiv S boundedSeq) g), Equiv.apply_symm_apply] at h
  rw [h, MonoidalClosed.uncurry_natural_left]
  rfl

theorem isTruncTower_towerF : IsTruncTower towerF := by
  unfold IsTruncTower
  intro S x k
  rw [curry_towerF, thetaF_app S x, Equiv.apply_symm_apply]
  refine (cancel_epi ((λ_ (Work.ATOM.zfree S)).inv)).mp ?_
  have hcancel : (λ_ (Work.ATOM.zfree S)).inv ≫ (λ_ (Work.ATOM.zfree S)).hom ≫
      (Work.ATOM.homFreeEquiv S boundedSeq).symm ((truncZ k).hom.app (Opposite.op S) x) =
      (Work.ATOM.homFreeEquiv S boundedSeq).symm ((truncZ k).hom.app (Opposite.op S) x) := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [truncPsi_ePoint_slice S x k, hcancel]

theorem isRetraction_towerF : IsRetraction towerF := by
  unfold IsRetraction
  refine hom_eq_of_zfree_comp_eq (M := boundedSeq) (N := boundedSeq)
    (u := sBoundedZ ≫ towerF) (v := 𝟙 boundedSeq) ?_
  intro S g
  rw [Category.comp_id, ← Category.assoc]
  have hsb : g ≫ sBoundedZ =
      (λ_ (Work.ATOM.zfree S)).inv ≫ (ePointZ 0 ▷ Work.ATOM.zfree S) ≫
        (LightCondensed.P ◁ g) := by
    show g ≫ ((λ_ boundedSeq).inv ≫ (ePointZ 0 ▷ boundedSeq)) = _
    rw [← Category.assoc, MonoidalCategory.leftUnitor_inv_naturality (f := g), Category.assoc,
      ← MonoidalCategory.whisker_exchange (ePointZ 0) g]
  rw [hsb, Category.assoc, Category.assoc, whiskerLeft_towerF S g,
    truncPsi_ePoint_slice S ((Work.ATOM.homFreeEquiv S boundedSeq) g) 0,
    truncZ_zero_app (Opposite.op S) ((Work.ATOM.homFreeEquiv S boundedSeq) g)]
  exact Equiv.symm_apply_apply _ _

/-- **Existence of `F` with the truncation data.**  There is `F : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ` which is
a retraction of `s = e_0 ⊗ -` (`Work.ANALYTIC.IsRetraction F`) and whose null family is the family
of truncations (`Work.ANALYTIC.IsTruncTower F`): for every light profinite `S`,
`x ∈ ∏^bnd ℤ(S)` and `k : ℕ`, the `k`-th component of the `S`-point of `F` at `x` is the
truncation `π_{≥k} x`, i.e. the section of `∏^bnd ℤ` over `S` with `m`-th component
`s ↦ x_m(s)·[k ≤ m]` (`Work.ANALYTIC.truncZ k`).  (Both reviewers note `truncZ 0 = 𝟙`, so the
second conjunct already implies the first; prove both as stated.)

Route: `LightCondensed.ihomPoints` reduces the `S`-points of `MonoidalClosed.curry F` to maps
`P ⊗ ℤ[S] ⟶ ∏^bnd ℤ`, and `Work.ATOM.Toolkit.PS_desc` says that giving such a map is equivalent
to giving a map `ℤ[(ℕ∪∞) × S] ⟶ ∏^bnd ℤ` killing the `∞`-slice (with `EA S ≫ ψ = φ`), i.e. an
element of `∏^bnd ℤ((ℕ∪∞) × S)` vanishing on `{∞} × S`.  That element is
`(m,(k,s)) ↦ x_m(s)·[k ≤ m]`; it is legitimate because `{k : k ≤ m}` is finite hence clopen, it
vanishes at `k = ∞`, and its bound is inherited from `x`.  Naturality in `S` follows from
`Work.ANALYTIC.EA_natural` plus the uniqueness in `PS_desc`; additivity in `x` gives the module
structure needed to assemble the natural transformation `∏^bnd ℤ ⟶ (P ⟹ ∏^bnd ℤ)`. -/
theorem exists_tower_F :
    ∃ F : Work.ATOM.tmul LightCondensed.P Work.ANALYTIC.boundedSeq ⟶ Work.ANALYTIC.boundedSeq,
      Work.ANALYTIC.IsRetraction F ∧ Work.ANALYTIC.IsTruncTower F :=
  ⟨towerF, isRetraction_towerF, isTruncTower_towerF⟩

end

end Work.ANALYTIC
