import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Submission.Commons.Algebra.Homology.homologyUnop_hom_naturality
import Submission.Commons.RepresentationTheory.GroupCohomology.barComplex_res_comp_pi
import Submission.Commons.RepresentationTheory.GroupCohomology.inhomogeneousCochainsIso_apply

set_option maxHeartbeats 2000000

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Limits

/-- The `n`-th component of the canonical chain map `barComplex k S ⟶ Res(barComplex k G)`
induced by the inclusion `S ⊆ G`: it sends the generator `x : Fin n → S` to the generator
`S.subtype ∘ x`. -/
noncomputable def barResMap (G : Type) [Group G] (S : Subgroup G) (n : ℕ) :
    (Rep.barComplex ℤ S).X n ⟶ Rep.res S.subtype (Rep.free ℤ G (Fin n → G)) :=
  Rep.freeLift ℤ S (Rep.res S.subtype (Rep.free ℤ G (Fin n → G)))
    (fun x : Fin n → S => Finsupp.single (S.subtype ∘ x) (1 : MonoidAlgebra ℤ G))

lemma barResMap_apply (G : Type) [Group G] (S : Subgroup G) (n : ℕ) (x : Fin n → S)
    (g : S) (r : ℤ) :
    (barResMap G S n).hom (Finsupp.single x (MonoidAlgebra.single g r)) =
      Finsupp.single (S.subtype ∘ x) (MonoidAlgebra.single (S.subtype g) r) := by
  show (Representation.freeLift (MonoidHom.comp (Rep.free ℤ G (Fin n → G)).ρ S.subtype)
      (fun x : Fin n → S => Finsupp.single (S.subtype ∘ x) (1 : MonoidAlgebra ℤ G)))
      (Finsupp.single x (MonoidAlgebra.single g r)) = _
  rw [Representation.freeLift_single_single]
  have h1 : (1 : MonoidAlgebra ℤ G) = MonoidAlgebra.single (1 : G) (1 : ℤ) := rfl
  rw [h1, MonoidHom.comp_apply, Representation.free_single_single]
  simp

lemma barResMap_comp (G : Type) [Group G] (S : Subgroup G) (n : ℕ) :
    barResMap G S (n+1) ≫ Rep.resMap S.subtype ((Rep.barComplex ℤ G).d (n+1) n) =
      (Rep.barComplex ℤ S).d (n+1) n ≫ barResMap G S n := by
  apply Rep.free_ext
  intro x
  rw [Rep.comp_apply, Rep.comp_apply]
  rw [Rep.barComplex.d_def, Rep.barComplex.d_def]
  rw [barResMap_apply G S (n+1) x 1 1]
  rw [Rep.resMap_hom_apply]
  simp only [map_one]
  rw [Rep.barComplex.d_single, Rep.barComplex.d_single]
  rw [map_add, map_sum]
  congr 1
  · rw [barResMap_apply G S n (fun i => x i.succ) (x 0) 1]
    congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [barResMap_apply G S n (j.contractNth (· * ·) x) 1 ((-1:ℤ)^(j.val+1))]
    congr 2
    exact (Fin.comp_contractNth (fun a b => a * b) (fun a b => a * b)
      (fun a b => map_mul S.subtype a b) j x).symm

/-- The canonical resolution of the trivial `S`-representation obtained by restricting the bar
resolution of `G`. -/
noncomputable abbrev barResResolution (G : Type) [Group G] (S : Subgroup G) :
    ProjectiveResolution (Rep.trivial ℤ S ℤ) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)

/-- The canonical chain map `barComplex k S ⟶ Res(barComplex k G)` over the identity. -/
noncomputable def barResChain (G : Type) [Group G] (S : Subgroup G) :
    Rep.barComplex ℤ S ⟶
      ((Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)).complex :=
  { f := fun n => barResMap G S n
    comm' := by rintro i j (rfl : j + 1 = i); exact barResMap_comp G S j }

set_option backward.isDefEq.respectTransparency false in
lemma barResChain_π (G : Type) [Group G] (S : Subgroup G) :
    barResChain G S ≫ (barResResolution G S).π = (Rep.barResolution ℤ S).π := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      simp only [barResChain, barResResolution, barResMap, Functor.mapProjectiveResolution_π,
        HomologicalComplex.comp_f]
      exact Commons.RepresentationTheory.GroupCohomology.barComplex_res_comp_pi S
  | succ n =>
      rw [HomologicalComplex.comp_f, ProjectiveResolution.π_f_succ, ProjectiveResolution.π_f_succ]
      simp

section IsoExtComparison

variable {R : Type*} [Ring R] {C : Type*} [Category* C] [Abelian C] [Linear R C] [EnoughProjectives C]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison between the identifications of `Ext` with the homology of
`Hom(-, Y)` for two projective resolutions of the same object. -/
lemma isoLeftDerivedObj_comp {D : Type*} [Category* D] [Abelian D] {X : C}
    (P Q : ProjectiveResolution X) (q : P.complex ⟶ Q.complex) (hq : q ≫ Q.π = P.π)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom =
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map q) := by
  have hcomm : q.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ (𝟙 X) := by
    have h := congrArg (fun (m : P.complex ⟶ (ChainComplex.single₀ C).obj X) => m.f 0) hq
    rw [HomologicalComplex.comp_f] at h
    erw [h, Category.comp_id]
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 X) P Q q hcomm F n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [show (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map q =
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map q) from rfl] at h
  rw [h]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison of the `Ext`-identifications `isoExt` for two projective resolutions of the same
object, expressed as the homology map of the induced morphism on `linearYonedaObj`. -/
lemma isoExt_inv_comp_hom {X : C} (P Q : ProjectiveResolution X)
    (q : P.complex ⟶ Q.complex) (hq : q ≫ Q.π = P.π) (Y : C) (n : ℕ) :
    (Q.isoExt n Y).inv ≫ (P.isoExt n Y).hom =
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).map
        ((HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
          (((Functor.mapHomologicalComplex ((linearYoneda R C).obj Y).rightOp
            (ComplexShape.down ℕ)).map q)).op) := by
  simp only [ProjectiveResolution.isoExt]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.unop_hom, Iso.unop_inv]
  have h1 : (Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom.unop ≫
      (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv.unop
      = ((HomologicalComplex.homologyFunctor (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) n).map
          ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ)).map q)).unop := by
    rw [← CategoryTheory.unop_comp (f := (P.isoLeftDerivedObj
        ((linearYoneda R C).obj Y).rightOp n).inv) (g := (Q.isoLeftDerivedObj
        ((linearYoneda R C).obj Y).rightOp n).hom)]
    rw [isoLeftDerivedObj_comp (D := (ModuleCat R)ᵒᵖ) P Q q hq ((linearYoneda R C).obj Y).rightOp n]
  calc ((((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            Q.complex).homologyUnop n).hom ≫
        (Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom.unop ≫
          (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv.unop ≫
            (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
              P.complex).homologyUnop n).inv)
      = (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            Q.complex).homologyUnop n).hom ≫
        ((Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom.unop ≫
          (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv.unop) ≫
            (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
              P.complex).homologyUnop n).inv := by
        simp only [Category.assoc]
    _ = (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            Q.complex).homologyUnop n).hom ≫
        ((HomologicalComplex.homologyFunctor (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) n).map
          ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ)).map q)).unop ≫
            (((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
              P.complex).homologyUnop n).inv := by
        rw [h1]
    _ = _ := Commons.Algebra.Homology.homologyUnop_hom_naturality _ n

end IsoExtComparison

section Comparison

variable (G : Type) [Group G] (S : Subgroup G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison morphism `Hom(Res(bar G), A) → Hom(bar S, A)` induced by the canonical chain
map `barResChain G S`. -/
noncomputable def psiMap (A : Rep ℤ S) :
    letI : Linear ℤ (Rep.{0,0,0} ℤ S) := Rep.instLinear
    ((((Rep.resFunctor S.subtype).mapProjectiveResolution
        (Rep.barResolution ℤ G)).complex).linearYonedaObj ℤ A) ⟶
      (((Rep.barComplex ℤ S).linearYonedaObj ℤ A)) :=
  letI : Linear ℤ (Rep.{0,0,0} ℤ S) := Rep.instLinear
  (HomologicalComplex.unopFunctor (ModuleCat ℤ) (ComplexShape.down ℕ)).map
    (((Functor.mapHomologicalComplex ((linearYoneda ℤ (Rep ℤ S)).obj A).rightOp
      (ComplexShape.down ℕ)).map (barResChain G S)).op)

set_option backward.isDefEq.respectTransparency false in
lemma psiMap_apply (A : Rep ℤ S) (i : ℕ)
    (h : (barResResolution G S).complex.X i ⟶ A)
    (z : (Rep.barComplex ℤ S).X i) :
    (((psiMap G S A).f i).hom h).hom z =
      h.hom (((barResChain G S).f i).hom z) := by
  rw [psiMap, HomologicalComplex.unopFunctor_map_f]
  simp only [Quiver.Hom.op_unop]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphism of complexes underlying Shapiro's lemma. -/
noncomputable def lambdaIso (A : Rep ℤ S) :
    letI : Linear ℤ (Rep.{0,0,0} ℤ G) := Rep.instLinear
    letI : Linear ℤ (Rep.{0,0,0} ℤ S) := Rep.instLinear
    ((((Rep.resFunctor S.subtype).mapProjectiveResolution
        (Rep.barResolution ℤ G)).complex).linearYonedaObj ℤ A) ≅
      (((Rep.barComplex ℤ G).linearYonedaObj ℤ (Rep.coind S.subtype A))) :=
  groupCohomology.linearYonedaObjResProjectiveResolutionIso (Rep.barResolution ℤ G) A

variable (M : Rep.{0,0,0} ℤ G)

set_option backward.isDefEq.respectTransparency false in
/-- The first arrow: the unit of the coind adjunction applied to `M`, as a cochain map. -/
noncomputable def coindUnitCochains :
    groupCohomology.inhomogeneousCochains M ⟶
      groupCohomology.inhomogeneousCochains (Rep.coind S.subtype (Rep.res S.subtype M)) :=
  groupCohomology.cochainsMap (MonoidHom.id G)
    ((Rep.resCoindAdjunction ℤ S.subtype).unit.app M)

set_option backward.isDefEq.respectTransparency false in
/-- The second arrow: restriction along `S ⊆ G`, as a cochain map. -/
noncomputable def resCochains :
    groupCohomology.inhomogeneousCochains M ⟶
      groupCohomology.inhomogeneousCochains (Rep.res S.subtype M) :=
  groupCohomology.cochainsMap S.subtype (𝟙 (Rep.res S.subtype M))


set_option backward.isDefEq.respectTransparency false in
lemma coindUnitCochains_apply (i : ℕ) (y : (Fin i → G) → M) :
    ((coindUnitCochains G S M).f i).hom y =
      (fun g => ((Rep.resCoindAdjunction ℤ S.subtype).unit.app M).hom (y g)) := by
  rw [coindUnitCochains, groupCohomology.cochainsMap_id_f_hom_eq_compLeft]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma resCochains_apply (i : ℕ) (y : (Fin i → G) → M) :
    ((resCochains G S M).f i).hom y = (fun s : Fin i → S => y (S.subtype ∘ s)) := by
  rw [resCochains, groupCohomology.cochainsMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma unit_apply_one (a : M) :
    letI : Module ℤ ↥(Rep.res S.subtype M) := (Rep.res S.subtype M).hV2
    (Representation.coindV S.subtype (Rep.res S.subtype M).ρ).subtype
      (((Rep.resCoindAdjunction ℤ S.subtype).unit.app M) a) 1 = a := by
  rw [show (Rep.resCoindAdjunction ℤ S.subtype).unit.app M
      = Rep.resCoindToHom S.subtype M (Rep.res S.subtype M)
          (𝟙 (Rep.res S.subtype M)) from rfl]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma barResChain_f_apply (i : ℕ) (x : Fin i → S) :
    ((barResChain G S).f i).hom (Finsupp.single x (MonoidAlgebra.single (1:S) (1:ℤ))) =
      Finsupp.single (S.subtype ∘ x) (MonoidAlgebra.single (1:G) (1:ℤ)) := by
  rw [barResChain]
  exact barResMap_apply G S i x 1 1

set_option backward.isDefEq.respectTransparency false in
lemma lambdaIso_symm_apply (A : Rep ℤ S) (i : ℕ)
    (g : (Rep.barComplex ℤ G).X i ⟶ Rep.coind S.subtype A)
    (u : (barResResolution G S).complex.X i) :
    letI : Module ℤ ↥A := A.hV2
    (((lambdaIso G S A).symm.hom.f i).hom g).hom u =
      ((Representation.coindV S.subtype A.ρ).subtype (g.hom u)) 1 := by
  simp only [lambdaIso, groupCohomology.linearYonedaObjResProjectiveResolutionIso, Iso.symm_hom,
    HomologicalComplex.Hom.isoOfComponents_inv_f, LinearEquiv.toModuleIso_inv,
    ModuleCat.ofHom_hom, Rep.resCoindHomEquiv_symm_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The key chain-level identity. -/
lemma key_chain_identity :
    coindUnitCochains G S M ≫
        (groupCohomology.inhomogeneousCochainsIso
          (Rep.coind S.subtype (Rep.res S.subtype M))).hom ≫
        (lambdaIso G S (Rep.res S.subtype M)).symm.hom ≫
        psiMap G S (Rep.res S.subtype M) =
      resCochains G S M ≫
        (groupCohomology.inhomogeneousCochainsIso (Rep.res S.subtype M)).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  letI : Module ℤ ((groupCohomology.inhomogeneousCochains M).X i) :=
    ModuleCat.isModule ((groupCohomology.inhomogeneousCochains M).X i)
  letI : Module ℤ (((Rep.barComplex ℤ S).linearYonedaObj ℤ (Rep.res S.subtype M)).X i) :=
    ModuleCat.isModule (((Rep.barComplex ℤ S).linearYonedaObj ℤ (Rep.res S.subtype M)).X i)
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext (fun y => ?_)
  apply Rep.free_ext
  intro x
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [ConcreteCategory.comp_apply]
  rw [psiMap_apply G S (Rep.res S.subtype M) i _
    (Finsupp.single x (MonoidAlgebra.single (1:S) (1:ℤ)))]
  rw [barResChain_f_apply G S i x]
  rw [lambdaIso_symm_apply G S (Rep.res S.subtype M) i _ _]
  have hι : (((groupCohomology.inhomogeneousCochainsIso
        (Rep.coind S.subtype (Rep.res S.subtype M))).hom.f i).hom
        (((coindUnitCochains G S M).f i).hom y)).hom
        (Finsupp.single (S.subtype ∘ x) (MonoidAlgebra.single (1:G) (1:ℤ))) =
        (((coindUnitCochains G S M).f i).hom y) (S.subtype ∘ x) :=
    inhomogeneousCochainsIso_apply (Rep.coind S.subtype (Rep.res S.subtype M)) i _ _
  rw [hι]
  rw [coindUnitCochains_apply]
  rw [unit_apply_one]
  have hι2 : (((groupCohomology.inhomogeneousCochainsIso (Rep.res S.subtype M)).hom.f i).hom
        (((resCochains G S M).f i).hom y)).hom
        (Finsupp.single x (MonoidAlgebra.single (1:S) (1:ℤ))) =
        (((resCochains G S M).f i).hom y) x :=
    inhomogeneousCochainsIso_apply (Rep.res S.subtype M) i _ _
  change y (S.subtype ∘ x) =
    (((groupCohomology.inhomogeneousCochainsIso (Rep.res S.subtype M)).hom.f i).hom
      (((resCochains G S M).f i).hom y)).hom
      (Finsupp.single x (MonoidAlgebra.single (1:S) (1:ℤ)))
  rw [hι2, resCochains_apply]

end Comparison

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem unit_coindIso_eq_resNatTrans {G : Type} [Group G] [Fintype G] (S : Subgroup G)
    (M : Rep.{0,0,0} ℤ G) (n : ℕ) :
    (groupCohomology.map (MonoidHom.id G)
        ((Rep.resCoindAdjunction ℤ S.subtype).unit.app M) n) ≫
      (groupCohomology.coindIso (k := ℤ) (S := S) (Rep.res S.subtype M) n).hom =
    (groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype n).app M := by
  letI : Linear ℤ (Rep.{0,0,0} ℤ S) := Rep.instLinear
  let A : Rep.{0,0,0} ℤ S := Rep.res S.subtype M
  let Q_ : ProjectiveResolution (Rep.trivial ℤ S ℤ) := barResResolution G S
  let ιA := groupCohomology.inhomogeneousCochainsIso A
  let ιCoA := groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A)
  let HιA := asIso (HomologicalComplex.homologyMap ιA.hom n)
  let lam := lambdaIso G S A
  have h_isoExtExt : (groupCohomologyIsoExt A n).inv ≫ HιA.hom
      = ((Rep.barResolution ℤ S).isoExt n A).hom := by
    dsimp only [groupCohomologyIsoExt, HιA, ιA, isoOfQuasiIsoAt, HomotopyEquiv.ofIso]
    rw [Iso.trans_inv, Iso.symm_inv]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hcoind : (groupCohomology.coindIso (k := ℤ) (S := S) A n).hom ≫ HιA.hom
      = ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
            (ιCoA ≪≫ lam.symm)).hom ≫
          (Q_.isoExt n A).inv ≫ ((Rep.barResolution ℤ S).isoExt n A).hom := by
    rw [groupCohomology.coindIso]
    dsimp only [Q_, lam, lambdaIso, barResResolution]
    rw [Iso.trans_hom, Iso.symm_hom]
    rw [groupCohomologyIso, Iso.trans_inv]
    simp only [Category.assoc]
    rw [h_isoExtExt]
  have hψ : (Q_.isoExt n A).inv ≫ ((Rep.barResolution ℤ S).isoExt n A).hom
      = HomologicalComplex.homologyMap (psiMap G S A) n := by
    dsimp only [Q_]
    exact isoExt_inv_comp_hom (Rep.barResolution ℤ S) (barResResolution G S)
      (barResChain G S) (barResChain_π G S) A n
  suffices h : (groupCohomology.map (MonoidHom.id G)
        ((Rep.resCoindAdjunction ℤ S.subtype).unit.app M) n) ≫
        (groupCohomology.coindIso (k := ℤ) (S := S) A n).hom ≫ HιA.hom =
      (groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype n).app M ≫ HιA.hom from
    (cancel_mono HιA.hom).mp h
  rw [hcoind, hψ]
  rw [show HιA.hom = HomologicalComplex.homologyMap
      (groupCohomology.inhomogeneousCochainsIso A).hom n from rfl]
  rw [show (groupCohomology.map (MonoidHom.id G)
        ((Rep.resCoindAdjunction ℤ S.subtype).unit.app M) n)
      = HomologicalComplex.homologyMap (coindUnitCochains G S M) n from rfl]
  rw [show (groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype n).app M
      = HomologicalComplex.homologyMap (resCochains G S M) n from rfl]
  rw [show ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
        (ιCoA ≪≫ lam.symm)).hom
      = HomologicalComplex.homologyMap ((ιCoA ≪≫ lam.symm).hom) n from rfl]
  rw [show (ιCoA ≪≫ lam.symm).hom = ιCoA.hom ≫ lam.symm.hom from rfl]
  dsimp only [lam, A]
  conv_lhs =>
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [key_chain_identity G S M]
  rw [HomologicalComplex.homologyMap_comp]

end Commons.RepresentationTheory.GroupCohomology