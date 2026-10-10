import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.Phi0Aux
import Submission.Work.SSGRoute.mapExactFunctor_id
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute
open CategoryTheory SSGRoute.PTExt
open scoped MonoidAlgebra

universe u v w

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- postcomposition chain map on `Hom(K_•, -)`. -/
def lyGen {C : Type u} [Category.{v} C] [Abelian C] (k : Type w) [Ring k] [Linear k C]
    (K : ChainComplex C ℕ) {Y Y' : C} (φ : Y ⟶ Y') :
    K.linearYonedaObj k Y ⟶ K.linearYonedaObj k Y' where
  f n := ((linearYoneda k C).map φ).app (Opposite.op (K.X n))
  comm' i j hij := by
    obtain rfl : j = i + 1 := by rw [ComplexShape.up_Rel] at hij; exact hij.symm
    exact (NatTrans.naturality ((linearYoneda k C).map φ) ((K.d (i+1) i).op)).symm

lemma lyGen_f_apply {C : Type u} [Category.{v} C] [Abelian C] (k : Type w) [Ring k] [Linear k C]
    (K : ChainComplex C ℕ) {Y Y' : C} (φ : Y ⟶ Y') (n : ℕ) (g : K.X n ⟶ Y) :
    (ModuleCat.Hom.hom ((lyGen k K φ).f n)) g = g ≫ φ := by
  simp only [lyGen, linearYoneda_map_app]
  exact Linear.rightComp_apply k _ φ g

/-- The `Classical.choose`d isomorphism `Hⁿ(Hom(R_•,-)) ≃ Ext` for a fixed resolution `R`. -/
noncomputable def PsiOf {C : Type u} [Category.{v} C] [Abelian C] (k : Type w) [Ring k]
    [Linear k C] [HasExt.{v} C] {X : C} (R : ProjectiveResolution X) (Y : C) (n : ℕ) :
    (R.complex.linearYonedaObj k Y).homology n ≃+ Abelian.Ext.{v} X Y n :=
  Classical.choose (E0bCore.extHAddEquivHomology (k := k) R n)

lemma PsiOf_spec {C : Type u} [Category.{v} C] [Abelian C] (k : Type w) [Ring k] [Linear k C]
    [HasExt.{v} C] {X Y : C} (R : ProjectiveResolution X) (n : ℕ)
    (f : R.complex.X n ⟶ Y) (hf : R.complex.d (n + 1) n ≫ f = 0) :
    PsiOf k R Y n ((HomologicalComplex.homologyπ (R.complex.linearYonedaObj k Y) n)
      (HomologicalComplex.cyclesMk (R.complex.linearYonedaObj k Y) f (n + 1) (by simp) (by
        change R.complex.d (n + 1) n ≫ f = 0
        exact hf))) =
      R.extMk f (n + 1) rfl hf :=
  Classical.choose_spec (E0bCore.extHAddEquivHomology (k := k) R n) f hf

lemma PsiOf_homologyπ_apply {C : Type u} [Category.{v} C] [Abelian C] (k : Type w) [Ring k]
    [Linear k C] [HasExt.{v} C] {X Y : C} (R : ProjectiveResolution X) (n : ℕ)
    (z : (R.complex.linearYonedaObj k Y).cycles n) :
    PsiOf k R Y n (HomologicalComplex.homologyπ (R.complex.linearYonedaObj k Y) n z) =
      R.extMk (E0bCore.cycHom R n z) (n + 1) rfl (E0bCore.cycHom_cocycle R n z) := by
  have hcoc : (ConcreteCategory.hom ((R.complex.linearYonedaObj k Y).d n (n + 1)))
      ((HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y) n) z) = 0 :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.iCycles_d (K := R.complex.linearYonedaObj k Y) n (n+1)) z
  have hf : R.complex.d (n + 1) n ≫ ((HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y) n) z) = 0 := by
    have h := hcoc
    rwa [E0bCore.linearYonedaObj_d_apply R.complex Y rfl
      ((HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y) n) z)] at h
  have hw : HomologicalComplex.cyclesMk (R.complex.linearYonedaObj k Y)
      ((HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y) n) z) (n + 1) (by simp) hcoc = z :=
    (ModuleCat.mono_iff_injective
      (HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y) n)).1 inferInstance
      (HomologicalComplex.i_cyclesMk (R.complex.linearYonedaObj k Y)
        ((HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y) n) z) (n + 1) (by simp) hcoc)
  conv_lhs => rw [← hw]
  rw [PsiOf_spec k R n ((HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y) n) z) hf]
  exact E0bCore.extMk_congr R (E0bCore.iCycles_eq_cycHom R n z) hf (E0bCore.cycHom_cocycle R n z)

lemma iCycles_cyclesMap {C : Type u} [Category.{v} C] [Abelian C] {k : Type w} [Ring k]
    [Linear k C] [HasExt.{v} C] {X Y Y' : C} (R : ProjectiveResolution X) (φ : Y ⟶ Y') (n : ℕ)
    (z : (R.complex.linearYonedaObj k Y).cycles n) :
    (HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y') n)
        (HomologicalComplex.cyclesMap (lyGen k R.complex φ) n z) =
      (ModuleCat.Hom.hom ((lyGen k R.complex φ).f n))
        ((HomologicalComplex.iCycles (R.complex.linearYonedaObj k Y) n) z) := by
  have h := congrArg (fun (g : (R.complex.linearYonedaObj k Y).cycles n ⟶
      (R.complex.linearYonedaObj k Y').X n) => g z)
    (HomologicalComplex.cyclesMap_i (lyGen k R.complex φ) n)
  simpa only [ConcreteCategory.comp_apply] using h

lemma cycHom_cyclesMap {C : Type u} [Category.{v} C] [Abelian C] {k : Type w} [Ring k]
    [Linear k C] [HasExt.{v} C] {X Y Y' : C} (R : ProjectiveResolution X) (φ : Y ⟶ Y') (n : ℕ)
    (z : (R.complex.linearYonedaObj k Y).cycles n) :
    E0bCore.cycHom R n (HomologicalComplex.cyclesMap (lyGen k R.complex φ) n z) =
      (ModuleCat.Hom.hom ((lyGen k R.complex φ).f n)) (E0bCore.cycHom R n z) := by
  rw [← E0bCore.iCycles_eq_cycHom R n
        (HomologicalComplex.cyclesMap (lyGen k R.complex φ) n z),
      iCycles_cyclesMap R φ n z, E0bCore.iCycles_eq_cycHom R n z]

lemma PsiOf_natural {C : Type u} [Category.{v} C] [Abelian C] (k : Type w) [Ring k] [Linear k C]
    [HasExt.{v} C] {X Y Y' : C} (R : ProjectiveResolution X) (φ : Y ⟶ Y') (n : ℕ)
    (y : (R.complex.linearYonedaObj k Y).homology n) :
    PsiOf k R Y' n ((HomologicalComplex.homologyMap (lyGen k R.complex φ) n) y) =
      (PsiOf k R Y n y).comp (Abelian.Ext.mk₀ φ) (add_zero n) := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyπ
      (R.complex.linearYonedaObj k Y) n)).1 inferInstance y
  have hnat : (HomologicalComplex.homologyMap (lyGen k R.complex φ) n)
        (HomologicalComplex.homologyπ (R.complex.linearYonedaObj k Y) n z) =
      HomologicalComplex.homologyπ (R.complex.linearYonedaObj k Y') n
        (HomologicalComplex.cyclesMap (lyGen k R.complex φ) n z) := by
    have h := congrArg (fun (g : (R.complex.linearYonedaObj k Y).cycles n ⟶
        (R.complex.linearYonedaObj k Y').homology n) => g z)
      (HomologicalComplex.homologyπ_naturality (lyGen k R.complex φ) n)
    simpa only [ConcreteCategory.comp_apply] using h
  rw [hnat]
  rw [PsiOf_homologyπ_apply k R n (HomologicalComplex.cyclesMap (lyGen k R.complex φ) n z),
      PsiOf_homologyπ_apply k R n z, ProjectiveResolution.extMk_comp_mk₀]
  exact E0bCore.extMk_congr R
    ((cycHom_cyclesMap R φ n z).trans (lyGen_f_apply k R.complex φ n (E0bCore.cycHom R n z))) _ _


/-! ## The `Rep`-specific coefficient change and the bridge -/

def lyCoeff (k : Type) [CommRing k] {G : Type} [Group G] {A B : Rep.{0,0,0} k G} (φ : A ⟶ B) :
    (Rep.barComplex k G).linearYonedaObj k A ⟶
      (Rep.barComplex k G).linearYonedaObj k B where
  f n := ((linearYoneda k (Rep.{0,0,0} k G)).map φ).app (Opposite.op ((Rep.barComplex k G).X n))
  comm' i j hij := by
    obtain rfl : j = i + 1 := by rw [ComplexShape.up_Rel] at hij; exact hij.symm
    exact (NatTrans.naturality ((linearYoneda k (Rep.{0,0,0} k G)).map φ)
      ((Rep.barComplex k G).d (i+1) i).op).symm

lemma lyCoeff_f_apply (k : Type) [CommRing k] {G : Type} [Group G] {A B : Rep.{0,0,0} k G}
    (φ : A ⟶ B) (n : ℕ) (g : (Rep.barComplex k G).X n ⟶ A) :
    (ModuleCat.Hom.hom ((lyCoeff k φ).f n)) g = g ≫ φ := by
  simp only [lyCoeff, linearYoneda_map_app]
  exact Linear.rightComp_apply k _ φ g

lemma iso_square (k : Type) [CommRing k] {G : Type} [Group G] {A B : Rep.{0,0,0} k G} (φ : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) φ ≫ (groupCohomology.inhomogeneousCochainsIso B).hom
      = (groupCohomology.inhomogeneousCochainsIso A).hom ≫ lyCoeff k φ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  ext z
  apply Rep.free_ext k G B
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [NK.RepresentationTheory.GroupCohomology.inhomogeneousCochainsIso_apply k G B i
        (ModuleCat.Hom.hom ((groupCohomology.cochainsMap (MonoidHom.id G) φ).f i) z) x,
      groupCohomology.cochainsMap_id_f_hom_eq_compLeft φ i]
  erw [lyCoeff_f_apply k φ i _]
  erw [Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_apply]
  erw [NK.RepresentationTheory.GroupCohomology.inhomogeneousCochainsIso_apply k G A i z x]
  simp only [LinearMap.compLeft_apply]
  rfl

theorem thetaHom_natural {G : Type} [Group G] {A B : Rep.{0,0,0} Coeff G} (φ : A ⟶ B) (n : ℕ)
    (x : groupCohomology A n) :
    thetaHom G B n ((groupCohomology.map (MonoidHom.id G) φ n).hom x) =
      (HomologicalComplex.homologyMap (lyCoeff Coeff φ) n).hom (thetaHom G A n x) := by
  have hcomp : HomologicalComplex.homologyMap
        (groupCohomology.cochainsMap (MonoidHom.id G) φ) n ≫
        HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
        HomologicalComplex.homologyMap (lyCoeff Coeff φ) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      iso_square Coeff φ]
  show (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso B).hom n))
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (groupCohomology.cochainsMap (MonoidHom.id G) φ) n) x) =
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (lyCoeff Coeff φ) n))
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (groupCohomology.inhomogeneousCochainsIso A).hom n) x)
  calc (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (groupCohomology.inhomogeneousCochainsIso B).hom n))
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (groupCohomology.cochainsMap (MonoidHom.id G) φ) n) x)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (groupCohomology.cochainsMap (MonoidHom.id G) φ) n ≫
          HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n)) x := by
          rw [ModuleCat.hom_comp]; rfl
    _ = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
          HomologicalComplex.homologyMap (lyCoeff Coeff φ) n)) x := by rw [hcomp]
    _ = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (lyCoeff Coeff φ) n))
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (groupCohomology.inhomogeneousCochainsIso A).hom n) x) := by
          rw [ModuleCat.hom_comp]; rfl

theorem extHMap_id_apply {G : Type} [Group G] {A B : Rep.{0,0,0} Coeff G} (φ : A ⟶ B) {n : ℕ}
    (y : SSGRoute.PTExt.extH A n) :
    SSGRoute.PTExt.extHMap (MonoidHom.id G) φ y =
      y.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero n) := by
  unfold SSGRoute.PTExt.extHMap SSGRoute.PTExt.extRes
  rw [show y.mapExactFunctor (Rep.resFunctor (MonoidHom.id G)) = y from mapExactFunctor_id y,
      show SSGRoute.PTExt.unitRes (MonoidHom.id G) = 𝟙 (SSGRoute.PTExt.unitRep G) from rfl]
  exact CategoryTheory.Abelian.Ext.mk₀_id_comp _

lemma Bridge_Psi_eq (n : ℕ) (G : Type) [Group G] (A : Rep.{0,0,0} Coeff G) :
    Bridge.Psi n G A = PsiOf Coeff (Bridge.barRes G) A n := rfl

theorem Psi_natural {G : Type} [Group G] {A B : Rep.{0,0,0} Coeff G} (φ : A ⟶ B) (n : ℕ)
    (y : ((Rep.barComplex Coeff G).linearYonedaObj Coeff A).homology n) :
    Bridge.Psi n G B ((HomologicalComplex.homologyMap (lyCoeff Coeff φ) n) y) =
      (Bridge.Psi n G A y).comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero n) := by
  rw [Bridge_Psi_eq n G B, Bridge_Psi_eq n G A]
  exact PsiOf_natural Coeff (Bridge.barRes G) φ n y

theorem bridgeE_map_coeff {G : Type} [Group G] (A B : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff G)
    (φ : Quiver.Hom A B) (n : ℕ) (x : groupCohomology A n) :
    Work.SSGRoute.bridgeE G B n
        ((groupCohomology.map (MonoidHom.id G) φ n).hom x) =
      SSGRoute.PTExt.extHMap (MonoidHom.id G) φ (Work.SSGRoute.bridgeE G A n x) := by
  show Bridge.Psi n G B (thetaHom G B n ((groupCohomology.map (MonoidHom.id G) φ n).hom x)) =
      SSGRoute.PTExt.extHMap (MonoidHom.id G) φ (Bridge.Psi n G A (thetaHom G A n x))
  rw [thetaHom_natural φ n x, Psi_natural φ n (thetaHom G A n x),
    ← extHMap_id_apply (G := G) φ (n := n) (Bridge.Psi n G A (thetaHom G A n x))]

end
end Work.SSGRoute
