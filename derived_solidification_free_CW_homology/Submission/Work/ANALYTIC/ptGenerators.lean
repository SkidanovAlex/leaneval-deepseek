import Mathlib
import Submission.Work.ANALYTIC.BoundedSeqC
import Submission.Work.ANALYTIC.evenOddDefs
import Submission.Work.ANALYTIC.coordTimesDelta_mem_range
import Submission.Work.FLAT.Setup
import Submission.Work.ATOM.ZS.Unred.LCZ_iso
import Submission.Work.ANALYTIC.cover_pt_eq_top
import Submission.Work.ANALYTIC.surjective_toSheafify_app_pt
import Submission.Work.ANALYTIC.zfree_pt_value
import Submission.Work.ANALYTIC.finsupp_collapse_NUI
import Submission.Work.ANALYTIC.finsupp_coord

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed
open Opposite

noncomputable section

namespace Work.ANALYTIC

abbrev J : GrothendieckTopology LightProfinite.{0} := coherentTopology LightProfinite.{0}

abbrev NUI : LightProfinite.{0} := LightProfinite.NatUnionInfty

/-- The presheaf underlying `ℤ[S]`: the sectionwise free presheaf on `S.toCondensed`. -/
abbrev Q (S : LightProfinite.{0}) : (LightProfinite.{0})ᵒᵖ ⥤ ModuleCat.{0} ℤ :=
  Work.FLAT.sectionwiseFree S.toCondensed

/-- The presheaf map `Q S ⟶ Q T` induced by a map `u : S ⟶ T` of light profinite sets. -/
noncomputable def Qmap {S T : LightProfinite.{0}} (u : S ⟶ T) : Q S ⟶ Q T :=
  ((Functor.whiskeringRight (LightProfinite.{0})ᵒᵖ (Type 0) (ModuleCat.{0} ℤ)).obj
    (ModuleCat.free ℤ)).map ((lightProfiniteToLightCondSet.map u).hom)

/-- The generator of `ℤ[S](∗)` attached to a map `u : ∗ ⟶ S`. -/
def ptGen (S : LightProfinite.{0}) (u : Work.ATOM.pt ⟶ S) :
    ↥((Work.ATOM.zfree S).obj.obj (op Work.ATOM.pt)) :=
  Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree S) (Work.ATOM.zmap u)

/-- The linear extension of the generators `ptGen S u`, as a morphism of modules. -/
noncomputable def Gm (S : LightProfinite.{0}) :
    (Q S).obj (op Work.ATOM.pt) ⟶ (Work.ATOM.zfree S).obj.obj (op Work.ATOM.pt) :=
  ModuleCat.freeDesc (↾fun u : Work.ATOM.pt ⟶ S =>
    Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree S) (Work.ATOM.zmap u))

/-- The linear extension of the elements `boundedSeq.map u.op deltaElem` (for `S = ℕ∪{∞}`). -/
noncomputable def Tm :
    (Q NUI).obj (op Work.ATOM.pt) ⟶ (Work.ANALYTIC.boundedSeq).obj.obj (op Work.ATOM.pt) :=
  ModuleCat.freeDesc (X := (NUI.toCondensed).obj.obj (op Work.ATOM.pt))
    (↾((fun u : Work.ATOM.pt ⟶ NUI => Work.ANALYTIC.boundedSeq.obj.map u.op
        Work.ANALYTIC.deltaElem) :
        (Work.ATOM.pt ⟶ NUI) → ↥((Work.ANALYTIC.boundedSeq).obj.obj (op Work.ATOM.pt))))

/-! ## Canonicalising lemmas -/

theorem Gm_eq (S : LightProfinite.{0}) :
    Gm S = ModuleCat.freeDesc (↾fun u : Work.ATOM.pt ⟶ S =>
      Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree S) (Work.ATOM.zmap u)) := rfl

theorem Tm_eq :
    Tm = ModuleCat.freeDesc (X := (NUI.toCondensed).obj.obj (op Work.ATOM.pt))
      (↾((fun u : Work.ATOM.pt ⟶ NUI => Work.ANALYTIC.boundedSeq.obj.map u.op
          Work.ANALYTIC.deltaElem) :
          (Work.ATOM.pt ⟶ NUI) → ↥((Work.ANALYTIC.boundedSeq).obj.obj (op Work.ATOM.pt)))) := rfl

theorem Qmap_eq {S T : LightProfinite.{0}} (u : S ⟶ T) :
    Qmap u = ((Functor.whiskeringRight (LightProfinite.{0})ᵒᵖ (Type 0) (ModuleCat.{0} ℤ)).obj
      (ModuleCat.free ℤ)).map ((lightProfiniteToLightCondSet.map u).hom) := rfl

/-! ## Carrier arithmetic (`ModuleCat` sections) -/

theorem map_zsmul_module {A B : ModuleCat.{0} ℤ} (φ : A ⟶ B) (k : ℤ) (x : ↥A) :
    φ (k • x) = k • (φ x) :=
  map_zsmul (ModuleCat.Hom.hom φ) k x

theorem map_add_module {A B : ModuleCat.{0} ℤ} (φ : A ⟶ B) (x y : ↥A) :
    φ (x + y) = φ x + φ y :=
  map_add (ModuleCat.Hom.hom φ) x y

theorem map_zero_module {A B : ModuleCat.{0} ℤ} (φ : A ⟶ B) : φ (0 : ↥A) = 0 :=
  map_zero (ModuleCat.Hom.hom φ)

theorem carrier_smul_add {M : ModuleCat.{0} ℤ} (k : ℤ) (x y : ↥M) :
    k • (x + y) = k • x + k • y := by
  rw [zsmul_add]

theorem carrier_add_smul {M : ModuleCat.{0} ℤ} (a b : ℤ) (x : ↥M) :
    (a + b) • x = a • x + b • x := by
  rw [add_zsmul]

theorem carrier_smul_smul {M : ModuleCat.{0} ℤ} (a b : ℤ) (x : ↥M) :
    a • (b • x) = (a * b) • x :=
  (mul_zsmul x a b).symm

theorem carrier_smul_comm {M : ModuleCat.{0} ℤ} (a b : ℤ) (x : ↥M) :
    a • (b • x) = b • (a • x) := by
  rw [carrier_smul_smul _ _ _, carrier_smul_smul _ _ _, mul_comm]

theorem carrier_smul_zero {M : ModuleCat.{0} ℤ} (k : ℤ) : k • (0 : ↥M) = 0 := by
  rw [zsmul_zero]

/-! ## The generator computations -/

theorem zmap_id (S : LightProfinite.{0}) :
    Work.ATOM.zmap (𝟙 S) = 𝟙 (Work.ATOM.zfree S) :=
  CategoryTheory.Functor.map_id _ _

-- the sheafification-map of `Qmap u` is `zmap u`
theorem zmap_hom_sheafifyMap {S T : LightProfinite.{0}} (u : S ⟶ T) :
    (Work.ATOM.zmap u).hom = CategoryTheory.sheafifyMap J (Qmap u) := rfl


/-! ## The values of `Gm` and `Tm` on the basis elements -/

theorem Gm_freeMk (S : LightProfinite.{0}) (u : Work.ATOM.pt ⟶ S) :
    (Gm S) (Finsupp.single u 1)
      = Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree S) (Work.ATOM.zmap u) :=
  ModuleCat.freeDesc_apply (↾fun u : Work.ATOM.pt ⟶ S =>
    Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree S) (Work.ATOM.zmap u)) u

theorem Tm_freeMk (u : Work.ATOM.pt ⟶ NUI) :
    Tm (Finsupp.single u 1)
      = Work.ANALYTIC.boundedSeq.obj.map u.op Work.ANALYTIC.deltaElem :=
  ModuleCat.freeDesc_apply (X := (NUI.toCondensed).obj.obj (op Work.ATOM.pt))
    (↾((fun u : Work.ATOM.pt ⟶ NUI => Work.ANALYTIC.boundedSeq.obj.map u.op
        Work.ANALYTIC.deltaElem) :
        (Work.ATOM.pt ⟶ NUI) → ↥((Work.ANALYTIC.boundedSeq).obj.obj (op Work.ATOM.pt)))) u


/-- The generator identification on the presheaf level: the map of sectionwise free presheaves
induced by `u` sends the basis element at `𝟙 ∗` to the basis element at `u`. -/
theorem Qmap_single {S : LightProfinite.{0}} (u : Work.ATOM.pt ⟶ S) :
    (Qmap u).app (op Work.ATOM.pt) (Finsupp.single (𝟙 Work.ATOM.pt) 1)
      = Finsupp.single u 1 := by
  simp only [Qmap, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
  exact ModuleCat.free_map_apply
    ((lightProfiniteToLightCondSet.map u).hom.app (op Work.ATOM.pt)) (𝟙 Work.ATOM.pt)


end Work.ANALYTIC
