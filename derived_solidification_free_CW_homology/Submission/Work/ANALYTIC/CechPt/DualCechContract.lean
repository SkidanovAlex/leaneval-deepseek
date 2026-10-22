import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualComplex
import Submission.Work.ANALYTIC.CechPt.DualCechSetup
import Submission.Work.ANALYTIC.CechPt.dualCech_exact
import Submission.Work.ANALYTIC.CechPt.dualCech_free
import Submission.Work.ANALYTIC.CechPt.contraction_of_exact
import Submission.Work.ANALYTIC.CechPt.DualCechBridge
import Submission.Work.ANALYTIC.CechPt.free_submodule_of_free
import Submission.Work.ANALYTIC.CechPt.sdBridge_natural

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section
set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt
open Work.ANALYTIC

/-! ## `pre` is ℤ-linear -/

theorem pre_neg' {A B : LightCondAb} (f : B ⟶ A) :
    MonoidalClosed.pre (-f) = -MonoidalClosed.pre f := by
  have h : MonoidalClosed.pre (-f) + MonoidalClosed.pre f = 0 := by
    rw [← pre_add, neg_add_cancel, pre_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem pre_zsmul' {A B : LightCondAb} (c : ℤ) (f : B ⟶ A) :
    MonoidalClosed.pre (c • f) = c • MonoidalClosed.pre f := by
  have hnat : ∀ n : ℕ, MonoidalClosed.pre ((n : ℤ) • f) = (n : ℤ) • MonoidalClosed.pre f := by
    intro n
    induction n with
    | zero => simp [pre_zero]
    | succ n ih =>
      rw [Nat.cast_succ, add_smul, one_smul, pre_add, ih, add_smul, one_smul]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg c
  · rw [hn]; exact hnat n
  · rw [hn, neg_smul, neg_smul, pre_neg', hnat n]

theorem pre_sum' {A B : LightCondAb} {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (u : ι → (B ⟶ A)) :
    MonoidalClosed.pre (∑ i ∈ s, c i • u i) =
      ∑ i ∈ s, c i • MonoidalClosed.pre (u i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pre_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, pre_add, ih, pre_zsmul']

/-! ## Sums of locally constant functions -/

theorem lc_sum_apply' {ι : Type*} (s : Finset ι) {X : Type*} [TopologicalSpace X]
    (ψ : ι → LocallyConstant X ℤ) (x : X) :
    (∑ i ∈ s, ψ i) x = ∑ i ∈ s, ψ i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LocallyConstant.add_apply, ih]

/-! ## The discrete locally constant functor is additive -/

theorem lcDiscFunctor_additive : (LightCondMod.LocallyConstant.functor ℤ).Additive := by
  haveI : (LightCondensed.discrete (ModuleCat.{0} ℤ)).Additive :=
    inferInstanceAs (constantSheaf (coherentTopology LightProfinite.{0})
      (ModuleCat.{0} ℤ)).Additive
  exact Functor.additive_of_iso (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).symm

/-! ## `ModuleCat.ofHom` is additive -/

theorem ofHom_add' {M N : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (φ ψ : M →ₗ[ℤ] N) :
    ModuleCat.ofHom (φ + ψ) = ModuleCat.ofHom φ + ModuleCat.ofHom ψ := by
  ext x
  rfl

theorem ofHom_smul' {M N : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (c : ℤ) (φ : M →ₗ[ℤ] N) :
    ModuleCat.ofHom (c • φ) = c • ModuleCat.ofHom φ := by
  ext x
  rfl

theorem ofHom_sum' (n : ℕ) (c : Fin n → ℤ) {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (φ : Fin n → (M →ₗ[ℤ] N)) :
    ModuleCat.ofHom (∑ i : Fin n, c i • φ i) = ∑ i : Fin n, c i • ModuleCat.ofHom (φ i) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, ofHom_add', ofHom_smul', ih]

/-! ## The `lcDisc`-model of the bridge and of the transferred maps -/

/-- Pullback of locally constant `ℤ`-valued functions along a face map. -/
noncomputable def facePull (p : ℕ) (i : Fin (p + 2)) : DualC p →ₗ[ℤ] DualC (p + 1) :=
  LocallyConstant.comapₗ ℤ (cechFace p i).hom.hom

/-- The `lcDisc`-model of a morphism of `ℤ`-modules. -/
noncomputable def lcDiscMapMod {M N : ModuleCat.{0} ℤ} (φ : M ⟶ N) :
    Work.DISC.lcDisc M ⟶ Work.DISC.lcDisc N :=
  (LightCondMod.LocallyConstant.functor ℤ).map φ

theorem lcDiscMapMod_comp {M N P : ModuleCat.{0} ℤ} (φ : M ⟶ N) (ψ : N ⟶ P) :
    lcDiscMapMod φ ≫ lcDiscMapMod ψ = lcDiscMapMod (φ ≫ ψ) := by
  rw [lcDiscMapMod, lcDiscMapMod, lcDiscMapMod, ← Functor.map_comp]

theorem lcDiscMapMod_add {M N : ModuleCat.{0} ℤ} (φ ψ : M ⟶ N) :
    lcDiscMapMod (φ + ψ) = lcDiscMapMod φ + lcDiscMapMod ψ := by
  haveI := lcDiscFunctor_additive
  rw [lcDiscMapMod, lcDiscMapMod, lcDiscMapMod, Functor.map_add]

theorem lcDiscMapMod_id (M : ModuleCat.{0} ℤ) :
    lcDiscMapMod (𝟙 M) = 𝟙 (Work.DISC.lcDisc M) :=
  CategoryTheory.Functor.map_id (LightCondMod.LocallyConstant.functor ℤ) M

theorem lcDiscMapMod_sum (n : ℕ) (c : Fin n → ℤ) {M N : ModuleCat.{0} ℤ}
    (φ : Fin n → (M ⟶ N)) :
    lcDiscMapMod (∑ i : Fin n, c i • φ i) = ∑ i : Fin n, c i • lcDiscMapMod (φ i) := by
  haveI := lcDiscFunctor_additive
  rw [lcDiscMapMod, Functor.map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Functor.map_zsmul]; rfl

/-- The `lcDisc`-model of a map between dual Čech groups (indexed by the Čech level). -/
noncomputable def cMap (p q : ℕ) (φ : DualC p →ₗ[ℤ] DualC q) :
    Work.DISC.lcDisc (ModuleCat.of ℤ (DualC p)) ⟶
      Work.DISC.lcDisc (ModuleCat.of ℤ (DualC q)) :=
  lcDiscMapMod (ModuleCat.ofHom φ)

/-- The `lcDisc`-model of the augmentation `ℤ ⟶ C(C_0,ℤ)`. -/
noncomputable def cMapIn (φ : ℤ →ₗ[ℤ] DualC 0) :
    Work.DISC.lcDisc (ModuleCat.of ℤ ℤ) ⟶
      Work.DISC.lcDisc (ModuleCat.of ℤ (DualC 0)) :=
  lcDiscMapMod (ModuleCat.ofHom φ)

/-- The `lcDisc`-model of a map `C(C_0,ℤ) ⟶ ℤ`. -/
noncomputable def cMapOut (φ : DualC 0 →ₗ[ℤ] ℤ) :
    Work.DISC.lcDisc (ModuleCat.of ℤ (DualC 0)) ⟶
      Work.DISC.lcDisc (ModuleCat.of ℤ ℤ) :=
  lcDiscMapMod (ModuleCat.ofHom φ)

theorem lcDiscMapMod_ofHom_id {M : ModuleCat.{0} ℤ} :
    lcDiscMapMod (ModuleCat.ofHom (LinearMap.id : ↥M →ₗ[ℤ] ↥M)) = 𝟙 (Work.DISC.lcDisc M) := by
  rw [show ModuleCat.ofHom (LinearMap.id : ↥M →ₗ[ℤ] ↥M) = 𝟙 M from rfl, lcDiscMapMod_id]

theorem cMap_comp {p q r : ℕ} (φ : DualC p →ₗ[ℤ] DualC q) (ψ : DualC q →ₗ[ℤ] DualC r) :
    cMap p q φ ≫ cMap q r ψ = cMap p r (ψ.comp φ) := by
  rw [cMap, cMap, cMap, lcDiscMapMod_comp, ModuleCat.ofHom_comp]

theorem cMap_sum (p q n : ℕ) (c : Fin n → ℤ) (φ : Fin n → (DualC p →ₗ[ℤ] DualC q)) :
    cMap p q (∑ i : Fin n, c i • φ i) = ∑ i : Fin n, c i • cMap p q (φ i) := by
  haveI := lcDiscFunctor_additive
  show lcDiscMapMod (ModuleCat.ofHom (∑ i : Fin n, c i • φ i)) =
    ∑ i : Fin n, c i • lcDiscMapMod (ModuleCat.ofHom (φ i))
  rw [ofHom_sum', lcDiscMapMod_sum]

/-- The bridge, stated in the `lcDisc`-model. -/
noncomputable def sdBridgeL (T : LightProfinite.{0}) :
    sd (zf T) ≅ Work.DISC.lcDisc (ModuleCat.of ℤ (LocallyConstant ↥T.toTop ℤ)) :=
  (CategoryTheory.ihom (Work.DISC.zfree T)).mapIso (lcDiscIntIso.symm) ≪≫
    @asIso _ _ _ _ (sdIsoHom T (ModuleCat.of ℤ ℤ)) (sdIsoHom_isIso T _)

/-! ## Sum expansions of the differentials -/

theorem dualD_eq_sum (p : ℕ) :
    dualD p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • facePull p i := by
  ext f x
  rw [dualD_apply, LinearMap.sum_apply, lc_sum_apply']
  apply Finset.sum_congr rfl
  intro i _
  have h2 : (facePull p i f) x = f ((cechFace p i) x) := rfl
  rw [LinearMap.smul_apply, LocallyConstant.smul_apply, smul_eq_mul, h2]

theorem dR_eq_sum (p : ℕ) :
    dR p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • Work.ATOM.zmap (cechFace p i) := rfl

theorem dE_eq_sum (p : ℕ) :
    dE p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
      (MonoidalClosed.pre (Work.ATOM.zmap (cechFace p i))).app (𝟙_ LightCondAb) := by
  rw [dE, dR_eq_sum, pre_sum', CategoryTheory.NatTrans.app_sum]
  exact Finset.sum_congr rfl (fun i _ => CategoryTheory.NatTrans.app_zsmul _ _ _)

/-! ## The differential compatibility -/

theorem hstep {p : ℕ} (i : Fin (p + 2))
    (hNat : (sdBridge (cechTerm p)).hom ≫
        (LightCondMod.LocallyConstant.functor ℤ).map
          (ModuleCat.ofHom (facePull p i))
        = (MonoidalClosed.pre (Work.ATOM.zmap (cechFace p i))).app (𝟙_ LightCondAb) ≫
          (sdBridge (cechTerm (p + 1))).hom) :
    (sdBridgeL (cechTerm p)).hom ≫ cMap p (p + 1) (facePull p i)
      = (MonoidalClosed.pre (Work.ATOM.zmap (cechFace p i))).app (𝟙_ LightCondAb) ≫
        (sdBridgeL (cechTerm (p + 1))).hom := by
  show (sdBridge (cechTerm p)).hom ≫
      (LightCondMod.LocallyConstant.functor ℤ).map (ModuleCat.ofHom (facePull p i))
      = (MonoidalClosed.pre (Work.ATOM.zmap (cechFace p i))).app (𝟙_ LightCondAb) ≫
        (sdBridge (cechTerm (p + 1))).hom
  exact hNat

theorem sdBridge_dE
    (hNat : ∀ (S T : LightProfinite.{0}) (f : S ⟶ T),
      (sdBridge T).hom ≫
        (LightCondMod.LocallyConstant.functor ℤ).map
          (ModuleCat.ofHom (LocallyConstant.comapₗ ℤ f.hom.hom))
        = (MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb) ≫ (sdBridge S).hom)
    (p : ℕ) :
    (sdBridgeL (cechTerm p)).hom ≫ cMap p (p + 1) (dualD p)
      = dE p ≫ (sdBridgeL (cechTerm (p + 1))).hom := by
  haveI := lcDiscFunctor_additive
  have h1 : cMap p (p + 1) (dualD p) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • cMap p (p + 1) (facePull p i) := by
    rw [dualD_eq_sum, cMap_sum]
  rw [h1, dE_eq_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul, hstep i (hNat (cechTerm (p + 1)) (cechTerm p) (cechFace p i)),
    Preadditive.zsmul_comp]


/-! ## The assembly -/

theorem dualAug_injective : Function.Injective dualAug := by
  intro k l hkl
  obtain ⟨x⟩ := cechTerm_nonempty 0
  have h := congrFun (congrArg (fun f : DualC 0 => (f : ↥(cechTerm 0) → ℤ)) hkl) x
  simpa using h

theorem cancel_iso_left {X Y Z : LightCondAb} (e : X ≅ Y) (f : Y ⟶ Z) :
    e.inv ≫ e.hom ≫ f = f := by
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem cancel_iso_right {X Y Z : LightCondAb} (e : X ≅ Y) (f : Z ⟶ X) :
    f ≫ e.hom ≫ e.inv = f := by
  rw [Iso.hom_inv_id, Category.comp_id]

theorem cancel_iso_left' {X Y Z : LightCondAb} (e : X ≅ Y) (f : X ⟶ Z) :
    e.hom ≫ e.inv ≫ f = f := by
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem cancel_iso_right' {X Y Z : LightCondAb} (e : X ≅ Y) (f : Z ⟶ Y) :
    f ≫ e.inv ≫ e.hom = f := by
  rw [Iso.inv_hom_id, Category.comp_id]

theorem conj_eq_one {X Y : LightCondAb} (e : X ≅ Y) (f : X ⟶ X)
    (h : e.inv ≫ f ≫ e.hom = 𝟙 Y) : f = 𝟙 X := by
  have h2 : e.hom ≫ (e.inv ≫ f ≫ e.hom) ≫ e.inv = 𝟙 X := by
    rw [h, Category.id_comp]
    exact Iso.hom_inv_id e
  rw [← h2]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem conj_add {X Y : LightCondAb} (e : X ≅ Y) (f g : X ⟶ X) :
    e.inv ≫ (f + g) ≫ e.hom = e.inv ≫ f ≫ e.hom + e.inv ≫ g ≫ e.hom := by
  rw [Preadditive.add_comp]
  rw [Preadditive.comp_add]

theorem cMapIn_cMapOut (φ : ℤ →ₗ[ℤ] DualC 0) (ψ : DualC 0 →ₗ[ℤ] ℤ) :
    cMapIn φ ≫ cMapOut ψ = lcDiscMapMod (ModuleCat.ofHom (ψ.comp φ)) := by
  show lcDiscMapMod (ModuleCat.ofHom φ) ≫ lcDiscMapMod (ModuleCat.ofHom ψ) =
    lcDiscMapMod (ModuleCat.ofHom (ψ.comp φ))
  rw [lcDiscMapMod_comp]
  exact congrArg lcDiscMapMod (ModuleCat.ofHom_comp φ ψ).symm

/-- The other order of the pair `(augmentation, splitting)`: the composite
`C(C_0,ℤ) ⟶ ℤ ⟶ C(C_0,ℤ)` is the image of `dualAug.comp h0` under `lcDisc`. -/
theorem cMapOut_cMapIn (φ : ℤ →ₗ[ℤ] DualC 0) (ψ : DualC 0 →ₗ[ℤ] ℤ) :
    cMapOut ψ ≫ cMapIn φ = cMap 0 0 (φ.comp ψ) := by
  show lcDiscMapMod (ModuleCat.ofHom ψ) ≫ lcDiscMapMod (ModuleCat.ofHom φ) =
    lcDiscMapMod (ModuleCat.ofHom (φ.comp ψ))
  rw [lcDiscMapMod_comp]
  exact congrArg lcDiscMapMod (ModuleCat.ofHom_comp ψ φ).symm

/-- `cMap` is additive in its linear-map argument. -/
theorem cMap_add {p q : ℕ} (φ ψ : DualC p →ₗ[ℤ] DualC q) :
    cMap p q (φ + ψ) = cMap p q φ + cMap p q ψ := by
  show lcDiscMapMod (ModuleCat.ofHom (φ + ψ)) =
    lcDiscMapMod (ModuleCat.ofHom φ) + lcDiscMapMod (ModuleCat.ofHom ψ)
  rw [ofHom_add', lcDiscMapMod_add]

/-- `cMap` of the identity is the identity. -/
theorem cMap_id (p : ℕ) :
    cMap p p (LinearMap.id : DualC p →ₗ[ℤ] DualC p) =
      𝟙 (Work.DISC.lcDisc (ModuleCat.of ℤ (DualC p))) := by
  show lcDiscMapMod (ModuleCat.ofHom (LinearMap.id : DualC p →ₗ[ℤ] DualC p)) =
    𝟙 (Work.DISC.lcDisc (ModuleCat.of ℤ (DualC p)))
  rw [show ModuleCat.ofHom (LinearMap.id : DualC p →ₗ[ℤ] DualC p) =
    𝟙 (ModuleCat.of ℤ (DualC p)) from rfl]
  exact lcDiscMapMod_id _

theorem final_assembly
    (hNat : ∀ (S T : LightProfinite.{0}) (f : S ⟶ T),
      (sdBridge T).hom ≫
        (LightCondMod.LocallyConstant.functor ℤ).map
          (ModuleCat.ofHom (LocallyConstant.comapₗ ℤ f.hom.hom))
        = (MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb) ≫ (sdBridge S).hom)
    (hRho : rho ≫ (sdBridge (cechTerm 0)).hom
      = lcDiscIntIso.inv ≫
        (LightCondMod.LocallyConstant.functor ℤ).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (LocallyConstant ↥(cechTerm 0) ℤ)
            (1 : LocallyConstant ↥(cechTerm 0) ℤ))))
    (hfree : ∀ p : ℕ, Module.Free ℤ (LinearMap.ker (dualD p))) :
    DualAugContractible := by
  obtain ⟨h, h0, h0aug, hbase, hchain⟩ :=
    contraction_of_exact DualC dualD dualAug dualAug_injective
      dualCech_exact.1 dualCech_exact.2 hfree
  have hform : cMapIn dualAug =
      (LightCondMod.LocallyConstant.functor ℤ).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (LocallyConstant ↥(cechTerm 0) ℤ)
          (1 : LocallyConstant ↥(cechTerm 0) ℤ))) := rfl
  have hiso : sdBridgeL (cechTerm 0) = sdBridge (cechTerm 0) := rfl
  -- the clean form of the augmentation compatibility
  have hρ : rho = lcDiscIntIso.inv ≫ cMapIn dualAug ≫ (sdBridgeL (cechTerm 0)).inv := by
    have h1 : rho ≫ (sdBridgeL (cechTerm 0)).hom = lcDiscIntIso.inv ≫ cMapIn dualAug := by
      rw [hiso]; exact hRho.trans (by rw [hform])
    calc rho = (rho ≫ (sdBridgeL (cechTerm 0)).hom) ≫ (sdBridgeL (cechTerm 0)).inv := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [h1]; rw [Category.assoc]
  refine ⟨(sdBridgeL (cechTerm 0)).hom ≫ cMapOut h0 ≫ lcDiscIntIso.hom,
    fun q => (sdBridgeL (cechTerm (q + 1))).hom ≫ cMap (q + 1) q (h q) ≫
      (sdBridgeL (cechTerm q)).inv, ?_, ?_, ?_⟩
  · -- `rho ≫ t₀ = 1`
    have hcomp : cMapIn dualAug ≫ cMapOut h0 = lcDiscMapMod (ModuleCat.ofHom (h0.comp dualAug)) :=
      cMapIn_cMapOut dualAug h0
    rw [hρ]
    simp only [Category.assoc]
    rw [← Category.assoc (f := (sdBridgeL (cechTerm 0)).inv), Iso.inv_hom_id, Category.id_comp]
    rw [← Category.assoc (f := cMapIn dualAug), hcomp]
    rw [show h0.comp dualAug = LinearMap.id from h0aug]
    rw [show lcDiscMapMod (ModuleCat.ofHom (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) = 𝟙 _ from
      lcDiscMapMod_ofHom_id (M := ModuleCat.of ℤ ℤ)]
    rw [Category.id_comp, Iso.inv_hom_id]
  · -- `dE 0 ≫ t 0 + t₀ ≫ rho = 1`
    apply conj_eq_one (sdBridgeL (cechTerm 0))
    rw [conj_add]
    -- first summand
    have hf : (sdBridgeL (cechTerm 0)).inv ≫
          (dE 0 ≫ (sdBridgeL (cechTerm (0 + 1))).hom ≫ cMap (0 + 1) 0 (h 0) ≫
            (sdBridgeL (cechTerm 0)).inv) ≫ (sdBridgeL (cechTerm 0)).hom =
        cMap 0 (0 + 1) (dualD 0) ≫ cMap (0 + 1) 0 (h 0) := by
      simp only [Category.assoc]
      rw [cancel_iso_right' (sdBridgeL (cechTerm 0)) (cMap (0 + 1) 0 (h 0))]
      rw [← Category.assoc (f := dE 0), ← sdBridge_dE hNat 0]
      simp only [Category.assoc]
      rw [cancel_iso_left (sdBridgeL (cechTerm 0))
        (cMap 0 (0 + 1) (dualD 0) ≫ cMap (0 + 1) 0 (h 0))]
    -- second summand
    have hg : (sdBridgeL (cechTerm 0)).inv ≫
          (((sdBridgeL (cechTerm 0)).hom ≫ cMapOut h0 ≫ lcDiscIntIso.hom) ≫ rho) ≫
            (sdBridgeL (cechTerm 0)).hom = cMapOut h0 ≫ cMapIn dualAug := by
      rw [hρ]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
      rw [Iso.inv_hom_id, Category.comp_id]
    rw [hf, hg, cMap_comp (dualD 0) (h 0), cMapOut_cMapIn dualAug h0]
    rw [← cMap_add, show (h 0).comp (dualD 0) + dualAug.comp h0 = LinearMap.id from hbase]
    exact cMap_id 0
  · -- the general identity
    intro r
    apply conj_eq_one (sdBridgeL (cechTerm (r + 1)))
    rw [conj_add]
    have hf : (sdBridgeL (cechTerm (r + 1))).inv ≫
          (dE (r + 1) ≫ (sdBridgeL (cechTerm (r + 1 + 1))).hom ≫
            cMap (r + 1 + 1) (r + 1) (h (r + 1)) ≫ (sdBridgeL (cechTerm (r + 1))).inv) ≫
          (sdBridgeL (cechTerm (r + 1))).hom =
        cMap (r + 1) (r + 1 + 1) (dualD (r + 1)) ≫ cMap (r + 1 + 1) (r + 1) (h (r + 1)) := by
      rw [← Category.assoc (f := dE (r + 1)), ← sdBridge_dE hNat (r + 1)]
      simp only [Category.assoc]
      rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    have hg : (sdBridgeL (cechTerm (r + 1))).inv ≫
          (((sdBridgeL (cechTerm (r + 1))).hom ≫ cMap (r + 1) r (h r) ≫
            (sdBridgeL (cechTerm r)).inv) ≫ dE r) ≫ (sdBridgeL (cechTerm (r + 1))).hom =
        cMap (r + 1) r (h r) ≫ cMap r (r + 1) (dualD r) := by
      simp only [Category.assoc]
      rw [← sdBridge_dE hNat r, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    rw [hf, hg, cMap_comp (dualD (r + 1)) (h (r + 1)), cMap_comp (h r) (dualD r)]
    rw [← cMap_add, show (h (r + 1)).comp (dualD (r + 1)) + (dualD r).comp (h r) =
      LinearMap.id from hchain r]
    exact cMap_id (r + 1)

end Work.ANALYTIC.CechPt
