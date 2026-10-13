import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Sheaf.Beta

/-!
# The Čech presheaf of the structure sheaf and its comparison isomorphisms

Let `X` be a scheme, `A` a commutative ring and `f : X ⟶ Spec A`.  The Čech presheaf
`DSMap.cechPresheaf A X f` is the functor `(X.Opens)ᵒᵖ ⥤ ModuleCat A` sending an open `V` to
the `A`-module `Γ(X, V)` (with its `A`-structure induced by `f`), with restriction maps the
restriction maps of the structure sheaf.

The sheaf-level model of the same presheaf (used in `DSF1`) is `V ↦ (V.ι)_* 𝒪_V`, the
pushforward of the structure sheaf of the open subscheme `V`, with restriction maps
`restr h` (`Submission.Work.DSF1.Sheaf.Beta`).  Its global sections are `Γ(X, V.ι ''ᵁ ⊤)`, and
the canonical identification `V ≅ V.ι ''ᵁ ⊤` induces an `A`-linear isomorphism with `Γ(X, V)`.

The main result of this file is that *any* functor `S` which agrees with `V ↦ (V.ι)_* 𝒪_V` on
objects and which sends each `homOfLE h` to (something heterogeneously equal to) `restr h`
becomes isomorphic to `cechPresheaf` after composing with the global-sections functor
`ΓA = Γ(X, -) : X.Modules ⥤ ModuleCat A`.
-/

namespace Work.DSF1.Sheaf

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits

variable {X : Scheme.{u}}

set_option maxHeartbeats 1000000 in
/-- `betaGen V V' g` is Mathlib's canonical structure morphism `𝒪_V ⟶ g_* 𝒪_{V'}`. -/
lemma betaGen_eq_unitToPushforwardObjUnit (V V' : X.Opens) (g : V'.toScheme ⟶ V.toScheme) :
    Work.DSF1.Sheaf.betaGen V V' g =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  refine (SheafOfModules.unitHomEquiv ((Scheme.Modules.pushforward g).obj
    (SheafOfModules.unit V'.toScheme.ringCatSheaf))).injective ?_
  ext W
  erw [SheafOfModules.unitHomEquiv_apply_coe]
  rw [Work.DSF1.Sheaf.betaGen]
  erw [← SheafOfModules.unitHomEquiv_apply_coe]
  rw [Equiv.apply_symm_apply]
  simp only [Work.DSF1.Sheaf.betaSect]
  conv_rhs => erw [SheafOfModules.unitHomEquiv_apply_coe]
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
  erw [SheafOfModules.unitHomEquiv_apply_coe]
  simp
  rfl

/-- On sections, `betaGen V V' g` is the ring map `g.app`. -/
lemma betaGen_app (V V' : X.Opens) (g : V'.toScheme ⟶ V.toScheme)
    (W : V.toScheme.Opens) (r : Γ(SheafOfModules.unit V.toScheme.ringCatSheaf, W)) :
    (Scheme.Modules.Hom.app (Work.DSF1.Sheaf.betaGen V V' g) W).hom r = (g.app W).hom r := by
  rw [betaGen_eq_unitToPushforwardObjUnit]
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]

/-- The module structure of `Γ(secSheaf V, W)` over `Γ(X, W)`: it is multiplication by the
restriction `V.ι.app W r` of the structure sheaf. -/
lemma secSheaf_smul (V : X.Opens) (W : X.Opens) (r : Γ(X, W))
    (x : Γ(Work.DSF1.secSheaf V, W)) :
    r • x = (show Γ(↑V, V.ι ⁻¹ᵁ W) from (V.ι.app W).hom r) *
            (show Γ(↑V, V.ι ⁻¹ᵁ W) from x) := rfl

set_option maxHeartbeats 1000000 in
/-- On global sections, the restriction map `restr h` of the Čech presheaf is the restriction
map of the structure sheaf. -/
lemma restr_app_top {V V' : X.Opens} (h : V' ≤ V) (x : Γ(Work.DSF1.secSheaf V, ⊤)) :
    (Scheme.Modules.Hom.app (Work.DSF1.Sheaf.restr h) ⊤).hom x =
      (X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op).hom x := by
  have hsecond' : ∀ (e' : ((X.homOfLE h ≫ V.ι) ⁻¹ᵁ (⊤ : X.Opens)) = (V'.ι ⁻¹ᵁ ⊤))
      (y : Γ(SheafOfModules.unit V'.toScheme.ringCatSheaf, (X.homOfLE h ≫ V.ι) ⁻¹ᵁ ⊤)),
      ((Scheme.Modules.presheaf (SheafOfModules.unit V'.toScheme.ringCatSheaf)).map (eqToHom e').op).hom y
        = y := by
    intro e' y
    rw [show eqToHom e' = 𝟙 _ from Subsingleton.elim _ _]
    erw [CategoryTheory.op_id]
    erw [CategoryTheory.Functor.map_id]
    rfl
  rw [Work.DSF1.Sheaf.restr]
  erw [Scheme.Modules.Hom.comp_app]
  erw [Scheme.Modules.pushforward_map_app]
  erw [Scheme.Modules.pushforwardCongr_hom_app_app]
  erw [AddCommGrpCat.hom_comp]
  erw [AddMonoidHom.comp_apply]
  erw [show _ = _ from hsecond' _ _]
  erw [show (Scheme.Modules.Hom.app (Work.DSF1.Sheaf.betaGen V V' (X.homOfLE h)) (V.ι ⁻¹ᵁ ⊤)).hom x
        = ((X.homOfLE h).app (V.ι ⁻¹ᵁ ⊤)).hom x from betaGen_app V V' (X.homOfLE h) (V.ι ⁻¹ᵁ ⊤) x]
  erw [Scheme.homOfLE_app]
  rfl

/-- The canonical identification `V ≅ V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤)`. -/
lemma opens_self (V : X.Opens) : V = V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)) := by simp

/-- The two restrictions `V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤) ← V` and `V ← V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤)` compose to the
identity. -/
lemma psiFun_comp_self (V : X.Opens) :
    (X.presheaf.map (eqToHom (opens_self V)).op) ≫
      (X.presheaf.map (eqToHom (opens_self V).symm).op) =
    𝟙 (X.presheaf.obj (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens))))) :=
  (X.presheaf.mapIso (Iso.op (eqToIso (opens_self V)))).hom_inv_id

/-- The reverse composite is the identity. -/
lemma psiFun_self_comp (V : X.Opens) :
    (X.presheaf.map (eqToHom (opens_self V).symm).op) ≫
      (X.presheaf.map (eqToHom (opens_self V)).op) = 𝟙 (X.presheaf.obj (op V)) :=
  (X.presheaf.mapIso (Iso.op (eqToIso (opens_self V)))).symm.hom_inv_id

/-- The two structure-sheaf restrictions `V ← ⊤` and `V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤) ← V` compose to
`V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤) ← ⊤`. -/
lemma restr_comp_eq (V : X.Opens) :
    (X.presheaf.map (homOfLE (le_top : V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)) ≤ ⊤)).op) ≫
      (X.presheaf.map (eqToHom (opens_self V)).op) =
    (X.presheaf.map (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op) := by
  rw [← Functor.map_comp]
  congr 1

section Psi

variable (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))

/-- The `A`-action on `↑(GammaA.obj (secSheaf V))` is multiplication by `phiU`. -/
lemma GammaA_smul_apply (V : X.Opens) (a : A)
    (x : ↑((DSMap.GammaA A X f).obj (Work.DSF1.secSheaf V))) :
    a • x = (show (X.presheaf.obj (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)))) : Type u) from
              (X.presheaf.map (homOfLE (le_top : V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)) ≤ ⊤)).op).hom
                (DSMap.phi A X f a)) *
            (show (X.presheaf.obj (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)))) : Type u) from x) := rfl

/-- The `A`-action on `↑(cechPresheaf.obj (op V))` is multiplication by `phiU`. -/
lemma cechPresheaf_smul_apply (V : X.Opens) (a : A)
    (y : ↑((DSMap.cechPresheaf A X f).obj (Opposite.op V))) :
    a • y = (X.presheaf.map (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op).hom (DSMap.phi A X f a) *
            (show ↑(X.presheaf.obj (op V)) from y) := rfl

/-- The "identity" comparison, in the `phiU`-form. -/
lemma psiFun_apply_phi (V : X.Opens) (a : A) :
    (X.presheaf.map (eqToHom (opens_self V)).op).hom
        ((X.presheaf.map (homOfLE (le_top : V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)) ≤ ⊤)).op).hom
          (DSMap.phi A X f a)) = DSMap.phiU A X f V a := by
  have h1 : (X.presheaf.map (eqToHom (opens_self V)).op).hom
        ((X.presheaf.map (homOfLE (le_top : V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)) ≤ ⊤)).op).hom
          (DSMap.phi A X f a)) =
      ((X.presheaf.map (homOfLE (le_top : V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)) ≤ ⊤)).op) ≫
        (X.presheaf.map (eqToHom (opens_self V)).op)).hom (DSMap.phi A X f a) := by
    rw [CommRingCat.hom_comp]
    rfl
  rw [h1, restr_comp_eq]
  rfl

/-- The `A`-linear "identity" `Γ(secSheaf V, ⊤) → Γ(X, V)`, through the canonical identification
of `V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤)` with `V`. -/
noncomputable def psiLM (V : X.Opens) :
    (↑((DSMap.GammaA A X f).obj (Work.DSF1.secSheaf V)) : Type u) →ₗ[A]
      (↑((DSMap.cechPresheaf A X f).obj (Opposite.op V)) : Type u) where
  toFun x := (X.presheaf.map (eqToHom (opens_self V)).op).hom x
  map_add' x y := map_add _ x y
  map_smul' a x := by
    show (X.presheaf.map (eqToHom (opens_self V)).op).hom (a • x) =
      a • (show ↑((DSMap.cechPresheaf A X f).obj (Opposite.op V)) from
        (X.presheaf.map (eqToHom (opens_self V)).op).hom x)
    rw [GammaA_smul_apply A X f V a x]
    rw [map_mul]
    rw [show (X.presheaf.map (eqToHom (opens_self V)).op).hom
          ((X.presheaf.map (homOfLE (le_top : V.ι ''ᵁ (V.ι ⁻¹ᵁ (⊤ : X.Opens)) ≤ ⊤)).op).hom
            (DSMap.phi A X f a)) = DSMap.phiU A X f V a from psiFun_apply_phi A X f V a]
    rw [cechPresheaf_smul_apply A X f V a ((X.presheaf.map (eqToHom (opens_self V)).op).hom x)]
    rfl

/-- `psiLM` is a bijection, by composing the two restrictions of the structure sheaf. -/
lemma psiLM_inv_left (V : X.Opens)
    (z : ↑((DSMap.GammaA A X f).obj (Work.DSF1.secSheaf V))) :
    (X.presheaf.map (eqToHom (opens_self V).symm).op).hom
      ((X.presheaf.map (eqToHom (opens_self V)).op).hom z) = z :=
  CommRingCat.inv_hom_apply (X.presheaf.mapIso (Iso.op (eqToIso (opens_self V)))) z

/-- The reverse composition is the identity as well. -/
lemma psiLM_inv_right (V : X.Opens)
    (z : ↑((DSMap.cechPresheaf A X f).obj (Opposite.op V))) :
    (X.presheaf.map (eqToHom (opens_self V)).op).hom
      ((X.presheaf.map (eqToHom (opens_self V).symm).op).hom z) = z :=
  CommRingCat.hom_inv_apply (X.presheaf.mapIso (Iso.op (eqToIso (opens_self V)))) z

/-- The underlying function of `psiLM` is bijective. -/
lemma psiLM_bijective (V : X.Opens) : Function.Bijective (psiLM A X f V) :=
  ⟨fun x y hxy => by
    have h1 := congrArg (fun w =>
      (X.presheaf.map (eqToHom (opens_self V).symm).op).hom w) hxy
    exact (psiLM_inv_left A X f V x).symm.trans (h1.trans (psiLM_inv_left A X f V y)),
   fun y => ⟨(X.presheaf.map (eqToHom (opens_self V).symm).op).hom y,
     psiLM_inv_right A X f V y⟩⟩

/-- The comparison linear equivalence `Γ(secSheaf V, ⊤) ≃ₗ[A] Γ(X, V)`. -/
noncomputable def psiEquiv (V : X.Opens) :
    (↑((DSMap.GammaA A X f).obj (Work.DSF1.secSheaf V)) : Type u) ≃ₗ[A]
      (↑((DSMap.cechPresheaf A X f).obj (Opposite.op V)) : Type u) where
  toLinearMap := psiLM A X f V
  invFun y := (X.presheaf.map (eqToHom (opens_self V).symm).op).hom y
  left_inv x := psiLM_inv_left A X f V x
  right_inv y := psiLM_inv_right A X f V y

/-- The comparison isomorphism `Γ(secSheaf V, ⊤) ≅ Γ(X, V)` of `A`-modules. -/
noncomputable def psi (V : X.Opens) : (DSMap.GammaA A X f).obj (Work.DSF1.secSheaf V) ≅
    (DSMap.cechPresheaf A X f).obj (Opposite.op V) :=
  LinearEquiv.toModuleIso (psiEquiv A X f V)

/-- The `psi`-comparison is given by the restriction along `opens_self V`. -/
lemma psi_hom_apply (V : X.Opens)
    (x : ↑((DSMap.GammaA A X f).obj (Work.DSF1.secSheaf V))) :
    (psi A X f V).hom.hom x = (X.presheaf.map (eqToHom (opens_self V)).op).hom x := rfl

set_option maxHeartbeats 4000000 in
/-- Naturality of `psi` with respect to the restriction maps of the structure sheaf. -/
lemma psi_naturality {V V' : X.Opens} (h : V' ≤ V) :
    (DSMap.GammaA A X f).map (Work.DSF1.Sheaf.restr h) ≫ (psi A X f V').hom =
      (psi A X f V).hom ≫ (DSMap.cechPresheaf A X f).map (CategoryTheory.homOfLE h).op := by
  apply ModuleCat.hom_ext
  ext x
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [show (DSMap.GammaA A X f).map (Work.DSF1.Sheaf.restr h) x
      = (Scheme.Modules.Hom.app (Work.DSF1.Sheaf.restr h) ⊤).hom x from by
        erw [ModuleCat.restrictScalars.map_apply]]
  rw [restr_app_top h x]
  rw [show (psi A X f V').hom.hom
        ((X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op).hom x)
      = (X.presheaf.map (eqToHom (opens_self V')).op).hom
          ((X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op).hom x)
      from psi_hom_apply A X f V' _]
  rw [show (psi A X f V).hom.hom x = (X.presheaf.map (eqToHom (opens_self V)).op).hom x
      from psi_hom_apply A X f V x]
  rw [show (DSMap.cechPresheaf A X f).map (CategoryTheory.homOfLE h).op
        ((X.presheaf.map (eqToHom (opens_self V)).op).hom x)
      = (X.presheaf.map (CategoryTheory.homOfLE h).op).hom
          ((X.presheaf.map (eqToHom (opens_self V)).op).hom x) from rfl]
  have hL : (X.presheaf.map (eqToHom (opens_self V')).op).hom
        ((X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op).hom x)
      = ((X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op) ≫
          (X.presheaf.map (eqToHom (opens_self V')).op)).hom x := by
    rw [CommRingCat.hom_comp]
    rfl
  have hR : (X.presheaf.map (CategoryTheory.homOfLE h).op).hom
        ((X.presheaf.map (eqToHom (opens_self V)).op).hom x)
      = ((X.presheaf.map (eqToHom (opens_self V)).op) ≫
          (X.presheaf.map (CategoryTheory.homOfLE h).op)).hom x := by
    rw [CommRingCat.hom_comp]
    rfl
  rw [hL, hR]
  have key : (X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op) ≫
        (X.presheaf.map (eqToHom (opens_self V')).op)
      = (X.presheaf.map (eqToHom (opens_self V)).op) ≫
        (X.presheaf.map (CategoryTheory.homOfLE h).op) :=
    (Functor.map_comp X.presheaf (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op
        (eqToHom (opens_self V')).op).symm.trans
      ((congrArg (fun γ => X.presheaf.map γ)
          (Subsingleton.elim ((homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op ≫
              (eqToHom (opens_self V')).op)
            ((eqToHom (opens_self V)).op ≫ (CategoryTheory.homOfLE h).op))).trans
        (Functor.map_comp X.presheaf (eqToHom (opens_self V)).op
          (CategoryTheory.homOfLE h).op))
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom key) x

end Psi

theorem gammaCechPresheaf (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (S : CategoryTheory.Functor (Opposite (X.Opens)) (AlgebraicGeometry.Scheme.Modules X))
    (hobj : ∀ V : X.Opens, S.obj (Opposite.op V) = Work.DSF1.secSheaf V)
    (hmap : ∀ ⦃V V' : X.Opens⦄ (h : V' ≤ V),
      HEq (S.map (CategoryTheory.homOfLE h).op) (Work.DSF1.Sheaf.restr h)) :
    Nonempty (CategoryTheory.Iso
      (CategoryTheory.Functor.comp S (DSMap.GammaA A X f)) (DSMap.cechPresheaf A X f)) :=
  set_option backward.isDefEq.respectTransparency false in by
  classical
  refine ⟨NatIso.ofComponents (fun V => eqToIso (congrArg
      (fun M => (DSMap.GammaA A X f).obj M) (hobj V.unop)) ≪≫ psi A X f V.unop) ?_⟩
  intro V W g
  change (DSMap.GammaA A X f).map (S.map g) ≫
      (eqToIso (congrArg (fun M => (DSMap.GammaA A X f).obj M) (hobj W.unop)) ≪≫
        psi A X f W.unop).hom =
    (eqToIso (congrArg (fun M => (DSMap.GammaA A X f).obj M) (hobj V.unop)) ≪≫
        psi A X f V.unop).hom ≫ (DSMap.cechPresheaf A X f).map g
  simp only [Iso.trans_hom, eqToIso.hom]
  have hle : W.unop ≤ V.unop := CategoryTheory.leOfHom g.unop
  have hg : g = (CategoryTheory.homOfLE hle).op := rfl
  rw [hg]
  rw [show S.map (CategoryTheory.homOfLE hle).op
      = eqToHom (hobj V.unop) ≫ Work.DSF1.Sheaf.restr hle ≫ eqToHom (hobj W.unop).symm
      from (CategoryTheory.conj_eqToHom_iff_heq _ _ (hobj V.unop) (hobj W.unop)).2 (hmap hle)]
  rw [Functor.map_comp, Functor.map_comp]
  rw [CategoryTheory.eqToHom_map (DSMap.GammaA A X f) (hobj V.unop)]
  have hcancel : ∀ {Z : ModuleCat A}
      (e : (DSMap.GammaA A X f).obj (Work.DSF1.secSheaf W.unop) ⟶ Z),
      (DSMap.GammaA A X f).map (eqToHom (hobj W.unop).symm) ≫
        eqToHom (congrArg (fun M => (DSMap.GammaA A X f).obj M) (hobj W.unop)) ≫ e = e := by
    intro Z e
    have h0 : (DSMap.GammaA A X f).map (eqToHom (hobj W.unop).symm) ≫
        eqToHom (congrArg (fun M => (DSMap.GammaA A X f).obj M) (hobj W.unop)) = 𝟙 _ := by
      rw [CategoryTheory.eqToHom_map]
      rw [CategoryTheory.eqToHom_trans]
      rw [show (congrArg (fun M => (DSMap.GammaA A X f).obj M) (hobj W.unop).symm).trans
            (congrArg (fun M => (DSMap.GammaA A X f).obj M) (hobj W.unop)) = rfl
          from Subsingleton.elim _ _]
      rw [CategoryTheory.eqToHom_refl]
    rw [← Category.assoc, h0, Category.id_comp]
  simp only [Category.assoc]
  rw [hcancel]
  rw [psi_naturality A X f hle]

end Work.DSF1.Sheaf
