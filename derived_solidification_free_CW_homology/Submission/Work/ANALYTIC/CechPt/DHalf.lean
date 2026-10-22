import Mathlib
import Submission.Work.ANALYTIC.CechPt.SolidChain
import Submission.Work.ANALYTIC.CechPt.DualComplex
import Submission.Work.ANALYTIC.CechPt.CoordDefs

/-!
# The solid Čech complex of the Cantor cover is a resolution of `ℤ`

This module constructs the augmentation `augCan : Dcpx ⟶ ℤ` of the *solid* Čech complex of the
Cantor cover (the transpose of the "constant function `1`" `rho` of `CechPt/DualComplex.lean`) and
proves that it is a solid-equivalence.

The indexing conventions are as in `CechPt/SolidChain.lean`: `Dchain : ChainComplex ℤ ℕ` with
`Dchain.X p = (ℤ[cechTerm p] ⟹ 𝟙) ⟹ 𝟙`, and `Dcpx` its extension to a cochain complex in
degrees `≤ 0` via `ComplexShape.embeddingDownNat`, so that `Dcpx.X (-(p:ℤ)) = Dchain.X p`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.ANALYTIC.CechPt

open Work.ATOM

/-! ## The augmentation -/

/-- The augmentation of the solid Čech complex, on the `ℕ`-graded part `Dchain`:
the transpose of the constant function `1`, followed by the canonical isomorphism
`𝟙_ LightCondAb ≅ ℤ[∗]`. -/
noncomputable def augZ : dd (zf (cechTerm 0)) ⟶ zfree Work.ATOM.pt :=
  (MonoidalClosed.pre rho).app (𝟙_ LightCondAb) ≫
    (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom ≫ Work.ATOM.unitIso.hom

/-- The augmentation, with its source written as `Dchain.X 0` (the two objects are
definitionally equal, but the wrapper keeps the two sides of subsequent identities
*syntactically* comparable, which the `rw` tactic needs). -/
noncomputable def augZD : Dchain.X 0 ⟶ zfree Work.ATOM.pt := augZ

/-- **The canonical evaluation pairing, evaluated at `rho`, is the sum map.** -/
theorem doubleDualUnit_augZ :
    doubleDualUnit (zf (cechTerm 0)) ≫ augZ = zmap (toPt (cechTerm 0)) := by
  have hcur : MonoidalClosed.curry ((ρ_ (zf (cechTerm 0))).hom ≫
      ((ρ_ (zf (cechTerm 0))).inv ≫ MonoidalClosed.uncurry rho)) = rho := by
    rw [Iso.hom_inv_id_assoc, MonoidalClosed.curry_uncurry]
  have h1 := doubleDualUnit_coord (zf (cechTerm 0))
    ((ρ_ (zf (cechTerm 0))).inv ≫ MonoidalClosed.uncurry rho)
  rw [coordMap, hcur] at h1
  have h2 : (doubleDualUnit (zf (cechTerm 0)) ≫
      ((MonoidalClosed.pre rho).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom)) =
      (ρ_ (zf (cechTerm 0))).inv ≫ MonoidalClosed.uncurry rho := h1
  calc doubleDualUnit (zf (cechTerm 0)) ≫ augZ
      = (doubleDualUnit (zf (cechTerm 0)) ≫
          ((MonoidalClosed.pre rho).app (𝟙_ LightCondAb) ≫
            (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom)) ≫ Work.ATOM.unitIso.hom := by
        rw [augZ]; simp only [Category.assoc]
    _ = ((ρ_ (zf (cechTerm 0))).inv ≫ MonoidalClosed.uncurry rho) ≫
          Work.ATOM.unitIso.hom := by rw [h2]
    _ = zmap (toPt (cechTerm 0)) := by
        rw [rho, MonoidalClosed.uncurry_curry]
        simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
          Category.id_comp]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ## The augmentation is a morphism of complexes -/

/-- The alternating sum of the Čech face maps kills the augmentation: `dR 0 ≫ sum = 0`,
because both faces `cechFace 0 i` (`i : Fin 2`) are sent to the terminal map `cechTerm 1 ⟶ ∗`. -/
theorem dR_zero_comp_aug :
    dR 0 ≫ (zmap (toPt (cechTerm 0)) ≫ Work.ATOM.unitIso.inv) = 0 := by
  have hface : ∀ i : Fin 2, cechFace 0 i ≫ toPt (cechTerm 0) = toPt (cechTerm 1) :=
    fun i => LightProfinite.isTerminalPUnit.hom_ext _ _
  have h1 : ∀ i : Fin 2, zmap (cechFace 0 i) ≫
      (zmap (toPt (cechTerm 0)) ≫ Work.ATOM.unitIso.inv) =
      zmap (toPt (cechTerm 1)) ≫ Work.ATOM.unitIso.inv := by
    intro i
    rw [← Category.assoc, ← Functor.map_comp, hface i]
  rw [dR, Preadditive.sum_comp, Fin.sum_univ_two]
  simp only [Preadditive.zsmul_comp, Preadditive.add_comp, Preadditive.neg_comp,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul, h1]
  simp

/-- The transpose of `dR 0` squares to zero with the augmentation of the dual complex:
`rho ≫ dE 0 = 0`. -/
theorem rho_comp_dE : rho ≫ dE 0 = 0 := by
  have h0 : (dR 0) ▷ (𝟙_ LightCondAb) ≫
      ((ρ_ (zf (cechTerm 0))).hom ≫ zmap (toPt (cechTerm 0)) ≫ Work.ATOM.unitIso.inv) = 0 := by
    rw [← Category.assoc, MonoidalCategory.rightUnitor_naturality, Category.assoc,
      dR_zero_comp_aug, comp_zero]
  rw [rho, dE, MonoidalClosed.curry_pre_app, h0, MonoidalClosed.curry_eq, Functor.map_zero,
    comp_zero]

/-! ## The augmentation in the `ℕ`-graded world

The augmentation `Dchain ⟶ ℤ[∗]` of the *solid* Čech complex is a morphism of complexes
(`Dchain_d_one_zero_augZ`, from `rho_comp_dE`), and the contraction of the augmented dual complex
dualises to a homotopy witnessing that it is a homotopy equivalence onto `ℤ[∗]` concentrated in
degree `0`.  Everything here is done on the `ℕ`-graded complex `Dchain`, where the index
arithmetic is well behaved, and transported to `Dcpx` (degrees `≤ 0`) by
`ComplexShape.embeddingDownNat.extendFunctor`.
-/

section

/-- The section of the augmentation in degree `0`, obtained by dualising `t₀`. -/
noncomputable def Dsec (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb)) :
    zfree Work.ATOM.pt ⟶ dd (zf (cechTerm 0)) :=
  Work.ATOM.unitIso.inv ≫ (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).inv ≫
    (MonoidalClosed.pre t₀).app (𝟙_ LightCondAb)

/-- The homotopy component in degree `m`, obtained by dualising `t m`. -/
noncomputable def Hs (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q))) (m : ℕ) :
    Dchain.X m ⟶ Dchain.X (m + 1) :=
  (MonoidalClosed.pre (t m)).app (𝟙_ LightCondAb)

/-- The matrix of the homotopy on the `ℕ`-graded complex. -/
noncomputable def Hchain (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q)))
    (i j : ℕ) : Dchain.X i ⟶ Dchain.X j :=
  if h : i + 1 = j then h ▸ (-(Hs t i)) else 0

lemma Hchain_succ (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q))) (i : ℕ) :
    Hchain t i (i + 1) = -(Hs t i) := by
  rw [Hchain, dite_eq_left rfl]

lemma Hchain_zero (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q)))
    (i j : ℕ) (h : ¬ i + 1 = j) : Hchain t i j = 0 := by
  rw [Hchain, dite_eq_right h]

/-- `Dchain.d (p+1) p` is the transpose of the dual Čech differential. -/
lemma Dchain_d_succ (p : ℕ) :
    Dchain.d (p+1) p = (MonoidalClosed.pre (dE p)).app (𝟙_ LightCondAb) :=
  ChainComplex.of_d (fun p : ℕ => dd (zf (cechTerm p))) (fun p => ddFMap (dR p)) p

/-- `Dchain.d 1 0 = ddFMap (dR 0)`. -/
lemma Dchain_d_one_zero : Dchain.d 1 0 = ddFMap (dR 0) := by
  have := ChainComplex.of_d (fun p : ℕ => dd (zf (cechTerm p))) (fun p => ddFMap (dR p)) 0
  simpa [Dchain] using this

/-- `Dchain.d 1 0 ≫ augZ = 0`: the transpose of `rho` squares to zero with the differential. -/
theorem Dchain_d_one_zero_augZ : Dchain.d 1 0 ≫ augZ = 0 := by
  rw [Dchain_d_one_zero]
  change (MonoidalClosed.pre (dE 0)).app (𝟙_ LightCondAb) ≫ augZ = 0
  rw [augZ, ← Category.assoc]
  rw [show (MonoidalClosed.pre (dE 0)).app (𝟙_ LightCondAb) ≫
      (MonoidalClosed.pre rho).app (𝟙_ LightCondAb) =
      (MonoidalClosed.pre (rho ≫ dE 0)).app (𝟙_ LightCondAb) from by
    rw [← CategoryTheory.NatTrans.comp_app, ← MonoidalClosed.pre_map rho (dE 0)]]
  rw [rho_comp_dE]
  simp only [pre_zero, CategoryTheory.NatTrans.app_zero, zero_comp]

end

/-- The augmentation, as a morphism of `ℕ`-graded chain complexes. -/
noncomputable def Ka : Dchain ⟶ ChainComplex.single₀ LightCondAb |>.obj (zfree Work.ATOM.pt) :=
  HomologicalComplex.mkHomToSingle augZ (by
    intro i hi
    rw [ComplexShape.down_Rel] at hi
    subst hi
    exact Dchain_d_one_zero_augZ)

/-- The section of the augmentation, as a morphism of `ℕ`-graded chain complexes. -/
noncomputable def Ks (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb)) :
    (ChainComplex.single₀ LightCondAb).obj (zfree Work.ATOM.pt) ⟶ Dchain :=
  HomologicalComplex.mkHomFromSingle (Dsec t₀) (by
    intro k hk
    rw [ComplexShape.down_Rel] at hk
    omega)

section

variable (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb))
  (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q)))
  (ht0 : rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb))
  (ht1 : dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0))))
  (ht2 : ∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r = 𝟙 (sd (zf (cechTerm (r+1)))))

lemma pre_add_app {A B : LightCondAb} (f g : B ⟶ A) (X : LightCondAb) :
    (MonoidalClosed.pre (f + g)).app X =
      (MonoidalClosed.pre f).app X + (MonoidalClosed.pre g).app X := by
  rw [pre_add, CategoryTheory.NatTrans.app_add]

lemma pre_comp_app (m : ℕ) :
    (MonoidalClosed.pre (dE m ≫ t m)).app (𝟙_ LightCondAb) =
      (MonoidalClosed.pre (t m)).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.pre (dE m)).app (𝟙_ LightCondAb) := by
  rw [MonoidalClosed.pre_map (dE m) (t m), CategoryTheory.NatTrans.comp_app]

lemma pre_comp_app_tdE (m : ℕ) :
    (MonoidalClosed.pre (t m ≫ dE m)).app (𝟙_ LightCondAb) =
      (MonoidalClosed.pre (dE m)).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.pre (t m)).app (𝟙_ LightCondAb) := by
  rw [MonoidalClosed.pre_map (t m) (dE m), CategoryTheory.NatTrans.comp_app]

lemma pre_comp_app_t₀ :
    (MonoidalClosed.pre (t₀ ≫ rho)).app (𝟙_ LightCondAb) =
      (MonoidalClosed.pre rho).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.pre t₀).app (𝟙_ LightCondAb) := by
  rw [MonoidalClosed.pre_map t₀ rho, CategoryTheory.NatTrans.comp_app]

lemma pre_rho_comp_pre_t₀ :
    (MonoidalClosed.pre rho).app (𝟙_ LightCondAb) ≫
      (MonoidalClosed.pre t₀).app (𝟙_ LightCondAb) = augZ ≫ Dsec t₀ := by
  rw [augZ, Dsec]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

lemma augZ_comp_Dsec (ht0 : rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb)) :
    Dsec t₀ ≫ augZ = 𝟙 (zfree Work.ATOM.pt) := by
  have hCD : (MonoidalClosed.pre t₀).app (𝟙_ LightCondAb) ≫
      (MonoidalClosed.pre rho).app (𝟙_ LightCondAb) =
      𝟙 ((CategoryTheory.ihom (𝟙_ LightCondAb)).obj (𝟙_ LightCondAb)) := by
    rw [← CategoryTheory.NatTrans.comp_app, ← MonoidalClosed.pre_map rho t₀, ht0,
      MonoidalClosed.pre_id, CategoryTheory.NatTrans.id_app]
  rw [Dsec, augZ]
  simp only [Category.assoc]
  rw [← CategoryTheory.Category.assoc
    (f := (MonoidalClosed.pre t₀).app (𝟙_ LightCondAb))
    (g := (MonoidalClosed.pre rho).app (𝟙_ LightCondAb))
    (h := (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom ≫ Work.ATOM.unitIso.hom)]
  rw [hCD, Category.id_comp]
  rw [show (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).inv ≫
      ((MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom ≫ Work.ATOM.unitIso.hom) =
      Work.ATOM.unitIso.hom from Iso.inv_hom_id_assoc _ _]
  exact Iso.inv_hom_id _

lemma Hs_zero_id (ht1 : dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0)))) :
    Hs t 0 ≫ Dchain.d 1 0 + (augZ ≫ Dsec t₀ : Dchain.X 0 ⟶ Dchain.X 0) =
    𝟙 (Dchain.X 0) := by
  have h1 : (MonoidalClosed.pre (dE 0 ≫ t 0)).app (𝟙_ LightCondAb) +
      (MonoidalClosed.pre (t₀ ≫ rho)).app (𝟙_ LightCondAb) =
      𝟙 (dd (zf (cechTerm 0))) := by
    have hs := pre_add_app (dE 0 ≫ t 0) (t₀ ≫ rho) (𝟙_ LightCondAb)
    rw [ht1, MonoidalClosed.pre_id, CategoryTheory.NatTrans.id_app] at hs
    exact hs.symm
  rw [pre_comp_app (m := 0), pre_comp_app_t₀, pre_rho_comp_pre_t₀] at h1
  rw [show Hs t 0 = (MonoidalClosed.pre (t 0)).app (𝟙_ LightCondAb) from rfl,
    show Dchain.d 1 0 = (MonoidalClosed.pre (dE 0)).app (𝟙_ LightCondAb) from
      Dchain_d_one_zero.trans rfl]
  exact h1

lemma Hs_succ_id (ht2 : ∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r =
    𝟙 (sd (zf (cechTerm (r+1))))) (m : ℕ) :
    Dchain.d (m+1) m ≫ Hs t m + Hs t (m+1) ≫ Dchain.d ((m+1)+1) (m+1) =
      𝟙 (Dchain.X (m+1)) := by
  have h1 : (MonoidalClosed.pre (dE (m+1) ≫ t (m+1))).app (𝟙_ LightCondAb) +
      (MonoidalClosed.pre (t m ≫ dE m)).app (𝟙_ LightCondAb) =
      𝟙 (dd (zf (cechTerm (m+1)))) := by
    have hs := pre_add_app (dE (m+1) ≫ t (m+1)) (t m ≫ dE m) (𝟙_ LightCondAb)
    rw [ht2 m, MonoidalClosed.pre_id, CategoryTheory.NatTrans.id_app] at hs
    exact hs.symm
  rw [pre_comp_app (m := m+1), pre_comp_app_tdE (m := m)] at h1
  rw [← Dchain_d_succ (m+1), ← Dchain_d_succ m,
    ← show Hs t (m+1) = (MonoidalClosed.pre (t (m+1))).app (𝟙_ LightCondAb) from rfl,
    ← show Hs t m = (MonoidalClosed.pre (t m)).app (𝟙_ LightCondAb) from rfl] at h1
  rw [add_comm (Dchain.d (m+1) m ≫ Hs t m)
    (Hs t (m+1) ≫ Dchain.d ((m+1)+1) (m+1))]
  exact h1

set_option backward.isDefEq.respectTransparency false in
lemma Ka_f_zero : Ka.f 0 = augZ ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (zfree Work.ATOM.pt)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- `Ka.f 0`, with the source of `augZ` written as `Dchain.X 0`. -/
lemma Ka_f_zero_D :
    Ka.f 0 = augZD ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (zfree Work.ATOM.pt)).inv := by
  rw [Ka_f_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma Ks_f_zero : (Ks t₀).f 0 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (zfree Work.ATOM.pt)).hom ≫
      Dsec t₀ :=
  HomologicalComplex.mkHomFromSingle_f _ _

lemma Ka_f_succ (i : ℕ) : Ka.f (i+1) = 0 := by
  simp only [Ka, HomologicalComplex.mkHomToSingle]
  exact dite_eq_right (by omega)

set_option backward.isDefEq.respectTransparency false in
lemma Ka_comp_Ks_zero : (Ka ≫ Ks t₀).f 0 = augZ ≫ Dsec t₀ := by
  rw [HomologicalComplex.comp_f, Ka_f_zero, Ks_f_zero]
  rw [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma Ka_comp_Ks_succ (i : ℕ) : (Ka ≫ Ks t₀).f (i+1) = 0 := by
  rw [HomologicalComplex.comp_f, Ka_f_succ, zero_comp]

/-- The homotopy witnessing that `Ka` is a homotopy equivalence onto `ℤ[∗]`.
The remaining goal is the `i+1` case of the homotopy condition: after
`Homotopy.dNext_succ_chainComplex`, `Homotopy.prevD_chainComplex`, `Hchain_succ`,
`Ka_comp_Ks_succ`, `HomologicalComplex.id_f`, `Preadditive.neg_comp` (twice) and
`Homology`-free rewriting it reduces to `Hs_succ_id`. -/
noncomputable def homotopy_Ka_Ks (ht0 : rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb))
    (ht1 : dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0))))
    (ht2 : ∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r = 𝟙 (sd (zf (cechTerm (r+1))))) :
    Homotopy (Ka ≫ Ks t₀) (𝟙 Dchain) where
  hom := Hchain t
  zero i j h := Hchain_zero t i j h
  comm i := by
    rcases i with _ | i
    · rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, Hchain_succ,
        Ka_comp_Ks_zero, HomologicalComplex.id_f]
      rw [zero_add, Preadditive.neg_comp, ← Hs_zero_id t₀ t ht1, neg_add_cancel_left]
      rfl
    · have hd : dNext (i+1) (Hchain t) = -(Dchain.d (i+1) i ≫ Hs t i) := by
        rw [Homotopy.dNext_succ_chainComplex, Hchain_succ, Preadditive.comp_neg]
      have hp : prevD (i+1) (Hchain t) =
          -(Hs t (i+1) ≫ Dchain.d ((i+1)+1) (i+1)) := by
        rw [Homotopy.prevD_chainComplex, Hchain_succ, Preadditive.neg_comp]
      have key : Dchain.d (i+1) i ≫ Hs t i + Hs t (i+1) ≫ Dchain.d ((i+1)+1) (i+1) =
          𝟙 (Dchain.X (i+1)) := by
        exact Hs_succ_id t ht2 i
      rw [hd, hp, Ka_comp_Ks_succ, HomologicalComplex.id_f, ← neg_add, key, neg_add_cancel]

end

end Work.ANALYTIC.CechPt
