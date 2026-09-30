import Mathlib
import Submission.Work.Serre.mvDeltaAuxDefs
import Submission.Work.Serre.MVGlue.mvSetup
import Submission.Work.Serre.mvLadder
import Submission.Work.Serre.MVShift.shKHomologyIsoNatural
import Submission.Work.Serre.MVShift.shS_delta_comm
import Submission.Work.Serre.MVShift.shKZeroRat
import Submission.Work.Serre.MVGlue.homotopyInverseMV

/-!
# The `δ`-square of the rational Mayer–Vietoris sequence: assembly

This file assembles the `(DELTA)` square `Work.Serre.mvDeltaCupMixedAux` from

* the honest cup morphism `cupSES : Smv X ∅ U V ⟶ shS (Smv X A U V) n₀` (built from the
  chain-level naturality identities, taken as hypotheses here — they are
  `Work.Serre.mvDeltaAuxCupNat`),
* the identification of its homology maps with the mixed cup product (taken as a hypothesis —
  `Work.Serre.mvDeltaAuxCupHom`),
* the strict homotopy inverse `η` of the comparison `zetaSmv` (`Work.Serre.MVGlue.homotopyInverseMV`),
* the degree-`n₀` naturality of the connecting map (`MVShift.shS_delta_naturality`) together with the
  compatibility of `δ` with the shift (`MVShift.shS_delta_comm`, `MVShift.shS_delta_comm_zero`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-! ## The cup morphism of the cover -/

/-- **The cup morphism of the cover**: cup with a relative cocycle is a morphism of short complexes
`Smv X ∅ U V ⟶ shS (Smv X A U V) n₀`.  The two squares are the chain-level naturality identities
`h1`, `h1V`, `h2`, `h2V` (statement `Work.Serre.mvDeltaAuxCupNat`). -/
noncomputable def cupSES (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0)
    (h1 : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) U)
        (cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A U) n₀))
    (h1V : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) V)
        (cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A V) n₀))
    (h2 : CategoryTheory.CategoryStruct.comp (mvGWU X (∅ : Set X) U V)
        (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopU X A U n₀ t ht)
          (MVShift.shMap (mvGWU X A U V) n₀))
    (h2V : CategoryTheory.CategoryStruct.comp (mvGWV X (∅ : Set X) U V)
        (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopV X A V n₀ t ht)
          (MVShift.shMap (mvGWV X A U V) n₀)) :
    MVGlue.Smv X (∅ : Set X) U V ⟶ MVShift.shS (MVGlue.Smv X A U V) n₀ :=
  ShortComplex.homMk (cupTop X A n₀ t ht) (cupMid X A U V n₀ t ht) (cupTopUV X A U V n₀ t ht)
    (by
      show cupTop X A n₀ t ht ≫ MVShift.shMap (Work.Serre.mvFChain X A U V) n₀
        = Work.Serre.mvFChain X (∅ : Set X) U V ≫ cupMid X A U V n₀ t ht
      unfold Work.Serre.mvFChain Work.Serre.cupMid
      rw [biprod.lift_desc]
      rw [biprod.lift_eq, shMap_add, MVShift.shMap_comp, MVShift.shMap_comp,
        Preadditive.comp_add]
      simp only [← Category.assoc]
      rw [h1, h1V])
    (by
      show cupMid X A U V n₀ t ht ≫ MVShift.shMap (Work.Serre.mvGChain X A U V) n₀
        = Work.Serre.mvGChain X (∅ : Set X) U V ≫ cupTopUV X A U V n₀ t ht
      unfold Work.Serre.mvGChain Work.Serre.cupMid
      apply biprod.hom_ext'
      · rw [← Category.assoc, biprod.inl_desc, Category.assoc, ← MVShift.shMap_comp,
          biprod.inl_desc]
        rw [← Category.assoc, biprod.inl_desc]
        exact h2.symm
      · rw [← Category.assoc, biprod.inr_desc, Category.assoc, ← MVShift.shMap_comp,
          biprod.inr_desc, shMap_neg, Preadditive.comp_neg]
        rw [← Category.assoc, biprod.inr_desc, Preadditive.neg_comp]
        rw [← h2V])

/-! ## The homology identification of the cup chain maps -/

/-- The statement of `Work.Serre.mvDeltaAuxCupHom`: the homology of the cup with a relative cocycle
is the mixed cup product with the class of the cocycle. -/
abbrev CupHomStatement (Y : TopCat) (B : Set Y) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ Y B n₀)
    (ht : Work.Cohomology.relDiffLM ℚ Y B n₀ t = 0) : Prop :=
  (∀ (k : ℕ) (hk : 1 ≤ k),
      CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap (cupRelChain Y B n₀ t ht) k)
          (MVShift.shK_homologyIso (Work.Cohomology.relComplex ℚ Y B) n₀ k hk).hom
        = CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set Y) k)
            (ModuleCat.ofHom ((Work.Thom.mixedCupC ℚ B k n₀).flip
              (Work.Cohomology.relClassOf ℚ Y B t ht))))
    ∧ (CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap (cupRelChain Y B n₀ t ht) 0)
          (MVShift.shK_homologyZero (Work.Cohomology.relComplex ℚ Y B) n₀)
        = CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set Y) 0)
            (ModuleCat.ofHom ((Work.Thom.mixedCupC ℚ B 0 n₀).flip
              (Work.Cohomology.relClassOf ℚ Y B t ht))))

/-! ## The restriction of a class to the overlap -/

/-- The restriction of a relative cocycle on `(X,A)` to `(U,A∩U)`, on classes. -/
theorem restrU_relClassOf (X : TopCat) (A U : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀) (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    (mvRestrU X A U n₀).hom (Work.Cohomology.relClassOf ℚ X A t ht)
      = Work.Cohomology.relClassOf ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U)
          (cupTgtU X A U n₀ t) (cupTgtU_cocycle X A U n₀ t ht) :=
  Work.Cohomology.homologyMap_relComplexMap_relClassOf (R := ℚ) (X₁ := TopCat.of ↥U) (X₂ := X)
    (A₁ := Work.Cohomology.interAU A U) (A₂ := A)
    (f := Work.Cohomology.subtypeIncl X U)
    (h := Work.Cohomology.interAU_incl_subtypeIncl X A U) (a := t) (ha := ht)

/-- The further restriction to `(U∩V, A∩U∩V)`, on classes. -/
theorem restrUVU_relClassOf (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) n₀)
    (ht : Work.Cohomology.relDiffLM ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) n₀ t = 0) :
    (mvRestrUVU X A U V n₀).hom
        (Work.Cohomology.relClassOf ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) t ht)
      = Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
          (Work.Cohomology.interAU A (U ∩ V))
          (Work.Cohomology.relMapLM (R := ℚ) (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥U)
            (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U)
            (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)
            (Work.Cohomology.interAU_incl_pdIncl_U X A U V) n₀ t)
          (Work.Cohomology.relDiffLM_relMapLM (R := ℚ) (X₁ := TopCat.of ↥(U ∩ V))
            (X₂ := TopCat.of ↥U) (A₁ := Work.Cohomology.interAU A (U ∩ V))
            (A₂ := Work.Cohomology.interAU A U)
            (f := Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)
            (h := Work.Cohomology.interAU_incl_pdIncl_U X A U V) (n := n₀) t ht) :=
  Work.Cohomology.homologyMap_relComplexMap_relClassOf (R := ℚ) (X₁ := TopCat.of ↥(U ∩ V))
    (X₂ := TopCat.of ↥U) (A₁ := Work.Cohomology.interAU A (U ∩ V))
    (A₂ := Work.Cohomology.interAU A U)
    (f := Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)
    (h := Work.Cohomology.interAU_incl_pdIncl_U X A U V) (a := t) (ha := ht)

/-- The overlap restriction of the class of a cocycle is the class of the restricted cocycle. -/
theorem ovlClass_relClassOf (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀) (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    U₀ovl X A U V n₀ (Work.Cohomology.relClassOf ℚ X A t ht)
      = Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V))
          (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht) := by
  rw [U₀ovl, restrU_relClassOf X A U n₀ t ht]
  exact restrUVU_relClassOf X A U V n₀ (cupTgtU X A U n₀ t) (cupTgtU_cocycle X A U n₀ t ht)

/-! ## Two bookkeeping lemmas -/

/-- The `eqToHom` of an index equality is compatible with the comparison isomorphisms `eTop`. -/
theorem eTop_inv_eqToHom_hom (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {j k : ℕ} (h : j = k) :
    CategoryTheory.CategoryStruct.comp (eTop X A U V hU hV hcov j).inv
        (CategoryTheory.CategoryStruct.comp
          (CategoryTheory.eqToHom (congrArg (fun i => Work.Thom.RelCoh ℚ i X A) h))
          (eTop X A U V hU hV hcov k).hom)
      = CategoryTheory.eqToHom
          (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) h) := by
  subst h
  simp only [Category.assoc, CategoryTheory.eqToHom_refl, Category.id_comp,
    Category.comp_id, Iso.inv_hom_id]

/-- The first component of `η` is the inverse of `eTop` on homology. -/
theorem eta_tau1_homology (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ)
    (η : Work.Serre.dqShort X (∅ : Set X) U V ⟶ MVGlue.Smv X (∅ : Set X) U V)
    (hη : ∀ k : ℕ,
      CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap η.τ₁ k)
          (HomologicalComplex.homologyMap (MVGlue.zetaSmv X (∅ : Set X) U V).τ₁ k)
        = CategoryTheory.CategoryStruct.id
            ((Work.Serre.dqShort X (∅ : Set X) U V).X₁.homology k)
      ∧ CategoryTheory.CategoryStruct.comp
            (HomologicalComplex.homologyMap (MVGlue.zetaSmv X (∅ : Set X) U V).τ₁ k)
            (HomologicalComplex.homologyMap η.τ₁ k)
          = CategoryTheory.CategoryStruct.id
              ((MVGlue.Smv X (∅ : Set X) U V).X₁.homology k))
    (k : ℕ) :
    HomologicalComplex.homologyMap η.τ₁ k = (eTop X (∅ : Set X) U V hU hV hcov k).inv := by
  haveI : IsIso (HomologicalComplex.homologyMap (zetaTop X (∅ : Set X) U V) k) :=
    isIso_homologyMap_zetaTop X (∅ : Set X) U V hU hV hcov k
  have h := (hη k).2
  rw [show (HomologicalComplex.homologyMap (MVGlue.zetaSmv X (∅ : Set X) U V).τ₁ k)
      = (eTop X (∅ : Set X) U V hU hV hcov k).hom from rfl] at h
  exact IsIso.eq_inv_of_hom_inv_id h

/-- The third component of `η` is the inverse of `eW` on homology. -/
theorem eta_tau3_homology (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ)
    (η : Work.Serre.dqShort X (∅ : Set X) U V ⟶ MVGlue.Smv X (∅ : Set X) U V)
    (hη : ∀ k : ℕ,
      CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap η.τ₃ k)
          (HomologicalComplex.homologyMap (MVGlue.zetaSmv X (∅ : Set X) U V).τ₃ k)
        = CategoryTheory.CategoryStruct.id
            ((Work.Serre.dqShort X (∅ : Set X) U V).X₃.homology k)
      ∧ CategoryTheory.CategoryStruct.comp
            (HomologicalComplex.homologyMap (MVGlue.zetaSmv X (∅ : Set X) U V).τ₃ k)
            (HomologicalComplex.homologyMap η.τ₃ k)
          = CategoryTheory.CategoryStruct.id
              ((MVGlue.Smv X (∅ : Set X) U V).X₃.homology k))
    (k : ℕ) :
    HomologicalComplex.homologyMap η.τ₃ k = (eW X (∅ : Set X) U V k).inv := by
  haveI : IsIso (HomologicalComplex.homologyMap (zetaW X (∅ : Set X) U V) k) :=
    isIso_homologyMap_zetaW X (∅ : Set X) U V k
  have h := (hη k).2
  rw [show (HomologicalComplex.homologyMap (MVGlue.zetaSmv X (∅ : Set X) U V).τ₃ k)
      = (eW X (∅ : Set X) U V k).hom from rfl] at h
  exact IsIso.eq_inv_of_hom_inv_id h

/-- The degree-`n` shift of a morphism of short complexes. -/
noncomputable def shSMap {S T : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ)} (f : S ⟶ T) (n : ℕ) :
    MVShift.shS S n ⟶ MVShift.shS T n :=
  ShortComplex.homMk (MVShift.shMap f.τ₁ n) (MVShift.shMap f.τ₂ n) (MVShift.shMap f.τ₃ n)
    (by
      show CategoryTheory.CategoryStruct.comp (MVShift.shMap f.τ₁ n) (MVShift.shMap T.f n)
        = CategoryTheory.CategoryStruct.comp (MVShift.shMap S.f n) (MVShift.shMap f.τ₂ n)
      rw [← MVShift.shMap_comp, f.comm₁₂, MVShift.shMap_comp])
    (by
      show CategoryTheory.CategoryStruct.comp (MVShift.shMap f.τ₂ n) (MVShift.shMap T.g n)
        = CategoryTheory.CategoryStruct.comp (MVShift.shMap S.g n) (MVShift.shMap f.τ₃ n)
      rw [← MVShift.shMap_comp, f.comm₂₃, MVShift.shMap_comp])

@[simp] theorem shSMap_τ₁ {S T : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ)} (f : S ⟶ T) (n : ℕ) :
    (shSMap f n).τ₁ = MVShift.shMap f.τ₁ n := rfl

@[simp] theorem shSMap_τ₂ {S T : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ)} (f : S ⟶ T) (n : ℕ) :
    (shSMap f n).τ₂ = MVShift.shMap f.τ₂ n := rfl

@[simp] theorem shSMap_τ₃ {S T : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ)} (f : S ⟶ T) (n : ℕ) :
    (shSMap f n).τ₃ = MVShift.shMap f.τ₃ n := rfl

/-! ## The homology of the cup morphism composed with the comparison -/

section Assembly

variable (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
  (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (t : Work.Cohomology.relKern ℚ X A n₀)
  (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0)

/-- The first component of the assembled morphism, in the interior degrees. -/
theorem phi_tau1_apply
    (h1 : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) U) (cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A U) n₀))
    (h1V : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) V) (cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A V) n₀))
    (h2 : CategoryTheory.CategoryStruct.comp (mvGWU X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopU X A U n₀ t ht)
          (MVShift.shMap (mvGWU X A U V) n₀))
    (h2V : CategoryTheory.CategoryStruct.comp (mvGWV X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopV X A V n₀ t ht)
          (MVShift.shMap (mvGWV X A U V) n₀))
    (η : Work.Serre.dqShort X (∅ : Set X) U V ⟶ MVGlue.Smv X (∅ : Set X) U V)
    (hη1 : ∀ k : ℕ,
      HomologicalComplex.homologyMap η.τ₁ k = (eTop X (∅ : Set X) U V hU hV hcov k).inv)
    (hHomX : CupHomStatement X A n₀ t ht) (k : ℕ) (hk : 1 ≤ k) :
    HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₁) k
      ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ k hk).hom
      = CategoryTheory.CategoryStruct.comp (eTop X (∅ : Set X) U V hU hV hcov k).inv
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set X) k)
              (ModuleCat.ofHom (MVGlue.cupWith X A k n₀
                (Work.Cohomology.relClassOf ℚ X A t ht))))
            (eTop X A U V hU hV hcov (k + n₀)).hom) := by
  have hsplit : HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₁) k
      = HomologicalComplex.homologyMap η.τ₁ k
        ≫ (HomologicalComplex.homologyMap (cupRelChain X A n₀ t ht) k
          ≫ HomologicalComplex.homologyMap
              (MVShift.shMap (MVGlue.zetaSmv X A U V).τ₁ n₀) k) := by
    rw [ShortComplex.comp_τ₁, ShortComplex.comp_τ₁, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp]
    rfl
  have hnat := MVShift.shKHomologyIsoNatural (MVGlue.zetaSmv X A U V).τ₁ n₀ k hk
  have hcup : HomologicalComplex.homologyMap (cupRelChain X A n₀ t ht) k
        ≫ (MVShift.shK_homologyIso (MVGlue.Smv X A U V).X₁ n₀ k hk).hom
      = Work.Thom.relToAbs ℚ (∅ : Set X) k
        ≫ ModuleCat.ofHom (MVGlue.cupWith X A k n₀ (Work.Cohomology.relClassOf ℚ X A t ht)) :=
    hHomX.1 k hk
  have heta : HomologicalComplex.homologyMap η.τ₁ k
      = (eTop X (∅ : Set X) U V hU hV hcov k).inv := hη1 k
  calc HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₁) k
        ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ k hk).hom
      = HomologicalComplex.homologyMap η.τ₁ k
        ≫ (HomologicalComplex.homologyMap (cupRelChain X A n₀ t ht) k
          ≫ (HomologicalComplex.homologyMap
                (MVShift.shMap (MVGlue.zetaSmv X A U V).τ₁ n₀) k
            ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ k hk).hom)) := by
        rw [hsplit]; simp only [Category.assoc]
    _ = HomologicalComplex.homologyMap η.τ₁ k
        ≫ (HomologicalComplex.homologyMap (cupRelChain X A n₀ t ht) k
          ≫ ((MVShift.shK_homologyIso (MVGlue.Smv X A U V).X₁ n₀ k hk).hom
            ≫ HomologicalComplex.homologyMap (MVGlue.zetaSmv X A U V).τ₁ (k + n₀))) := by
        simp only [Category.assoc, hnat]
    _ = HomologicalComplex.homologyMap η.τ₁ k
        ≫ ((HomologicalComplex.homologyMap (cupRelChain X A n₀ t ht) k
            ≫ (MVShift.shK_homologyIso (MVGlue.Smv X A U V).X₁ n₀ k hk).hom)
          ≫ HomologicalComplex.homologyMap (MVGlue.zetaSmv X A U V).τ₁ (k + n₀)) := by
        simp only [Category.assoc]
    _ = HomologicalComplex.homologyMap η.τ₁ k
        ≫ ((Work.Thom.relToAbs ℚ (∅ : Set X) k
            ≫ ModuleCat.ofHom (MVGlue.cupWith X A k n₀
              (Work.Cohomology.relClassOf ℚ X A t ht)))
          ≫ (eTop X A U V hU hV hcov (k + n₀)).hom) := by
        simp only [Category.assoc, hcup]
        rw [show HomologicalComplex.homologyMap (MVGlue.zetaSmv X A U V).τ₁ (k + n₀)
            = (eTop X A U V hU hV hcov (k + n₀)).hom from rfl]
    _ = (eTop X (∅ : Set X) U V hU hV hcov k).inv
        ≫ ((Work.Thom.relToAbs ℚ (∅ : Set X) k
            ≫ ModuleCat.ofHom (MVGlue.cupWith X A k n₀
              (Work.Cohomology.relClassOf ℚ X A t ht)))
          ≫ (eTop X A U V hU hV hcov (k + n₀)).hom) := by
        rw [heta]

/-- The third component of the assembled morphism, in the interior degrees. -/
theorem phi_tau3_apply
    (h1 : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) U) (cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A U) n₀))
    (h1V : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) V) (cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A V) n₀))
    (h2 : CategoryTheory.CategoryStruct.comp (mvGWU X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopU X A U n₀ t ht)
          (MVShift.shMap (mvGWU X A U V) n₀))
    (h2V : CategoryTheory.CategoryStruct.comp (mvGWV X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopV X A V n₀ t ht)
          (MVShift.shMap (mvGWV X A U V) n₀))
    (η : Work.Serre.dqShort X (∅ : Set X) U V ⟶ MVGlue.Smv X (∅ : Set X) U V)
    (hη3 : ∀ k : ℕ,
      HomologicalComplex.homologyMap η.τ₃ k = (eW X (∅ : Set X) U V k).inv)
    (hHomUV : CupHomStatement (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
      (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht))
    (k : ℕ) (hk : 1 ≤ k) :
    HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃) k
      ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₃ n₀ k hk).hom
      = CategoryTheory.CategoryStruct.comp (eW X (∅ : Set X) U V k).inv
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp
              (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) k)
              (ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
                k n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
                  (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
                  (cupTgtUV_cocycle X A U V n₀ t ht)))))
            (eW X A U V (k + n₀)).hom) := by
  have hsplit : HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃) k
      = HomologicalComplex.homologyMap η.τ₃ k
        ≫ (HomologicalComplex.homologyMap
              (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
                (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) k
          ≫ HomologicalComplex.homologyMap
              (MVShift.shMap (MVGlue.zetaSmv X A U V).τ₃ n₀) k) := by
    rw [ShortComplex.comp_τ₃, ShortComplex.comp_τ₃, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp]
    rfl
  have hnat := MVShift.shKHomologyIsoNatural (MVGlue.zetaSmv X A U V).τ₃ n₀ k hk
  have hcup : HomologicalComplex.homologyMap
          (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
            (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) k
        ≫ (MVShift.shK_homologyIso (MVGlue.Smv X A U V).X₃ n₀ k hk).hom
      = Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) k
        ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
            k n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
              (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
              (cupTgtUV_cocycle X A U V n₀ t ht))) :=
    hHomUV.1 k hk
  have heta : HomologicalComplex.homologyMap η.τ₃ k = (eW X (∅ : Set X) U V k).inv := hη3 k
  calc HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃) k
        ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₃ n₀ k hk).hom
      = HomologicalComplex.homologyMap η.τ₃ k
        ≫ (HomologicalComplex.homologyMap
              (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
                (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) k
          ≫ (HomologicalComplex.homologyMap
                (MVShift.shMap (MVGlue.zetaSmv X A U V).τ₃ n₀) k
            ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₃ n₀ k hk).hom)) := by
        rw [hsplit]; simp only [Category.assoc]
    _ = HomologicalComplex.homologyMap η.τ₃ k
        ≫ (HomologicalComplex.homologyMap
              (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
                (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) k
          ≫ ((MVShift.shK_homologyIso (MVGlue.Smv X A U V).X₃ n₀ k hk).hom
            ≫ HomologicalComplex.homologyMap (MVGlue.zetaSmv X A U V).τ₃ (k + n₀))) := by
        simp only [Category.assoc, hnat]
    _ = HomologicalComplex.homologyMap η.τ₃ k
        ≫ ((HomologicalComplex.homologyMap
              (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
                (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) k
            ≫ (MVShift.shK_homologyIso (MVGlue.Smv X A U V).X₃ n₀ k hk).hom)
          ≫ (eW X A U V (k + n₀)).hom) := by
        simp only [Category.assoc]
        rw [show HomologicalComplex.homologyMap (MVGlue.zetaSmv X A U V).τ₃ (k + n₀)
            = (eW X A U V (k + n₀)).hom from rfl]
    _ = HomologicalComplex.homologyMap η.τ₃ k
        ≫ ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) k
            ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
                k n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
                  (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
                  (cupTgtUV_cocycle X A U V n₀ t ht))))
          ≫ (eW X A U V (k + n₀)).hom) := by
        simp only [Category.assoc, hcup]
    _ = (eW X (∅ : Set X) U V k).inv
        ≫ ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) k
            ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
                k n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
                  (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
                  (cupTgtUV_cocycle X A U V n₀ t ht))))
          ≫ (eW X A U V (k + n₀)).hom) := by
        rw [heta]

/-- The third component of the assembled morphism, in degree zero. -/
theorem phi_tau3_apply_zero
    (h1 : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) U) (cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A U) n₀))
    (h1V : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) V) (cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A V) n₀))
    (h2 : CategoryTheory.CategoryStruct.comp (mvGWU X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopU X A U n₀ t ht)
          (MVShift.shMap (mvGWU X A U V) n₀))
    (h2V : CategoryTheory.CategoryStruct.comp (mvGWV X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopV X A V n₀ t ht)
          (MVShift.shMap (mvGWV X A U V) n₀))
    (η : Work.Serre.dqShort X (∅ : Set X) U V ⟶ MVGlue.Smv X (∅ : Set X) U V)
    (hη3 : ∀ k : ℕ,
      HomologicalComplex.homologyMap η.τ₃ k = (eW X (∅ : Set X) U V k).inv)
    (hHomUV : CupHomStatement (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
      (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) :
    HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃) 0
      ≫ MVShift.shK_homologyZero (Work.Serre.dqShort X A U V).X₃ n₀
      = CategoryTheory.CategoryStruct.comp (eW X (∅ : Set X) U V 0).inv
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp
              (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0)
              (ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
                0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
                  (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
                  (cupTgtUV_cocycle X A U V n₀ t ht)))))
            (eW X A U V (0 + n₀)).hom) := by
  have hsplit : HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃) 0
      = HomologicalComplex.homologyMap η.τ₃ 0
        ≫ (HomologicalComplex.homologyMap
              (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
                (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) 0
          ≫ HomologicalComplex.homologyMap
              (MVShift.shMap (MVGlue.zetaSmv X A U V).τ₃ n₀) 0) := by
    rw [ShortComplex.comp_τ₃, ShortComplex.comp_τ₃, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp]
    rfl
  have hnat := MVShift.shK_homologyZero_natural (MVGlue.zetaSmv X A U V).τ₃ n₀
  have hcup : HomologicalComplex.homologyMap
          (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
            (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) 0
        ≫ MVShift.shK_homologyZero (MVGlue.Smv X A U V).X₃ n₀
      = Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0
        ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
            0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
              (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
              (cupTgtUV_cocycle X A U V n₀ t ht))) :=
    hHomUV.2
  have heta : HomologicalComplex.homologyMap η.τ₃ 0 = (eW X (∅ : Set X) U V 0).inv := hη3 0
  calc HomologicalComplex.homologyMap
        ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
          ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃) 0
        ≫ MVShift.shK_homologyZero (Work.Serre.dqShort X A U V).X₃ n₀
      = HomologicalComplex.homologyMap η.τ₃ 0
        ≫ (HomologicalComplex.homologyMap
              (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
                (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) 0
          ≫ (HomologicalComplex.homologyMap
                (MVShift.shMap (MVGlue.zetaSmv X A U V).τ₃ n₀) 0
            ≫ MVShift.shK_homologyZero (Work.Serre.dqShort X A U V).X₃ n₀)) := by
        rw [hsplit]; simp only [Category.assoc]
    _ = HomologicalComplex.homologyMap η.τ₃ 0
        ≫ (HomologicalComplex.homologyMap
              (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
                (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) 0
          ≫ (MVShift.shK_homologyZero (MVGlue.Smv X A U V).X₃ n₀
            ≫ HomologicalComplex.homologyMap (MVGlue.zetaSmv X A U V).τ₃ (0 + n₀))) := by
        simp only [Category.assoc, ← hnat]
    _ = HomologicalComplex.homologyMap η.τ₃ 0
        ≫ ((HomologicalComplex.homologyMap
              (cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
                (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) 0
            ≫ MVShift.shK_homologyZero (MVGlue.Smv X A U V).X₃ n₀)
          ≫ (eW X A U V (0 + n₀)).hom) := by
        simp only [Category.assoc]
        rw [show HomologicalComplex.homologyMap (MVGlue.zetaSmv X A U V).τ₃ (0 + n₀)
            = (eW X A U V (0 + n₀)).hom from rfl]
    _ = HomologicalComplex.homologyMap η.τ₃ 0
        ≫ ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0
            ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
                0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
                  (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
                  (cupTgtUV_cocycle X A U V n₀ t ht))))
          ≫ (eW X A U V (0 + n₀)).hom) := by
        simp only [Category.assoc, hcup]
    _ = (eW X (∅ : Set X) U V 0).inv
        ≫ ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0
            ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
                0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
                  (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
                  (cupTgtUV_cocycle X A U V n₀ t ht))))
          ≫ (eW X A U V (0 + n₀)).hom) := by
        rw [heta]

end Assembly


/-! ## The `δ`-square -/

/-! ## The `δ`-square -/

/-! ## The `δ`-square -/

/-! ## The `δ`-square -/

/-! ## The `δ`-square -/

/-! ## The `δ`-square -/

section Delta

variable (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
  (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (t : Work.Cohomology.relKern ℚ X A n₀)
  (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0)

/-- The first identification, with the `(eTop X A …)`-inverse on the right. -/
theorem phi_tau1_apply_inv
    (h1 : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) U) (cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A U) n₀))
    (h1V : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) V) (cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A V) n₀))
    (h2 : CategoryTheory.CategoryStruct.comp (mvGWU X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopU X A U n₀ t ht)
          (MVShift.shMap (mvGWU X A U V) n₀))
    (h2V : CategoryTheory.CategoryStruct.comp (mvGWV X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopV X A V n₀ t ht)
          (MVShift.shMap (mvGWV X A U V) n₀))
    (η : Work.Serre.dqShort X (∅ : Set X) U V ⟶ MVGlue.Smv X (∅ : Set X) U V)
    (hη1 : ∀ k : ℕ,
      HomologicalComplex.homologyMap η.τ₁ k = (eTop X (∅ : Set X) U V hU hV hcov k).inv)
    (hHomX : CupHomStatement X A n₀ t ht) (k : ℕ) (hk : 1 ≤ k) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap
          ((η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V
            ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₁) k)
        (CategoryTheory.CategoryStruct.comp
          (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ k hk).hom
          (eTop X A U V hU hV hcov (k + n₀)).inv)
      = CategoryTheory.CategoryStruct.comp (eTop X (∅ : Set X) U V hU hV hcov k).inv
          (CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set X) k)
            (ModuleCat.ofHom (MVGlue.cupWith X A k n₀ (Work.Cohomology.relClassOf ℚ X A t ht)))) := by
  have h := phi_tau1_apply X A U V hU hV hcov n₀ t ht h1 h1V h2 h2V η hη1 hHomX k hk
  have hh := congrArg (fun z => CategoryTheory.CategoryStruct.comp z
    (eTop X A U V hU hV hcov (k + n₀)).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

theorem deltaSquare_succ
    (h1 : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) U) (cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A U) n₀))
    (h1V : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) V) (cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A V) n₀))
    (h2 : CategoryTheory.CategoryStruct.comp (mvGWU X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopU X A U n₀ t ht)
          (MVShift.shMap (mvGWU X A U V) n₀))
    (h2V : CategoryTheory.CategoryStruct.comp (mvGWV X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopV X A V n₀ t ht)
          (MVShift.shMap (mvGWV X A U V) n₀))
    (hHomX : CupHomStatement X A n₀ t ht)
    (hHomUV : CupHomStatement (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
      (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht))
    (m : ℕ) :
    mvDelta X (∅ : Set X) U V hU hV hcov (m + 1) ≫ (Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1 + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith X A (m + 1 + 1) n₀ (Work.Cohomology.relClassOf ℚ X A t ht)))
      = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) (m + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) (m + 1) n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ (mvDelta X A U V hU hV hcov ((m + 1) + n₀) ≫ (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) (by omega : ((m + 1) + n₀) + 1 = (m + 1 + 1) + n₀)))) := by
  obtain ⟨η, hη⟩ := MVGlue.homotopyInverseMV X U V hU hV hcov
  have hη1 : ∀ k : ℕ, HomologicalComplex.homologyMap η.τ₁ k
      = (eTop X (∅ : Set X) U V hU hV hcov k).inv :=
    fun k => eta_tau1_homology X U V hU hV hcov η hη.1 k
  have hη3 : ∀ k : ℕ, HomologicalComplex.homologyMap η.τ₃ k
      = (eW X (∅ : Set X) U V k).inv :=
    fun k => eta_tau3_homology X U V hU hV hcov η hη.2 k
  have hk1 : 1 ≤ m + 1 + 1 := by omega
  have hkm : 1 ≤ m + 1 := by omega
  have hcast : ((m + 1) + n₀) + 1 = (m + 1 + 1) + n₀ := by omega
  have h0 := MVShift.shS_delta_naturality (Work.Serre.dqShort_shortExact X (∅ : Set X) U V)
      (Work.Serre.dqShort_shortExact X A U V) n₀
      (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀)
      (m + 1) (m + 1 + 1) (by rfl)
  calc mvDelta X (∅ : Set X) U V hU hV hcov (m + 1) ≫ (Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1 + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith X A (m + 1 + 1) n₀ (Work.Cohomology.relClassOf ℚ X A t ht)))

      _ = (eW X (∅ : Set X) U V (m + 1)).hom ≫ ((Work.Serre.dqShort_shortExact X (∅ : Set X) U V).δ (m + 1) (m + 1 + 1) (by rfl) ≫ ((eTop X (∅ : Set X) U V hU hV hcov (m + 1 + 1)).inv ≫ (Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1 + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith X A (m + 1 + 1) n₀ (Work.Cohomology.relClassOf ℚ X A t ht))))) := by
        rw [mvDelta]; simp only [Category.assoc]
      _ = (eW X (∅ : Set X) U V (m + 1)).hom ≫ ((Work.Serre.dqShort_shortExact X (∅ : Set X) U V).δ (m + 1) (m + 1 + 1) (by rfl) ≫ ((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₁ (m + 1 + 1)) ≫ ((MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ (m + 1 + 1) hk1).hom ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv))) := by
        rw [← phi_tau1_apply_inv X A U V hU hV hcov n₀ t ht h1 h1V h2 h2V η hη1 hHomX (m + 1 + 1) hk1]
      _ = (eW X (∅ : Set X) U V (m + 1)).hom ≫ (((Work.Serre.dqShort_shortExact X (∅ : Set X) U V).δ (m + 1) (m + 1 + 1) (by rfl) ≫ (HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₁ (m + 1 + 1))) ≫ ((MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ (m + 1 + 1) hk1).hom ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv)) := by
        simp only [Category.assoc]
      _ = (eW X (∅ : Set X) U V (m + 1)).hom ≫ (((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃ (m + 1)) ≫ (MVShift.shS_shortExact (Work.Serre.dqShort X A U V) (Work.Serre.dqShort_shortExact X A U V) n₀).δ (m + 1) (m + 1 + 1) (by rfl)) ≫ ((MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ (m + 1 + 1) hk1).hom ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv)) := by
        rw [h0]
      _ = (eW X (∅ : Set X) U V (m + 1)).hom ≫ ((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃ (m + 1)) ≫ (((MVShift.shS_shortExact (Work.Serre.dqShort X A U V) (Work.Serre.dqShort_shortExact X A U V) n₀).δ (m + 1) (m + 1 + 1) (by rfl) ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ (m + 1 + 1) hk1).hom) ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv)) := by
        simp only [Category.assoc]
      _ = (eW X (∅ : Set X) U V (m + 1)).hom ≫ ((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃ (m + 1)) ≫ (((MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₃ n₀ (m + 1) hkm).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ ((m + 1) + n₀) (((m + 1) + n₀) + 1) (by rfl) ≫ (CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast)))) ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv)) := by
        rw [MVShift.shS_delta_comm (Work.Serre.dqShort X A U V) (Work.Serre.dqShort_shortExact X A U V) n₀ (m + 1) hkm]
      _ = (eW X (∅ : Set X) U V (m + 1)).hom ≫ (((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃ (m + 1)) ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₃ n₀ (m + 1) hkm).hom) ≫ (((Work.Serre.dqShort_shortExact X A U V).δ ((m + 1) + n₀) (((m + 1) + n₀) + 1) (by rfl) ≫ (CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast))) ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv)) := by
        simp only [Category.assoc]
      _ = (eW X (∅ : Set X) U V (m + 1)).hom ≫ (((eW X (∅ : Set X) U V (m + 1)).inv ≫ ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) (m + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) (m + 1) n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ (eW X A U V ((m + 1) + n₀)).hom)) ≫ (((Work.Serre.dqShort_shortExact X A U V).δ ((m + 1) + n₀) (((m + 1) + n₀) + 1) (by rfl) ≫ (CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast))) ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv)) := by
        rw [← phi_tau3_apply X A U V n₀ t ht h1 h1V h2 h2V η hη3 hHomUV (m + 1) hkm]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) (m + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) (m + 1) n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V ((m + 1) + n₀)).hom ≫ (((Work.Serre.dqShort_shortExact X A U V).δ ((m + 1) + n₀) (((m + 1) + n₀) + 1) (by rfl) ≫ (CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast))) ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv)) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) (m + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) (m + 1) n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V ((m + 1) + n₀)).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ ((m + 1) + n₀) (((m + 1) + n₀) + 1) (by rfl) ≫ ((CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast)) ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv))) := by
        simp only [Category.assoc]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) (m + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) (m + 1) n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V ((m + 1) + n₀)).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ ((m + 1) + n₀) (((m + 1) + n₀) + 1) (by rfl) ≫ (((eTop X A U V hU hV hcov (((m + 1) + n₀) + 1)).inv ≫ ((CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) hcast)) ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).hom)) ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv))) := by
        rw [← eTop_inv_eqToHom_hom X A U V hU hV hcov hcast]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) (m + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) (m + 1) n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V ((m + 1) + n₀)).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ ((m + 1) + n₀) (((m + 1) + n₀) + 1) (by rfl) ≫ ((eTop X A U V hU hV hcov (((m + 1) + n₀) + 1)).inv ≫ ((CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) hcast)) ≫ ((eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).hom ≫ (eTop X A U V hU hV hcov (m + 1 + 1 + n₀)).inv))))) := by
        simp only [Category.assoc]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) (m + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) (m + 1) n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V ((m + 1) + n₀)).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ ((m + 1) + n₀) (((m + 1) + n₀) + 1) (by rfl) ≫ ((eTop X A U V hU hV hcov (((m + 1) + n₀) + 1)).inv ≫ (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) hcast))))) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) (m + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) (m + 1) n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ (mvDelta X A U V hU hV hcov ((m + 1) + n₀) ≫ (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) (by omega : ((m + 1) + n₀) + 1 = (m + 1 + 1) + n₀)))) := by
        rw [mvDelta]; simp only [Category.assoc]
/-- **The `δ`-square, degree zero.** -/
theorem deltaSquare_zero
    (h1 : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) U) (cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A U) n₀))
    (h1V : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) V) (cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A V) n₀))
    (h2 : CategoryTheory.CategoryStruct.comp (mvGWU X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopU X A U n₀ t ht)
          (MVShift.shMap (mvGWU X A U V) n₀))
    (h2V : CategoryTheory.CategoryStruct.comp (mvGWV X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopV X A V n₀ t ht)
          (MVShift.shMap (mvGWV X A U V) n₀))
    (hHomX : CupHomStatement X A n₀ t ht)
    (hHomUV : CupHomStatement (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
      (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) :
    mvDelta X (∅ : Set X) U V hU hV hcov 0 ≫ (Work.Thom.relToAbs ℚ (∅ : Set X) (0 + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith X A (0 + 1) n₀ (Work.Cohomology.relClassOf ℚ X A t ht)))
      = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0 ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) 0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ (mvDelta X A U V hU hV hcov (0 + n₀) ≫ (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) (by omega : (0 + n₀) + 1 = (0 + 1) + n₀)))) := by
  obtain ⟨η, hη⟩ := MVGlue.homotopyInverseMV X U V hU hV hcov
  have hη1 : ∀ k : ℕ, HomologicalComplex.homologyMap η.τ₁ k
      = (eTop X (∅ : Set X) U V hU hV hcov k).inv :=
    fun k => eta_tau1_homology X U V hU hV hcov η hη.1 k
  have hη3 : ∀ k : ℕ, HomologicalComplex.homologyMap η.τ₃ k
      = (eW X (∅ : Set X) U V k).inv :=
    fun k => eta_tau3_homology X U V hU hV hcov η hη.2 k
  have hk1 : 1 ≤ 0 + 1 := by omega
  have hcast : (0 + n₀) + 1 = (0 + 1) + n₀ := by omega
  have h0 := MVShift.shS_delta_naturality (Work.Serre.dqShort_shortExact X (∅ : Set X) U V)
      (Work.Serre.dqShort_shortExact X A U V) n₀
      (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀)
      0 (0 + 1) (by rfl)
  calc mvDelta X (∅ : Set X) U V hU hV hcov 0 ≫ (Work.Thom.relToAbs ℚ (∅ : Set X) (0 + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith X A (0 + 1) n₀ (Work.Cohomology.relClassOf ℚ X A t ht)))

      _ = (eW X (∅ : Set X) U V 0).hom ≫ ((Work.Serre.dqShort_shortExact X (∅ : Set X) U V).δ 0 (0 + 1) (by rfl) ≫ ((eTop X (∅ : Set X) U V hU hV hcov (0 + 1)).inv ≫ (Work.Thom.relToAbs ℚ (∅ : Set X) (0 + 1) ≫ ModuleCat.ofHom (MVGlue.cupWith X A (0 + 1) n₀ (Work.Cohomology.relClassOf ℚ X A t ht))))) := by
        rw [mvDelta]; simp only [Category.assoc]
      _ = (eW X (∅ : Set X) U V 0).hom ≫ ((Work.Serre.dqShort_shortExact X (∅ : Set X) U V).δ 0 (0 + 1) (by rfl) ≫ ((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₁ (0 + 1)) ≫ ((MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ (0 + 1) hk1).hom ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv))) := by
        rw [← phi_tau1_apply_inv X A U V hU hV hcov n₀ t ht h1 h1V h2 h2V η hη1 hHomX (0 + 1) hk1]
      _ = (eW X (∅ : Set X) U V 0).hom ≫ (((Work.Serre.dqShort_shortExact X (∅ : Set X) U V).δ 0 (0 + 1) (by rfl) ≫ (HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₁ (0 + 1))) ≫ ((MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ (0 + 1) hk1).hom ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv)) := by
        simp only [Category.assoc]
      _ = (eW X (∅ : Set X) U V 0).hom ≫ (((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃ 0) ≫ (MVShift.shS_shortExact (Work.Serre.dqShort X A U V) (Work.Serre.dqShort_shortExact X A U V) n₀).δ 0 (0 + 1) (by rfl)) ≫ ((MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ (0 + 1) hk1).hom ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv)) := by
        rw [h0]
      _ = (eW X (∅ : Set X) U V 0).hom ≫ ((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃ 0) ≫ (((MVShift.shS_shortExact (Work.Serre.dqShort X A U V) (Work.Serre.dqShort_shortExact X A U V) n₀).δ 0 (0 + 1) (by rfl) ≫ (MVShift.shK_homologyIso (Work.Serre.dqShort X A U V).X₁ n₀ (0 + 1) hk1).hom) ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv)) := by
        simp only [Category.assoc]
      _ = (eW X (∅ : Set X) U V 0).hom ≫ ((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃ 0) ≫ (((MVShift.shK_homologyZero (Work.Serre.dqShort X A U V).X₃ n₀) ≫ ((Work.Serre.dqShort_shortExact X A U V).δ (0 + n₀) ((0 + n₀) + 1) (by rfl) ≫ (CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast)))) ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv)) := by
        rw [MVShift.shS_delta_comm_zero (Work.Serre.dqShort X A U V) (Work.Serre.dqShort_shortExact X A U V) n₀]
      _ = (eW X (∅ : Set X) U V 0).hom ≫ (((HomologicalComplex.homologyMap (η ≫ cupSES X A U V n₀ t ht h1 h1V h2 h2V ≫ shSMap (MVGlue.zetaSmv X A U V) n₀).τ₃ 0) ≫ (MVShift.shK_homologyZero (Work.Serre.dqShort X A U V).X₃ n₀)) ≫ (((Work.Serre.dqShort_shortExact X A U V).δ (0 + n₀) ((0 + n₀) + 1) (by rfl) ≫ (CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast))) ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv)) := by
        simp only [Category.assoc]
      _ = (eW X (∅ : Set X) U V 0).hom ≫ (((eW X (∅ : Set X) U V 0).inv ≫ ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0 ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) 0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ (eW X A U V (0 + n₀)).hom)) ≫ (((Work.Serre.dqShort_shortExact X A U V).δ (0 + n₀) ((0 + n₀) + 1) (by rfl) ≫ (CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast))) ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv)) := by
        rw [← phi_tau3_apply_zero X A U V n₀ t ht h1 h1V h2 h2V η hη3 hHomUV]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0 ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) 0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V (0 + n₀)).hom ≫ (((Work.Serre.dqShort_shortExact X A U V).δ (0 + n₀) ((0 + n₀) + 1) (by rfl) ≫ (CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast))) ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv)) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0 ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) 0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V (0 + n₀)).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ (0 + n₀) ((0 + n₀) + 1) (by rfl) ≫ ((CategoryTheory.eqToHom (congrArg (fun i => (Work.Serre.dqShort X A U V).X₁.homology i) hcast)) ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv))) := by
        simp only [Category.assoc]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0 ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) 0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V (0 + n₀)).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ (0 + n₀) ((0 + n₀) + 1) (by rfl) ≫ (((eTop X A U V hU hV hcov ((0 + n₀) + 1)).inv ≫ ((CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) hcast)) ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).hom)) ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv))) := by
        rw [← eTop_inv_eqToHom_hom X A U V hU hV hcov hcast]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0 ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) 0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V (0 + n₀)).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ (0 + n₀) ((0 + n₀) + 1) (by rfl) ≫ ((eTop X A U V hU hV hcov ((0 + n₀) + 1)).inv ≫ ((CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) hcast)) ≫ ((eTop X A U V hU hV hcov (0 + 1 + n₀)).hom ≫ (eTop X A U V hU hV hcov (0 + 1 + n₀)).inv))))) := by
        simp only [Category.assoc]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0 ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) 0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ ((eW X A U V (0 + n₀)).hom ≫ ((Work.Serre.dqShort_shortExact X A U V).δ (0 + n₀) ((0 + n₀) + 1) (by rfl) ≫ ((eTop X A U V hU hV hcov ((0 + n₀) + 1)).inv ≫ (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) hcast))))) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) 0 ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) 0 n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)))) ≫ (mvDelta X A U V hU hV hcov (0 + n₀) ≫ (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) (by omega : (0 + n₀) + 1 = (0 + 1) + n₀)))) := by
        rw [mvDelta]; simp only [Category.assoc]
theorem deltaSquare
    (h1 : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) U) (cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A U) n₀))
    (h1V : CategoryTheory.CategoryStruct.comp (mvFU X (∅ : Set X) V) (cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTop X A n₀ t ht)
          (MVShift.shMap (mvFU X A V) n₀))
    (h2 : CategoryTheory.CategoryStruct.comp (mvGWU X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopU X A U n₀ t ht)
          (MVShift.shMap (mvGWU X A U V) n₀))
    (h2V : CategoryTheory.CategoryStruct.comp (mvGWV X (∅ : Set X) U V) (cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (cupTopV X A V n₀ t ht)
          (MVShift.shMap (mvGWV X A U V) n₀))
    (hHomX : CupHomStatement X A n₀ t ht)
    (hHomUV : CupHomStatement (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
      (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht))
    (m : ℕ) :
    mvDelta X (∅ : Set X) U V hU hV hcov m
        ≫ (Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1)
          ≫ ModuleCat.ofHom (MVGlue.cupWith X A (m + 1) n₀
            (Work.Cohomology.relClassOf ℚ X A t ht)))
      = (Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) m
          ≫ ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V))
            m n₀ (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
              (Work.Cohomology.interAU A (U ∩ V)) (cupTgtUV X A U V n₀ t)
              (cupTgtUV_cocycle X A U V n₀ t ht))))
        ≫ (mvDelta X A U V hU hV hcov (m + n₀)
          ≫ CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
            (by omega : (m + n₀) + 1 = (m + 1) + n₀))) := by
  rcases m with _ | m'
  · exact deltaSquare_zero X A U V hU hV hcov n₀ t ht h1 h1V h2 h2V hHomX hHomUV
  · exact deltaSquare_succ X A U V hU hV hcov n₀ t ht h1 h1V h2 h2V hHomX hHomUV m'


/-- The two spellings of the restriction of `U₀` to the overlap: `U₀ovl` (through `U` and then
`U ∩ V`) is the direct restriction along the inclusion `U ∩ V ⊆ X`. -/
theorem U₀ovl_eq_relCohMap (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) :
    U₀ovl X A U V n₀ U₀
      = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          (Work.Cohomology.interAU A (U ∩ V)) A (fun _ hy => hy) ℚ n₀).hom U₀ := by
  have hU : mvRestrU X A U n₀ ≫ mvRestrUVU X A U V n₀
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          (Work.Cohomology.interAU A (U ∩ V)) A (fun _ hx => hx) ℚ n₀ := by
    rw [show mvRestrUVU X A U V n₀ = Work.Thom.relCohMap
          (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
          (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U) (fun _ hx => hx) ℚ n₀ from rfl,
      show mvRestrU X A U n₀ = Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          (Work.Cohomology.interAU A U) A (fun _ hy => hy) ℚ n₀ from rfl,
      Work.Thom.relCohMap_compA (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U) A
          (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) ℚ n₀]
    exact (Work.Thom.relCohMap_congrA _ _ (by ext x; rfl) (fun x hx => hx) (fun x hx => hx)
        ℚ n₀).trans
      (Work.Thom.relCohMap_hcongrA _ _ _ (fun x hx => hx) (fun x hx => hx) ℚ n₀)
  exact congrArg (fun (f : Work.Thom.RelCoh ℚ n₀ X A ⟶ mvCohUV X A U V n₀) =>
    ModuleCat.Hom.hom f U₀) hU

end Delta
