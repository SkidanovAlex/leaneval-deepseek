import Submission.Work.Serre.RatMVDefs
import Submission.Work.Serre.dq_shortExact
import Submission.Work.Serre.dq_quasiIso
import Submission.Work.Serre.thetaRel_exists
import Submission.Work.Serre.dqBiprodIsoSpec
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.Cohomology.hmv_chain_shortExact
import Submission.Work.Cohomology.hmv_isIso_eta
import Submission.Work.Cohomology.hmv_naturality
import Submission.Work.Cohomology.relCohMV_honest_defs
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Bordism.dualComplex_biprod
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

/-! ## §1. The comparison isomorphisms -/

noncomputable def ThetaCmp : ∀ (X : TopCat) (A : Set X),
    Work.Cohomology.relComplex ℚ X A ≅ DQ (Work.Cohomology.relChains X A) :=
  Classical.choose thetaRel_exists

theorem ThetaCmp_nat {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (hf : ∀ x ∈ A, f x ∈ B) :
    (ThetaCmp Y B).hom ≫ dqMap (Work.Cohomology.hmvPairsChains A B f hf)
      = Work.Cohomology.relComplexMap ℚ A B f hf ≫ (ThetaCmp X A).hom :=
  Classical.choose_spec thetaRel_exists A B f hf

noncomputable def zetaTop (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relComplex ℚ X A ⟶ DQ (Work.Cohomology.relMVTopC X A U V) :=
  (ThetaCmp X A).hom ≫ dqMap (Work.Cohomology.HMV.mvPhi X A U V)

noncomputable def zetaU (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U)
      ⟶ DQ (Work.Cohomology.relMVUU X A U V) :=
  (ThetaCmp (TopCat.of ↥U) (Work.Cohomology.interAU A U)).hom
    ≫ dqMap (Work.Cohomology.HMV.etaU A U V)

noncomputable def zetaV (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V)
      ⟶ DQ (Work.Cohomology.relMVVV X A U V) :=
  (ThetaCmp (TopCat.of ↥V) (Work.Cohomology.interAU A V)).hom
    ≫ dqMap (Work.Cohomology.HMV.etaV A U V)

noncomputable def zetaW (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relComplex ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V))
      ⟶ DQ (Work.Cohomology.relMVUV X A U V) :=
  (ThetaCmp (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V))).hom
    ≫ dqMap (Work.Cohomology.relMVUVPhi X A U V)

/-! ## §2. The biproduct comparison -/

noncomputable def dqBiprodIso (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    DQ (C ⊞ D) ≅ DQ C ⊞ DQ D := Classical.choose (dqBiprodIsoSpec C D)

theorem dqBiprodIso_hom (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    (dqBiprodIso C D).hom = biprod.lift (dqMap (biprod.inl : C ⟶ C ⊞ D))
      (dqMap (biprod.inr : D ⟶ C ⊞ D)) :=
  (Classical.choose_spec (dqBiprodIsoSpec C D)).1

theorem dqBiprodIso_inv (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    (dqBiprodIso C D).inv = biprod.desc (dqMap (biprod.fst : C ⊞ D ⟶ C))
      (dqMap (biprod.snd : C ⊞ D ⟶ D)) :=
  (Classical.choose_spec (dqBiprodIsoSpec C D)).2

/-! ## §3. The middle comparison -/

/-- The `U`-component of the cochain-level `F`-map. -/
noncomputable def mvFU (X : TopCat) (A U : Set X) :
    Work.Cohomology.relComplex ℚ X A ⟶
      Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) :=
  Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥U) (X₂ := X) ℚ
    (Work.Cohomology.interAU A U) A
    (Work.Cohomology.subtypeIncl X U) (Work.Cohomology.interAU_incl_subtypeIncl X A U)

/-- The `U`-component of the cochain-level `G`-map. -/
noncomputable def mvGWU (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) ⟶
      Work.Cohomology.relComplex ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) :=
  Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥U) ℚ
    (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U)
    (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)
    (Work.Cohomology.interAU_incl_pdIncl_U X A U V)

/-- The `V`-component of the cochain-level `G`-map. -/
noncomputable def mvGWV (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V) ⟶
      Work.Cohomology.relComplex ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) :=
  Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥V) ℚ
    (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A V)
    (Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right)
    (Work.Cohomology.interAU_incl_pdIncl_V X A U V)

/-- The cochain-level `F`-map of the relative Mayer–Vietoris sequence. -/
noncomputable def mvFChain (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relComplex ℚ X A ⟶
      (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) ⊞
        Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V)) :=
  biprod.lift (mvFU X A U) (mvFU X A V)

/-- The cochain-level `G`-map of the relative Mayer–Vietoris sequence. -/
noncomputable def mvGChain (X : TopCat) (A U V : Set X) :
    (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) ⊞
        Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V))
      ⟶ Work.Cohomology.relComplex ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) :=
  biprod.desc (mvGWU X A U V) (-(mvGWV X A U V))

/-- The comparison for the middle term. -/
noncomputable def zetaMid (X : TopCat) (A U V : Set X) :
    (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) ⊞
        Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V))
      ⟶ DQ (Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V) :=
  biprod.map (zetaU X A U V) (zetaV X A U V)
    ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V) (Work.Cohomology.relMVVV X A U V)).inv

end
end Work.Serre

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-- `h ≫ biprod.lift f g = biprod.lift (h ≫ f) (h ≫ g)`. -/
theorem biprod_comp_lift {C : Type*} [Category C] [Preadditive C] {X Y : C}
    [HasBinaryBiproducts C] (h : X ⟶ Y) {Z W : C} (f : Y ⟶ Z) (g : Y ⟶ W) :
    h ≫ biprod.lift f g = biprod.lift (h ≫ f) (h ≫ g) := by
  refine biprod.ext_to_iff.mpr ⟨?_, ?_⟩
  · rw [Category.assoc, biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, biprod.lift_snd, biprod.lift_snd]

/-- `biprod.map f g ≫ biprod.desc h k = biprod.desc (f ≫ h) (g ≫ k)`. -/
theorem biprod_map_desc {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {X₁ X₂ Y₁ Y₂ Z : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : Y₁ ⟶ Z) (k : Y₂ ⟶ Z) :
    biprod.map f g ≫ biprod.desc h k = biprod.desc (f ≫ h) (g ≫ k) := by
  rw [biprod.map_eq, biprod.desc_eq, biprod.desc_eq]
  simp [Category.assoc]

end
end Work.Serre

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-- `biprod.desc h k ≫ m = biprod.desc (h ≫ m) (k ≫ m)`. -/
theorem biprod_desc_comp {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {X Y Z W : C} (h : X ⟶ Z) (k : Y ⟶ Z) (m : Z ⟶ W) :
    biprod.desc h k ≫ m = biprod.desc (h ≫ m) (k ≫ m) := by
  refine biprod.ext_from_iff.mpr ⟨?_, ?_⟩
  · simp
  · simp

theorem dqMap_desc (X : TopCat) (A U V : Set X) :
    dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
        (Work.Cohomology.HMV.alphaV X A U V))
      = biprod.lift (dqMap (Work.Cohomology.HMV.alphaU X A U V))
          (dqMap (Work.Cohomology.HMV.alphaV X A U V))
        ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
            (Work.Cohomology.relMVVV X A U V)).inv := by
  have hkey : dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
        (Work.Cohomology.HMV.alphaV X A U V))
      ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
          (Work.Cohomology.relMVVV X A U V)).hom
      = biprod.lift (dqMap (Work.Cohomology.HMV.alphaU X A U V))
          (dqMap (Work.Cohomology.HMV.alphaV X A U V)) := by
    rw [dqBiprodIso_hom, biprod_comp_lift]
    congr 1
    · rw [← dqMap_comp]
      rw [show (biprod.inl : Work.Cohomology.relMVUU X A U V ⟶
          Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V)
          ≫ biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
              (Work.Cohomology.HMV.alphaV X A U V) = Work.Cohomology.HMV.alphaU X A U V
        from biprod.inl_desc _ _]
    · rw [← dqMap_comp]
      rw [show (biprod.inr : Work.Cohomology.relMVVV X A U V ⟶
          Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V)
          ≫ biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
              (Work.Cohomology.HMV.alphaV X A U V) = Work.Cohomology.HMV.alphaV X A U V
        from biprod.inr_desc _ _]
  calc dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
        (Work.Cohomology.HMV.alphaV X A U V))
      = dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
          (Work.Cohomology.HMV.alphaV X A U V))
          ≫ 𝟙 (DQ (Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V)) :=
        (Category.comp_id _).symm
    _ = dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
          (Work.Cohomology.HMV.alphaV X A U V))
          ≫ ((dqBiprodIso (Work.Cohomology.relMVUU X A U V)
                (Work.Cohomology.relMVVV X A U V)).hom
              ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
                (Work.Cohomology.relMVVV X A U V)).inv) := by
        rw [Iso.hom_inv_id]
    _ = (dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
          (Work.Cohomology.HMV.alphaV X A U V))
          ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
              (Work.Cohomology.relMVVV X A U V)).hom)
          ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
              (Work.Cohomology.relMVVV X A U V)).inv := (Category.assoc _ _ _).symm
    _ = biprod.lift (dqMap (Work.Cohomology.HMV.alphaU X A U V))
          (dqMap (Work.Cohomology.HMV.alphaV X A U V))
        ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
            (Work.Cohomology.relMVVV X A U V)).inv := by rw [hkey]

theorem dqMap_lift (X : TopCat) (A U V : Set X) :
    dqMap (biprod.lift (Work.Cohomology.HMV.gamma X A U V)
        (-(Work.Cohomology.HMV.delta X A U V)))
      = (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
            (Work.Cohomology.relMVVV X A U V)).hom
        ≫ biprod.desc (dqMap (Work.Cohomology.HMV.gamma X A U V))
            (dqMap (-(Work.Cohomology.HMV.delta X A U V))) := by
  have hkey : (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
          (Work.Cohomology.relMVVV X A U V)).inv
      ≫ dqMap (biprod.lift (Work.Cohomology.HMV.gamma X A U V)
          (-(Work.Cohomology.HMV.delta X A U V)))
      = biprod.desc (dqMap (Work.Cohomology.HMV.gamma X A U V))
          (dqMap (-(Work.Cohomology.HMV.delta X A U V))) := by
    rw [dqBiprodIso_inv, biprod_desc_comp]
    congr 1
    · rw [← dqMap_comp]
      rw [show (biprod.lift (Work.Cohomology.HMV.gamma X A U V)
            (-(Work.Cohomology.HMV.delta X A U V)))
          ≫ (biprod.fst : Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V ⟶
              Work.Cohomology.relMVUU X A U V) = Work.Cohomology.HMV.gamma X A U V
        from biprod.lift_fst _ _]
    · rw [← dqMap_comp]
      rw [show (biprod.lift (Work.Cohomology.HMV.gamma X A U V)
            (-(Work.Cohomology.HMV.delta X A U V)))
          ≫ (biprod.snd : Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V ⟶
              Work.Cohomology.relMVVV X A U V) = -(Work.Cohomology.HMV.delta X A U V)
        from biprod.lift_snd _ _]
  rw [← hkey, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end
end Work.Serre

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

theorem biprod_map_lift {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {X Y Z W V : C} (a : X ⟶ Y) (b : X ⟶ Z) (f : Y ⟶ W) (g : Z ⟶ V) :
    biprod.lift a b ≫ biprod.map f g = biprod.lift (a ≫ f) (b ≫ g) := by
  refine biprod.ext_to_iff.mpr ⟨?_, ?_⟩
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd, biprod.lift_snd]


theorem dqMap_zero' {C D : ChainComplex (ModuleCat ℤ) ℕ} :
    dqMap (0 : C ⟶ D) = 0 := dqMap_zero

theorem dqMap_neg {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) :
    dqMap (-φ) = -dqMap φ := by
  have h : dqMap (-φ) + dqMap φ = 0 := by
    rw [← dqMap_add, neg_add_cancel, dqMap_zero']
  exact eq_neg_of_add_eq_zero_left h

theorem zetaU_gamma (X : TopCat) (A U V : Set X) :
    zetaU X A U V ≫ dqMap (Work.Cohomology.HMV.gamma X A U V)
      = mvGWU X A U V ≫ zetaW X A U V := by
  unfold zetaU zetaW mvGWU
  rw [Category.assoc, ← dqMap_comp, ← Work.Cohomology.hmvChain_natWU, dqMap_comp,
    ← Category.assoc]
  rw [ThetaCmp_nat (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U)
    (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)
    (Work.Cohomology.interAU_incl_pdIncl_U X A U V)]
  simp only [Category.assoc]

theorem zetaV_delta (X : TopCat) (A U V : Set X) :
    zetaV X A U V ≫ dqMap (-(Work.Cohomology.HMV.delta X A U V))
      = (-(mvGWV X A U V)) ≫ zetaW X A U V := by
  have h : zetaV X A U V ≫ dqMap (Work.Cohomology.HMV.delta X A U V)
      = mvGWV X A U V ≫ zetaW X A U V := by
    unfold zetaV zetaW mvGWV
    rw [Category.assoc, ← dqMap_comp, ← Work.Cohomology.hmvChain_natWV, dqMap_comp,
      ← Category.assoc]
    rw [ThetaCmp_nat (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A V)
      (Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right)
      (Work.Cohomology.interAU_incl_pdIncl_V X A U V)]
    simp only [Category.assoc]
  rw [dqMap_neg, Preadditive.comp_neg, h, Preadditive.neg_comp]

theorem zetaTop_alphaU (X : TopCat) (A U V : Set X) :
    zetaTop X A U V ≫ dqMap (Work.Cohomology.HMV.alphaU X A U V)
      = mvFU X A U ≫ zetaU X A U V := by
  unfold zetaTop zetaU mvFU
  rw [Category.assoc, ← dqMap_comp, Work.Cohomology.hmvChain_natU, dqMap_comp,
    ← Category.assoc]
  rw [ThetaCmp_nat (Work.Cohomology.interAU A U) A (Work.Cohomology.subtypeIncl X U)
    (Work.Cohomology.interAU_incl_subtypeIncl X A U)]
  simp only [Category.assoc]

theorem zetaTop_alphaV (X : TopCat) (A U V : Set X) :
    zetaTop X A U V ≫ dqMap (Work.Cohomology.HMV.alphaV X A U V)
      = mvFU X A V ≫ zetaV X A U V := by
  unfold zetaTop zetaV mvFU
  rw [Category.assoc, ← dqMap_comp, Work.Cohomology.hmvChain_natV, dqMap_comp,
    ← Category.assoc]
  rw [ThetaCmp_nat (Work.Cohomology.interAU A V) A (Work.Cohomology.subtypeIncl X V)
    (Work.Cohomology.interAU_incl_subtypeIncl_V X A V)]
  simp only [Category.assoc]

theorem natA (X : TopCat) (A U V : Set X) :
    zetaTop X A U V ≫ dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
        (Work.Cohomology.HMV.alphaV X A U V))
      = mvFChain X A U V ≫ zetaMid X A U V := by
  have hl : biprod.lift (zetaTop X A U V ≫ dqMap (Work.Cohomology.HMV.alphaU X A U V))
        (zetaTop X A U V ≫ dqMap (Work.Cohomology.HMV.alphaV X A U V))
      = biprod.lift (mvFU X A U ≫ zetaU X A U V) (mvFU X A V ≫ zetaV X A U V) := by
    congr 1
    · exact zetaTop_alphaU X A U V
    · exact zetaTop_alphaV X A U V
  have h1 : zetaTop X A U V ≫ biprod.lift (dqMap (Work.Cohomology.HMV.alphaU X A U V))
        (dqMap (Work.Cohomology.HMV.alphaV X A U V))
      = biprod.lift (zetaTop X A U V ≫ dqMap (Work.Cohomology.HMV.alphaU X A U V))
          (zetaTop X A U V ≫ dqMap (Work.Cohomology.HMV.alphaV X A U V)) :=
    biprod_comp_lift _ _ _
  have h2 : biprod.lift (mvFU X A U) (mvFU X A V) ≫ biprod.map (zetaU X A U V) (zetaV X A U V)
      = biprod.lift (mvFU X A U ≫ zetaU X A U V) (mvFU X A V ≫ zetaV X A U V) :=
    biprod_map_lift _ _ _ _
  calc zetaTop X A U V ≫ dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
        (Work.Cohomology.HMV.alphaV X A U V))
      = (zetaTop X A U V ≫ biprod.lift (dqMap (Work.Cohomology.HMV.alphaU X A U V))
            (dqMap (Work.Cohomology.HMV.alphaV X A U V)))
          ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
              (Work.Cohomology.relMVVV X A U V)).inv := by
        rw [dqMap_desc, ← Category.assoc]
    _ = biprod.lift (zetaTop X A U V ≫ dqMap (Work.Cohomology.HMV.alphaU X A U V))
          (zetaTop X A U V ≫ dqMap (Work.Cohomology.HMV.alphaV X A U V))
          ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
              (Work.Cohomology.relMVVV X A U V)).inv := by
        rw [h1]
    _ = biprod.lift (mvFU X A U ≫ zetaU X A U V) (mvFU X A V ≫ zetaV X A U V)
          ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
              (Work.Cohomology.relMVVV X A U V)).inv := by
        rw [hl]
    _ = mvFChain X A U V ≫ zetaMid X A U V := by
        rw [zetaMid, mvFChain, ← Category.assoc, h2]

theorem natB (X : TopCat) (A U V : Set X) :
    zetaMid X A U V ≫ dqMap (biprod.lift (Work.Cohomology.HMV.gamma X A U V)
        (-(Work.Cohomology.HMV.delta X A U V)))
      = mvGChain X A U V ≫ zetaW X A U V := by
  have h3 : (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
        (Work.Cohomology.relMVVV X A U V)).inv
      ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
        (Work.Cohomology.relMVVV X A U V)).hom
      ≫ biprod.desc (dqMap (Work.Cohomology.HMV.gamma X A U V))
          (dqMap (-(Work.Cohomology.HMV.delta X A U V)))
      = biprod.desc (dqMap (Work.Cohomology.HMV.gamma X A U V))
          (dqMap (-(Work.Cohomology.HMV.delta X A U V))) := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc zetaMid X A U V ≫ dqMap (biprod.lift (Work.Cohomology.HMV.gamma X A U V)
        (-(Work.Cohomology.HMV.delta X A U V)))
      = biprod.map (zetaU X A U V) (zetaV X A U V)
          ≫ biprod.desc (dqMap (Work.Cohomology.HMV.gamma X A U V))
              (dqMap (-(Work.Cohomology.HMV.delta X A U V))) := by
        rw [zetaMid, dqMap_lift, Category.assoc, h3]
    _ = biprod.desc (zetaU X A U V ≫ dqMap (Work.Cohomology.HMV.gamma X A U V))
          (zetaV X A U V ≫ dqMap (-(Work.Cohomology.HMV.delta X A U V))) := by
        rw [biprod_map_desc]
    _ = biprod.desc (mvGWU X A U V ≫ zetaW X A U V)
          ((-(mvGWV X A U V)) ≫ zetaW X A U V) := by
        rw [zetaU_gamma, zetaV_delta]
    _ = mvGChain X A U V ≫ zetaW X A U V := by
        rw [mvGChain, biprod_desc_comp]

end
end Work.Serre
namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-! ## §5. The homology of a biproduct of `ℚ`-cochain complexes -/

/-- The homology of a biproduct of cochain complexes of `ℚ`-modules is the biproduct of the
homologies, compatibly with the biproduct structure maps. -/
theorem homology_biprod_iso_Q (C D : CochainComplex (ModuleCat ℚ) ℕ) (k : ℕ) :
    ∃ (e : (C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k),
      (biprod.inl : C.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
        = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k ∧
      (biprod.inr : D.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
        = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  refine ⟨F.mapBiprod C D, ?_, ?_⟩
  · erw [Functor.mapBiprod_inv, biprod.inl_desc]
    rfl
  · erw [Functor.mapBiprod_inv, biprod.inr_desc]
    rfl

/-- The chosen identification of the homology of a biproduct of cochain complexes of `ℚ`-modules
with the biproduct of the homologies. -/
noncomputable def hbip (C D : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (C ⊞ D).homology n ≅ C.homology n ⊞ D.homology n :=
  Classical.choose (homology_biprod_iso_Q C D n)

theorem hbip_inl (C D : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n) ≫ (hbip C D n).inv
      = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n :=
  (Classical.choose_spec (homology_biprod_iso_Q C D n)).1

theorem hbip_inr (C D : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n) ≫ (hbip C D n).inv
      = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n :=
  (Classical.choose_spec (homology_biprod_iso_Q C D n)).2

theorem hbip_hom_inl (C D : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n ≫ (hbip C D n).hom
      = (biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n) := by
  rw [← hbip_inl C D n, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem hbip_hom_inr (C D : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n ≫ (hbip C D n).hom
      = (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n) := by
  rw [← hbip_inr C D n, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Extensionality for maps out of the homology of a biproduct of cochain complexes, expressed by
the two homology maps of the biproduct inclusions. -/
theorem hbip_hom_ext (C D : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) {T : ModuleCat ℚ}
    {f g : (C ⊞ D).homology n ⟶ T}
    (h₁ : HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n ≫ f
        = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n ≫ g)
    (h₂ : HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n ≫ f
        = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n ≫ g) : f = g := by
  have h₁' : (biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n)
        ≫ ((hbip C D n).inv ≫ f)
      = (biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n)
        ≫ ((hbip C D n).inv ≫ g) := by
    rw [← Category.assoc, ← Category.assoc, hbip_inl C D n]
    exact h₁
  have h₂' : (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n)
        ≫ ((hbip C D n).inv ≫ f)
      = (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n)
        ≫ ((hbip C D n).inv ≫ g) := by
    rw [← Category.assoc, ← Category.assoc, hbip_inr C D n]
    exact h₂
  exact (cancel_epi (hbip C D n).inv).mp (biprod.ext_from_iff.mpr ⟨h₁', h₂'⟩)

theorem hbip_hom_fst (C D : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (hbip C D n).hom ≫ (biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n)
      = HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n := by
  refine hbip_hom_ext C D n ?_ ?_
  · rw [← Category.assoc, hbip_hom_inl C D n, biprod.inl_fst,
      ← HomologicalComplex.homologyMap_comp, biprod.inl_fst, HomologicalComplex.homologyMap_id]
  · rw [← Category.assoc, hbip_hom_inr C D n, biprod.inr_fst,
      ← HomologicalComplex.homologyMap_comp, biprod.inr_fst,
      HomologicalComplex.homologyMap_zero]

theorem hbip_hom_snd (C D : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (hbip C D n).hom ≫ (biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n)
      = HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n := by
  refine hbip_hom_ext C D n ?_ ?_
  · rw [← Category.assoc, hbip_hom_inl C D n, biprod.inl_snd,
      ← HomologicalComplex.homologyMap_comp, biprod.inl_snd,
      HomologicalComplex.homologyMap_zero]
  · rw [← Category.assoc, hbip_hom_inr C D n, biprod.inr_snd,
      ← HomologicalComplex.homologyMap_comp, biprod.inr_snd, HomologicalComplex.homologyMap_id]

/-- **The homology of a `lift`**: the homology of the lift of two maps into a biproduct is the
lift of the homologies, up to the identification `hbip`. -/
theorem homologyMap_biprod_lift {C D E : CochainComplex (ModuleCat ℚ) ℕ}
    (f : E ⟶ C) (g : E ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.lift f g) n
      = biprod.lift (HomologicalComplex.homologyMap f n) (HomologicalComplex.homologyMap g n)
        ≫ (hbip C D n).inv := by
  refine (cancel_mono (hbip C D n).hom).mp ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine biprod.ext_to_iff.mpr ⟨?_, ?_⟩
  · rw [Category.assoc, hbip_hom_fst, ← HomologicalComplex.homologyMap_comp, biprod.lift_fst,
      biprod.lift_fst]
  · rw [Category.assoc, hbip_hom_snd, ← HomologicalComplex.homologyMap_comp, biprod.lift_snd,
      biprod.lift_snd]

/-- **The homology of a `desc`**: the homology of the desc of two maps out of a biproduct is the
`desc` of the homologies, up to the identification `hbip`. -/
theorem homologyMap_biprod_desc {C D E : CochainComplex (ModuleCat ℚ) ℕ}
    (f : C ⟶ E) (g : D ⟶ E) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.desc f g) n
      = (hbip C D n).hom
        ≫ biprod.desc (HomologicalComplex.homologyMap f n)
            (HomologicalComplex.homologyMap g n) := by
  refine hbip_hom_ext C D n ?_ ?_
  · rw [← Category.assoc, hbip_hom_inl C D n, biprod.inl_desc,
      ← HomologicalComplex.homologyMap_comp, biprod.inl_desc]
  · rw [← Category.assoc, hbip_hom_inr C D n, biprod.inr_desc,
      ← HomologicalComplex.homologyMap_comp, biprod.inr_desc]

end

end Work.Serre
namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-! ## §5b. The short exact sequence of the small model -/

/-- The zero composite of the two chain-level relative Mayer–Vietoris maps. -/
theorem mvHz (X : TopCat) (A U V : Set X) :
    biprod.lift (Work.Cohomology.HMV.gamma X A U V)
        (-(Work.Cohomology.HMV.delta X A U V))
      ≫ biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
        (Work.Cohomology.HMV.alphaV X A U V) = 0 := by
  rw [biprod.lift_desc, Preadditive.neg_comp]
  have h := Work.Cohomology.gamma_comp_alphaU_eq_delta_comp_alphaV X A U V
  rw [← h]
  simp

/-- The chain-level relative Mayer–Vietoris short complex (small chains). -/
abbrev mvShortZ (X : TopCat) (A U V : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (biprod.lift (Work.Cohomology.HMV.gamma X A U V)
      (-(Work.Cohomology.HMV.delta X A U V)))
    (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
      (Work.Cohomology.HMV.alphaV X A U V)) (mvHz X A U V)

theorem mvShortZ_shortExact (X : TopCat) (A U V : Set X) :
    (mvShortZ X A U V).ShortExact :=
  Work.Cohomology.hmv_chain_shortExact X A U V (mvHz X A U V)

/-- The rational sheet of the relative Mayer–Vietoris sequence. -/
abbrev dqShort (X : TopCat) (A U V : Set X) : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) :=
  ShortComplex.mk (dqMap (mvShortZ X A U V).g) (dqMap (mvShortZ X A U V).f)
    (by rw [← dqMap_comp, (mvShortZ X A U V).zero, dqMap_zero])

theorem dqShort_shortExact (X : TopCat) (A U V : Set X) :
    (dqShort X A U V).ShortExact :=
  dq_shortExact (mvShortZ_shortExact X A U V) (dqShort X A U V).zero

/-! ## §5c. The comparison isomorphisms are quasi-isomorphisms -/

/-- `dqMap` of an isomorphism is an isomorphism. -/
theorem isIso_dqMap {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) [IsIso φ] :
    IsIso (dqMap φ) := by
  refine IsIso.mk ⟨dqMap (inv φ), ?_, ?_⟩
  · rw [← dqMap_comp, IsIso.inv_hom_id φ, dqMap_id]
  · rw [← dqMap_comp, IsIso.hom_inv_id φ, dqMap_id]

theorem isIso_homologyMap_zetaTop (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (zetaTop X A U V) n) := by
  haveI h1 : IsIso (HomologicalComplex.homologyMap (ThetaCmp X A).hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n)
      (ThetaCmp X A).hom
  haveI h2 : IsIso (HomologicalComplex.homologyMap
      (dqMap (Work.Cohomology.HMV.mvPhi X A U V)) n) :=
    dq_quasiIso (Work.Cohomology.HMV.mvPhi X A U V)
      (fun m => Work.Cohomology.HMV.isIso_homologyMap_mvPhi X A U V hU hV hcov m) n
  rw [show zetaTop X A U V = (ThetaCmp X A).hom ≫ dqMap (Work.Cohomology.HMV.mvPhi X A U V)
      from rfl]
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

theorem isIso_homologyMap_zetaU (X : TopCat) (A U V : Set X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (zetaU X A U V) n) := by
  haveI h1 : IsIso (HomologicalComplex.homologyMap
      (ThetaCmp (TopCat.of ↥U) (Work.Cohomology.interAU A U)).hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n)
      (ThetaCmp (TopCat.of ↥U) (Work.Cohomology.interAU A U)).hom
  haveI h2 : IsIso (Work.Cohomology.HMV.etaU A U V) := (Work.Cohomology.hmv_isIso_eta X A U V).1
  haveI h3 : IsIso (dqMap (Work.Cohomology.HMV.etaU A U V)) := isIso_dqMap _
  rw [show zetaU X A U V = (ThetaCmp (TopCat.of ↥U) (Work.Cohomology.interAU A U)).hom
      ≫ dqMap (Work.Cohomology.HMV.etaU A U V) from rfl]
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

theorem isIso_homologyMap_zetaV (X : TopCat) (A U V : Set X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (zetaV X A U V) n) := by
  haveI h1 : IsIso (HomologicalComplex.homologyMap
      (ThetaCmp (TopCat.of ↥V) (Work.Cohomology.interAU A V)).hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n)
      (ThetaCmp (TopCat.of ↥V) (Work.Cohomology.interAU A V)).hom
  haveI h2 : IsIso (Work.Cohomology.HMV.etaV A U V) := (Work.Cohomology.hmv_isIso_eta X A U V).2.1
  haveI h3 : IsIso (dqMap (Work.Cohomology.HMV.etaV A U V)) := isIso_dqMap _
  rw [show zetaV X A U V = (ThetaCmp (TopCat.of ↥V) (Work.Cohomology.interAU A V)).hom
      ≫ dqMap (Work.Cohomology.HMV.etaV A U V) from rfl]
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

theorem isIso_homologyMap_zetaW (X : TopCat) (A U V : Set X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (zetaW X A U V) n) := by
  haveI h1 : IsIso (HomologicalComplex.homologyMap
      (ThetaCmp (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V))).hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n)
      (ThetaCmp (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V))).hom
  haveI h2 : IsIso (Work.Cohomology.relMVUVPhi X A U V) :=
    (Work.Cohomology.hmv_isIso_eta X A U V).2.2
  haveI h3 : IsIso (dqMap (Work.Cohomology.relMVUVPhi X A U V)) := isIso_dqMap _
  rw [show zetaW X A U V = (ThetaCmp (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU A (U ∩ V))).hom
      ≫ dqMap (Work.Cohomology.relMVUVPhi X A U V) from rfl]
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

theorem isIso_homologyMap_zetaMid (X : TopCat) (A U V : Set X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (zetaMid X A U V) n) := by
  haveI hU' : IsIso (zetaU X A U V) := by
    rw [show zetaU X A U V = (ThetaCmp (TopCat.of ↥U) (Work.Cohomology.interAU A U)).hom
      ≫ dqMap (Work.Cohomology.HMV.etaU A U V) from rfl]
    haveI h2 : IsIso (Work.Cohomology.HMV.etaU A U V) :=
      (Work.Cohomology.hmv_isIso_eta X A U V).1
    haveI h3 : IsIso (dqMap (Work.Cohomology.HMV.etaU A U V)) := isIso_dqMap _
    infer_instance
  haveI hV' : IsIso (zetaV X A U V) := by
    rw [show zetaV X A U V = (ThetaCmp (TopCat.of ↥V) (Work.Cohomology.interAU A V)).hom
      ≫ dqMap (Work.Cohomology.HMV.etaV A U V) from rfl]
    haveI h2 : IsIso (Work.Cohomology.HMV.etaV A U V) :=
      (Work.Cohomology.hmv_isIso_eta X A U V).2.1
    haveI h3 : IsIso (dqMap (Work.Cohomology.HMV.etaV A U V)) := isIso_dqMap _
    infer_instance
  haveI h1 : IsIso (biprod.map (zetaU X A U V) (zetaV X A U V)) := by
    have h : biprod.map (zetaU X A U V) (zetaV X A U V)
        = (biprod.mapIso (asIso (zetaU X A U V)) (asIso (zetaV X A U V))).hom := by
      rw [biprod.mapIso_hom, asIso_hom, asIso_hom]
    rw [h]
    exact Iso.isIso_hom (biprod.mapIso (asIso (zetaU X A U V)) (asIso (zetaV X A U V)))
  rw [show zetaMid X A U V = biprod.map (zetaU X A U V) (zetaV X A U V)
      ≫ (dqBiprodIso (Work.Cohomology.relMVUU X A U V)
        (Work.Cohomology.relMVVV X A U V)).inv from rfl]
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

end

end Work.Serre
namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-! ## §6. The bridge between the honest model and the small-chain model -/

/-- The `U`-component of the honest `F`-map is the homology of the cochain-level inclusion. -/
theorem homologyMap_mvFU_U (X : TopCat) (A U : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (mvFU X A U) n = mvRestrU X A U n := rfl

/-- The `V`-component of the honest `F`-map is the homology of the cochain-level inclusion. -/
theorem homologyMap_mvFU_V (X : TopCat) (A V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (mvFU X A V) n = mvRestrV X A V n := rfl

/-- The `U`-component of the honest `G`-map. -/
theorem homologyMap_mvGWU (X : TopCat) (A U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (mvGWU X A U V) n = mvRestrUVU X A U V n := rfl

/-- The `V`-component of the honest `G`-map. -/
theorem homologyMap_mvGWV (X : TopCat) (A U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (mvGWV X A U V) n = mvRestrUVV X A U V n := rfl

/-- The honest `G`-map as a `desc`. -/
theorem mvG_eq_desc (X : TopCat) (A U V : Set X) (n : ℕ) :
    mvG X A U V n = biprod.desc (mvRestrUVU X A U V n) (-(mvRestrUVV X A U V n)) := by
  rw [mvG, biprod.desc_eq]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_neg,
    LinearMap.neg_comp, sub_eq_add_neg]

/-- **Bridge for `F`.** -/
theorem homologyMap_mvFChain (X : TopCat) (A U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (mvFChain X A U V) n
        ≫ (hbip (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U))
            (Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V)) n).hom
      = mvF X A U V n := by
  rw [mvFChain, homologyMap_biprod_lift, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    mvF, homologyMap_mvFU_U, homologyMap_mvFU_V]
  rfl

/-- **Bridge for `G`.** -/
theorem homologyMap_mvGChain (X : TopCat) (A U V : Set X) (n : ℕ) :
    (hbip (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U))
        (Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V)) n).inv
      ≫ HomologicalComplex.homologyMap (mvGChain X A U V) n
      = mvG X A U V n := by
  have hdesc : HomologicalComplex.homologyMap (mvGChain X A U V) n
      = (hbip (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U))
            (Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V)) n).hom
        ≫ biprod.desc (mvRestrUVU X A U V n) (-(mvRestrUVV X A U V n)) := by
    rw [mvGChain, homologyMap_biprod_desc, HomologicalComplex.homologyMap_neg,
      homologyMap_mvGWU, homologyMap_mvGWV]
  rw [hdesc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, mvG_eq_desc X A U V n]
  rfl

end

end Work.Serre
namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-! ## §7. Linear-algebra transfer lemmas -/

theorem surjective_hom_of_iso {M N : ModuleCat ℚ} (e : M ≅ N) :
    Function.Surjective e.hom.hom := by
  intro y
  exact ⟨e.inv.hom y, by
    have h := congrArg (fun (f : N ⟶ N) => f.hom y) (Iso.inv_hom_id e)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h⟩

theorem injective_hom_of_iso {M N : ModuleCat ℚ} (e : M ≅ N) :
    Function.Injective e.hom.hom := by
  intro x y hxy
  have hx := congrArg (fun (f : M ⟶ M) => f.hom x) (Iso.hom_inv_id e)
  have hy := congrArg (fun (f : M ⟶ M) => f.hom y) (Iso.hom_inv_id e)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    at hx hy
  rw [← hx, hxy, hy]

/-- Preimages under the forward map of an isomorphism of modules are images under the inverse. -/
theorem comap_hom_eq_map_inv {M N : ModuleCat ℚ} (e : M ≅ N) (S : Submodule ℚ ↥N) :
    Submodule.comap e.hom.hom S = Submodule.map e.inv.hom S := by
  ext x
  rw [Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨e.hom.hom x, hx, ?_⟩
    have h := congrArg (fun (f : M ⟶ M) => f.hom x) (Iso.hom_inv_id e)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h
  · rintro ⟨y, hy, rfl⟩
    have h := congrArg (fun (f : N ⟶ N) => f.hom y) (Iso.inv_hom_id e)
    have h2 : e.hom.hom (e.inv.hom y) = y := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using h
    rw [h2]
    exact hy

theorem range_comp_iso_inv {M N P : ModuleCat ℚ} (f : M ⟶ P) (e : N ≅ P) :
    LinearMap.range ((f ≫ e.inv).hom) = Submodule.map e.inv.hom (LinearMap.range f.hom) := by
  rw [ModuleCat.hom_comp, LinearMap.range_comp]

theorem range_comp_hom_of_surj {M N P : ModuleCat ℚ} (f : M ⟶ N) (g : N ⟶ P)
    (hf : Function.Surjective f.hom) : LinearMap.range (f ≫ g).hom = LinearMap.range g.hom := by
  have hf' : LinearMap.range (ModuleCat.Hom.hom f) = ⊤ := LinearMap.range_eq_top.mpr hf
  rw [ModuleCat.hom_comp, LinearMap.range_comp, hf', Submodule.map_top]

theorem ker_comp_iso_hom {M N P : ModuleCat ℚ} (e : M ≅ N) (f : N ⟶ P) :
    LinearMap.ker ((e.hom ≫ f).hom) = Submodule.comap e.hom.hom (LinearMap.ker f.hom) := by
  rw [ModuleCat.hom_comp, LinearMap.ker_comp]

theorem ker_comp_iso_inv {M N P : ModuleCat ℚ} (f : M ⟶ P) (e : N ≅ P) :
    LinearMap.ker ((f ≫ e.inv).hom) = LinearMap.ker f.hom := by
  have hker : LinearMap.ker (ModuleCat.Hom.hom e.inv) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (injective_hom_of_iso e.symm)
  rw [ModuleCat.hom_comp, LinearMap.ker_comp, hker, Submodule.comap_bot]

/-! ## §8. The comparison isomorphisms on homology -/

noncomputable def eTop (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    (Work.Cohomology.relComplex ℚ X A).homology n
      ≅ (DQ (Work.Cohomology.relMVTopC X A U V)).homology n :=
  @asIso (ModuleCat ℚ) _ _ _ (HomologicalComplex.homologyMap (zetaTop X A U V) n)
    (isIso_homologyMap_zetaTop X A U V hU hV hcov n)

theorem eTop_hom (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    (eTop X A U V hU hV hcov n).hom
      = HomologicalComplex.homologyMap (zetaTop X A U V) n := rfl

noncomputable def eMid (X : TopCat) (A U V : Set X) (n : ℕ) :
    (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) ⊞
        Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V)).homology n
      ≅ (DQ (Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V)).homology n :=
  @asIso (ModuleCat ℚ) _ _ _ (HomologicalComplex.homologyMap (zetaMid X A U V) n)
    (isIso_homologyMap_zetaMid X A U V n)

theorem eMid_hom (X : TopCat) (A U V : Set X) (n : ℕ) :
    (eMid X A U V n).hom = HomologicalComplex.homologyMap (zetaMid X A U V) n := rfl

noncomputable def eW (X : TopCat) (A U V : Set X) (n : ℕ) :
    mvCohUV X A U V n ≅ (DQ (Work.Cohomology.relMVUV X A U V)).homology n :=
  @asIso (ModuleCat ℚ) _ _ _ (HomologicalComplex.homologyMap (zetaW X A U V) n)
    (isIso_homologyMap_zetaW X A U V n)

theorem eW_hom (X : TopCat) (A U V : Set X) (n : ℕ) :
    (eW X A U V n).hom = HomologicalComplex.homologyMap (zetaW X A U V) n := rfl

/-- The comparison for the middle term, in the honest biproduct coordinates. -/
noncomputable def ea (X : TopCat) (A U V : Set X) (n : ℕ) :
    (mvCohU X A U n ⊞ mvCohV X A V n)
      ≅ (DQ (Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V)).homology n :=
  (hbip (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U))
      (Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU A V)) n).symm
    ≪≫ eMid X A U V n

theorem surjective_zetaTop (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap (zetaTop X A U V) n).hom := by
  have h := surjective_hom_of_iso (eTop X A U V hU hV hcov n)
  rwa [eTop_hom] at h

/-! ## §9. The maps of the small model and the identification of the honest maps -/

/-- The first map of the relative Mayer–Vietoris sequence on the small model. -/
noncomputable def mvHomF (X : TopCat) (A U V : Set X) (n : ℕ) :
    (DQ (Work.Cohomology.relMVTopC X A U V)).homology n ⟶
      (DQ (Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V)).homology n :=
  HomologicalComplex.homologyMap
    (dqMap (biprod.desc (Work.Cohomology.HMV.alphaU X A U V)
      (Work.Cohomology.HMV.alphaV X A U V))) n

/-- The second map of the relative Mayer–Vietoris sequence on the small model. -/
noncomputable def mvHomG (X : TopCat) (A U V : Set X) (n : ℕ) :
    (DQ (Work.Cohomology.relMVUU X A U V ⊞ Work.Cohomology.relMVVV X A U V)).homology n ⟶
      (DQ (Work.Cohomology.relMVUV X A U V)).homology n :=
  HomologicalComplex.homologyMap
    (dqMap (biprod.lift (Work.Cohomology.HMV.gamma X A U V)
      (-(Work.Cohomology.HMV.delta X A U V)))) n

/-- **The honest `F`-map is the small-model `F`-map conjugated by the comparison isomorphisms.** -/
theorem mvF_eq (X : TopCat) (A U V : Set X) (n : ℕ) :
    mvF X A U V n
      = (HomologicalComplex.homologyMap (zetaTop X A U V) n ≫ mvHomF X A U V n)
        ≫ (ea X A U V n).inv := by
  have hnat : HomologicalComplex.homologyMap (zetaTop X A U V) n ≫ mvHomF X A U V n
      = HomologicalComplex.homologyMap (mvFChain X A U V) n
        ≫ HomologicalComplex.homologyMap (zetaMid X A U V) n := by
    rw [mvHomF, ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      natA X A U V]
  rw [Iso.eq_comp_inv, ← homologyMap_mvFChain X A U V n, Category.assoc, ea, Iso.trans_hom,
    Iso.symm_hom, eMid_hom, Iso.hom_inv_id_assoc, hnat]

/-- **The honest `G`-map is the small-model `G`-map conjugated by the comparison isomorphisms.** -/
theorem mvG_eq (X : TopCat) (A U V : Set X) (n : ℕ) :
    mvG X A U V n
      = ((ea X A U V n).hom ≫ mvHomG X A U V n) ≫ (eW X A U V n).inv := by
  have hnat : HomologicalComplex.homologyMap (zetaMid X A U V) n ≫ mvHomG X A U V n
      = HomologicalComplex.homologyMap (mvGChain X A U V) n
        ≫ HomologicalComplex.homologyMap (zetaW X A U V) n := by
    rw [mvHomG, ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      natB X A U V]
  have hkey : (eMid X A U V n).inv ≫ HomologicalComplex.homologyMap (mvGChain X A U V) n
      = mvHomG X A U V n ≫ (eW X A U V n).inv := by
    rw [Iso.inv_comp_eq, eMid_hom, ← Category.assoc, hnat, ← eW_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [← homologyMap_mvGChain X A U V n, ← Iso.hom_inv_id_assoc (eMid X A U V n)
      (HomologicalComplex.homologyMap (mvGChain X A U V) n), hkey, ea, Iso.trans_hom,
    Iso.symm_hom, eMid_hom]
  simp only [Category.assoc]

/-- The connecting homomorphism of the rational relative Mayer–Vietoris sequence. -/
noncomputable def mvDelta (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    mvCohUV X A U V n ⟶ Work.Thom.RelCoh ℚ (n + 1) X A :=
  ((eW X A U V n).hom
      ≫ (dqShort_shortExact X A U V).δ n (n + 1) (Work.Cohomology.relCohMVUpRel n))
    ≫ (eTop X A U V hU hV hcov (n + 1)).inv

/-! ## §10. Exactness -/

/-- Exactness at the middle term of the small model. -/
theorem range_mvHomF_eq_ker_mvHomG (X : TopCat) (A U V : Set X) (n : ℕ) :
    LinearMap.range (mvHomF X A U V n).hom = LinearMap.ker (mvHomG X A U V n).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker ((dqShort_shortExact X A U V).homology_exact₂ n)

/-- Exactness at the third term of the small model. -/
theorem range_mvHomG_eq_ker_delta (X : TopCat) (A U V : Set X) (n : ℕ) :
    LinearMap.range (mvHomG X A U V n).hom
      = LinearMap.ker ((dqShort_shortExact X A U V).δ n (n + 1)
          (Work.Cohomology.relCohMVUpRel n)).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker
    ((dqShort_shortExact X A U V).homology_exact₃ n (n + 1) (Work.Cohomology.relCohMVUpRel n))

/-- Exactness at the first term of the small model. -/
theorem range_delta_eq_ker_mvHomF (X : TopCat) (A U V : Set X) (n : ℕ) :
    LinearMap.range ((dqShort_shortExact X A U V).δ n (n + 1)
        (Work.Cohomology.relCohMVUpRel n)).hom
      = LinearMap.ker (mvHomF X A U V (n + 1)).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker
    ((dqShort_shortExact X A U V).homology_exact₁ n (n + 1) (Work.Cohomology.relCohMVUpRel n))

/-- Exactness at `H^n(U,U∩A) ⊞ H^n(V,V∩A)`. -/
theorem exact_mvF_mvG (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (mvF X A U V n).hom = LinearMap.ker (mvG X A U V n).hom := by
  rw [mvF_eq X A U V n, mvG_eq X A U V n,
    range_comp_iso_inv _ (ea X A U V n),
    range_comp_hom_of_surj _ _ (surjective_zetaTop X A U V hU hV hcov n),
    range_mvHomF_eq_ker_mvHomG X A U V n,
    ← comap_hom_eq_map_inv (ea X A U V n) (LinearMap.ker (mvHomG X A U V n).hom),
    ker_comp_iso_inv _ (eW X A U V n),
    ker_comp_iso_hom (ea X A U V n) (mvHomG X A U V n)]

/-- Exactness at `H^n(U∩V,U∩V∩A)`. -/
theorem exact_mvG_mvDelta (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (mvG X A U V n).hom
      = LinearMap.ker (mvDelta X A U V hU hV hcov n).hom := by
  rw [mvG_eq X A U V n, mvDelta,
    range_comp_iso_inv _ (eW X A U V n),
    range_comp_hom_of_surj _ _ (surjective_hom_of_iso (ea X A U V n)),
    range_mvHomG_eq_ker_delta X A U V n,
    ← comap_hom_eq_map_inv (eW X A U V n)
      (LinearMap.ker ((dqShort_shortExact X A U V).δ n (n + 1)
        (Work.Cohomology.relCohMVUpRel n)).hom),
    ker_comp_iso_inv _ (eTop X A U V hU hV hcov (n + 1)),
    ker_comp_iso_hom (eW X A U V n) _]

/-- Exactness at `H^{n+1}(X,A)`. -/
theorem exact_mvDelta_mvF (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (mvDelta X A U V hU hV hcov n).hom
      = LinearMap.ker (mvF X A U V (n + 1)).hom := by
  rw [mvDelta, mvF_eq X A U V (n + 1),
    range_comp_iso_inv _ (eTop X A U V hU hV hcov (n + 1)),
    range_comp_hom_of_surj _ _ (surjective_hom_of_iso (eW X A U V n)),
    range_delta_eq_ker_mvHomF X A U V n,
    ← comap_hom_eq_map_inv (eTop X A U V hU hV hcov (n + 1))
      (LinearMap.ker (mvHomF X A U V (n + 1)).hom),
    ker_comp_iso_inv _ (ea X A U V (n + 1)),
    ← eTop_hom X A U V hU hV hcov (n + 1),
    ker_comp_iso_hom (eTop X A U V hU hV hcov (n + 1)) _]

end

end Work.Serre

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- **The rational relative Mayer–Vietoris long exact sequence.** -/
theorem relCohMV_les_rat (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    ∃ (d : ∀ n : ℕ, Work.Serre.mvCohUV X A U V n ⟶ Work.Thom.RelCoh ℚ (n + 1) X A),
      (∀ n, LinearMap.range (Work.Serre.mvF X A U V n).hom
          = LinearMap.ker (Work.Serre.mvG X A U V n).hom) ∧
      (∀ n, LinearMap.range (Work.Serre.mvG X A U V n).hom = LinearMap.ker (d n).hom) ∧
      (∀ n, LinearMap.range (d n).hom
          = LinearMap.ker (Work.Serre.mvF X A U V (n + 1)).hom) :=
  ⟨mvDelta X A U V hU hV hcov,
    fun n => exact_mvF_mvG X A U V hU hV hcov n,
    fun n => exact_mvG_mvDelta X A U V hU hV hcov n,
    fun n => exact_mvDelta_mvF X A U V hU hV hcov n⟩

end

end Work.Serre
