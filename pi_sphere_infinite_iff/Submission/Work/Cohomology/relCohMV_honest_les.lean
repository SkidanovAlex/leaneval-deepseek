import Mathlib
import Submission.Work.Cohomology.pd_glue_defs
import Submission.Work.Cohomology.relCohMV_les
import Submission.Work.Cohomology.relCohMV_honest_defs
import Submission.Work.Cohomology.relCohMV_honest_prereq
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Cohomology.hmv_shortExact
import Submission.Work.Cohomology.hmv_isIso_eta
import Submission.Work.Cohomology.hmv_naturality

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The homology of a biproduct of cochain complexes -/

/-- The chosen isomorphism between the homology of a biproduct of cochain complexes and the
biproduct of the homologies (`homology_biprod_iso`), together with its defining rules. -/
noncomputable def homBiprodIso (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    (C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k :=
  (homology_biprod_iso C D k).choose

theorem homBiprodIso_inl (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    biprod.inl ≫ (homBiprodIso C D k).inv
      = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k :=
  (homology_biprod_iso C D k).choose_spec.1

theorem homBiprodIso_inr (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    biprod.inr ≫ (homBiprodIso C D k).inv
      = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k :=
  (homology_biprod_iso C D k).choose_spec.2

/-- The composite `biprod.inl ≫ (homBiprodIso).inv ≫ f` is `H(biprod.inl) ≫ f`. -/
theorem homBiprodIso_inl_assoc (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) {T : ModuleCat ℤ}
    (f : (C ⊞ D).homology k ⟶ T) :
    biprod.inl ≫ (homBiprodIso C D k).inv ≫ f
      = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k ≫ f := by
  rw [← Category.assoc, homBiprodIso_inl C D k]

/-- The composite `biprod.inr ≫ (homBiprodIso).inv ≫ f` is `H(biprod.inr) ≫ f`. -/
theorem homBiprodIso_inr_assoc (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) {T : ModuleCat ℤ}
    (f : (C ⊞ D).homology k ⟶ T) :
    biprod.inr ≫ (homBiprodIso C D k).inv ≫ f
      = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k ≫ f := by
  rw [← Category.assoc, homBiprodIso_inr C D k]

/-- The inverse of the biproduct-homology isomorphism is the `desc` of the two homology
inclusions. -/
theorem homBiprodIso_inv_desc (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    (homBiprodIso C D k).inv
      = biprod.desc (HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k)
          (HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k) := by
  refine biprod.ext_from_iff.mpr ⟨?_, ?_⟩
  · rw [homBiprodIso_inl C D k]
    exact (biprod.inl_desc _ _).symm
  · rw [homBiprodIso_inr C D k]
    exact (biprod.inr_desc _ _).symm

/-- The composite `H(inl) ≫ (homBiprodIso).hom` is `biprod.inl`. -/
theorem homBiprodIso_hom_inl (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k ≫ (homBiprodIso C D k).hom
      = biprod.inl := by
  rw [← homBiprodIso_inl C D k, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The composite `H(inr) ≫ (homBiprodIso).hom` is `biprod.inr`. -/
theorem homBiprodIso_hom_inr (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k ≫ (homBiprodIso C D k).hom
      = biprod.inr := by
  rw [← homBiprodIso_inr C D k, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Extensionality for maps out of the homology of a biproduct of cochain complexes, expressed in
terms of the two summands of the biproduct of the homologies. -/
theorem homBiprodIso_hom_ext (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) {T : ModuleCat ℤ}
    {f g : (C ⊞ D).homology k ⟶ T}
    (h₁ : HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k ≫ f
      = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k ≫ g)
    (h₂ : HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k ≫ f
      = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k ≫ g) : f = g := by
  have h₁' : biprod.inl ≫ ((homBiprodIso C D k).inv ≫ f)
      = biprod.inl ≫ ((homBiprodIso C D k).inv ≫ g) := by
    rw [← Category.assoc, ← Category.assoc, homBiprodIso_inl C D k]
    exact h₁
  have h₂' : biprod.inr ≫ ((homBiprodIso C D k).inv ≫ f)
      = biprod.inr ≫ ((homBiprodIso C D k).inv ≫ g) := by
    rw [← Category.assoc, ← Category.assoc, homBiprodIso_inr C D k]
    exact h₂
  have h := biprod.ext_from_iff.mpr ⟨h₁', h₂'⟩
  exact (cancel_epi (homBiprodIso C D k).inv).mp h

/-- The composite of the biproduct-homology isomorphism with the first projection is the first
homology projection. -/
theorem homBiprodIso_hom_fst (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    (homBiprodIso C D k).hom
        ≫ (biprod.fst : C.homology k ⊞ D.homology k ⟶ C.homology k)
      = HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) k := by
  refine homBiprodIso_hom_ext C D k ?_ ?_
  · rw [← Category.assoc, homBiprodIso_hom_inl C D k, biprod.inl_fst,
      ← HomologicalComplex.homologyMap_comp, biprod.inl_fst, HomologicalComplex.homologyMap_id]
  · rw [← Category.assoc, homBiprodIso_hom_inr C D k, biprod.inr_fst,
      ← HomologicalComplex.homologyMap_comp, biprod.inr_fst, HomologicalComplex.homologyMap_zero]

/-- The composite of the biproduct-homology isomorphism with the second projection is the second
homology projection. -/
theorem homBiprodIso_hom_snd (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    (homBiprodIso C D k).hom
        ≫ (biprod.snd : C.homology k ⊞ D.homology k ⟶ D.homology k)
      = HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) k := by
  refine homBiprodIso_hom_ext C D k ?_ ?_
  · rw [← Category.assoc, homBiprodIso_hom_inl C D k, biprod.inl_snd,
      ← HomologicalComplex.homologyMap_comp, biprod.inl_snd, HomologicalComplex.homologyMap_zero]
  · rw [← Category.assoc, homBiprodIso_hom_inr C D k, biprod.inr_snd,
      ← HomologicalComplex.homologyMap_comp, biprod.inr_snd, HomologicalComplex.homologyMap_id]

/-! ## The comparison isomorphisms on cohomology -/

variable (X : TopCat) (A U V : Set X)

/-- The comparison of the `U`-piece of the relative Mayer–Vietoris sequence with the honest
relative cochains of `U` is an isomorphism on cohomology. -/
theorem hmv_isIso_homologyMap_cmpU (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cmpU X A U V) k) := by
  haveI : IsIso (HMV.etaU A U V) := (hmv_isIso_eta X A U V).1
  haveI : IsIso (dualComplexMap ℤ (relMVUU X A U V)
      (relChains (TopCat.of U) (interAU A U)) (HMV.etaU A U V)) :=
    isIso_dualComplexMap (HMV.etaU A U V)
  haveI : IsIso (cmpU X A U V) := by
    rw [show cmpU X A U V = (relDualIsoComplex (TopCat.of U) (interAU A U)).inv
      ≫ dualComplexMap ℤ (relMVUU X A U V) (relChains (TopCat.of U) (interAU A U))
        (HMV.etaU A U V) from rfl]
    infer_instance
  exact (HomologicalComplex.homologyMapIso (asIso (cmpU X A U V)) k).isIso_hom

/-- The comparison of the `V`-piece is an isomorphism on cohomology. -/
theorem hmv_isIso_homologyMap_cmpV (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cmpV X A U V) k) := by
  haveI : IsIso (HMV.etaV A U V) := (hmv_isIso_eta X A U V).2.1
  haveI : IsIso (dualComplexMap ℤ (relMVVV X A U V)
      (relChains (TopCat.of V) (interAU A V)) (HMV.etaV A U V)) :=
    isIso_dualComplexMap (HMV.etaV A U V)
  haveI : IsIso (cmpV X A U V) := by
    rw [show cmpV X A U V = (relDualIsoComplex (TopCat.of V) (interAU A V)).inv
      ≫ dualComplexMap ℤ (relMVVV X A U V) (relChains (TopCat.of V) (interAU A V))
        (HMV.etaV A U V) from rfl]
    infer_instance
  exact (HomologicalComplex.homologyMapIso (asIso (cmpV X A U V)) k).isIso_hom

/-- The comparison of the overlap is an isomorphism on cohomology. -/
theorem hmv_isIso_homologyMap_cmpW (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cmpW X A U V) k) := by
  haveI : IsIso (relMVUVPhi X A U V) := (hmv_isIso_eta X A U V).2.2
  haveI : IsIso (dualComplexMap ℤ (relMVUV X A U V)
      (relChains (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))) (relMVUVPhi X A U V)) :=
    isIso_dualComplexMap (relMVUVPhi X A U V)
  haveI : IsIso (cmpW X A U V) := by
    rw [show cmpW X A U V = (relDualIsoComplex (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))).inv
      ≫ dualComplexMap ℤ (relMVUV X A U V)
        (relChains (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))) (relMVUVPhi X A U V) from rfl]
    infer_instance
  exact (HomologicalComplex.homologyMapIso (asIso (cmpW X A U V)) k).isIso_hom

/-- The comparison of the `U`-piece, as an isomorphism on cohomology. -/
noncomputable def cmpUIso (k : ℕ) :
    pdCohSub X A U k ≅ (relCohMVUUDual X A U V).homology k :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (cmpU X A U V) k)
    (hmv_isIso_homologyMap_cmpU X A U V k)

/-- The comparison of the `V`-piece, as an isomorphism on cohomology. -/
noncomputable def cmpVIso (k : ℕ) :
    pdCohSub X A V k ≅ (relCohMVVVDual X A U V).homology k :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (cmpV X A U V) k)
    (hmv_isIso_homologyMap_cmpV X A U V k)

/-- The comparison of the overlap, as an isomorphism on cohomology. -/
noncomputable def cmpWIso (k : ℕ) :
    pdCohSub X A (U ∩ V) k ≅ (relCohMVUVDual X A U V).homology k :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (cmpW X A U V) k)
    (hmv_isIso_homologyMap_cmpW X A U V k)

/-- The comparison of the pair `(X,A)`, as an isomorphism on cohomology. -/
noncomputable def cmpXIso (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    pdCoh X A k ≅ (relCohMVTopDual X A U V).homology k :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (cmpX X A U V) k)
    (isIso_homologyMap_cmpX X A U V hU hV hcov k)

theorem cmpUIso_hom (k : ℕ) :
    (cmpUIso X A U V k).hom = HomologicalComplex.homologyMap (cmpU X A U V) k := rfl

theorem cmpVIso_hom (k : ℕ) :
    (cmpVIso X A U V k).hom = HomologicalComplex.homologyMap (cmpV X A U V) k := rfl

theorem cmpWIso_hom (k : ℕ) :
    (cmpWIso X A U V k).hom = HomologicalComplex.homologyMap (cmpW X A U V) k := rfl

theorem cmpXIso_hom (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    (cmpXIso X A U V hU hV hcov k).hom = HomologicalComplex.homologyMap (cmpX X A U V) k := rfl

/-! ## The four naturality identities at the level of cohomology -/

/-- The transposed naturality square for the `U`-piece, at the level of cohomology. -/
theorem hmvNatU_hom (k : ℕ) :
    HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := TopCat.of U) (X₂ := X)
        (interAU A U) A (subtypeIncl X U) (fun y hy => hy)) k
      ≫ HomologicalComplex.homologyMap (cmpU X A U V) k
      = HomologicalComplex.homologyMap (cmpX X A U V) k
        ≫ HomologicalComplex.homologyMap
            (dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V) (HMV.alphaU X A U V)) k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun φ => HomologicalComplex.homologyMap φ k) (hmv_naturality_U X A U V)

/-- The transposed naturality square for the `V`-piece, at the level of cohomology. -/
theorem hmvNatV_hom (k : ℕ) :
    HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := TopCat.of V) (X₂ := X)
        (interAU A V) A (subtypeIncl X V) (fun y hy => hy)) k
      ≫ HomologicalComplex.homologyMap (cmpV X A U V) k
      = HomologicalComplex.homologyMap (cmpX X A U V) k
        ≫ HomologicalComplex.homologyMap
            (dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V) (HMV.alphaV X A U V)) k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun φ => HomologicalComplex.homologyMap φ k) (hmv_naturality_V X A U V)

/-- The transposed naturality square for the overlap, `U`-component, at the level of cohomology. -/
theorem hmvNatWU_hom (k : ℕ) :
    HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := topW X U V) (X₂ := TopCat.of U)
        (interAU A (U ∩ V)) (interAU A U) (pdIncl U (U ∩ V) Set.inter_subset_left)
        (fun y hy => hy)) k
      ≫ HomologicalComplex.homologyMap (cmpW X A U V) k
      = HomologicalComplex.homologyMap (cmpU X A U V) k
        ≫ HomologicalComplex.homologyMap
            (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)) k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun φ => HomologicalComplex.homologyMap φ k) (hmv_naturality_WU X A U V)

/-- The transposed naturality square for the overlap, `V`-component, at the level of cohomology. -/
theorem hmvNatWV_hom (k : ℕ) :
    HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := topW X U V) (X₂ := TopCat.of V)
        (interAU A (U ∩ V)) (interAU A V) (pdIncl V (U ∩ V) Set.inter_subset_right)
        (fun y hy => hy)) k
      ≫ HomologicalComplex.homologyMap (cmpW X A U V) k
      = HomologicalComplex.homologyMap (cmpV X A U V) k
        ≫ HomologicalComplex.homologyMap
            (dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)) k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun φ => HomologicalComplex.homologyMap φ k) (hmv_naturality_WV X A U V)

/-! ## The two maps of the small relative Mayer–Vietoris sequence -/

theorem hmvF_comp_fst :
    hmvF X A U V
        ≫ (biprod.fst : (relCohMVUUDual X A U V) ⊞ (relCohMVVVDual X A U V) ⟶
          relCohMVUUDual X A U V)
      = dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V) (HMV.alphaU X A U V) :=
  biprod.lift_fst _ _

theorem hmvF_comp_snd :
    hmvF X A U V
        ≫ (biprod.snd : (relCohMVUUDual X A U V) ⊞ (relCohMVVVDual X A U V) ⟶
          relCohMVVVDual X A U V)
      = dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V) (HMV.alphaV X A U V) :=
  biprod.lift_snd _ _

theorem hmvG_comp_inl :
    (biprod.inl : relCohMVUUDual X A U V ⟶
        (relCohMVUUDual X A U V) ⊞ (relCohMVVVDual X A U V)) ≫ hmvG X A U V
      = dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V) :=
  biprod.inl_desc _ _

theorem hmvG_comp_inr :
    (biprod.inr : relCohMVVVDual X A U V ⟶
        (relCohMVUUDual X A U V) ⊞ (relCohMVVVDual X A U V)) ≫ hmvG X A U V
      = -(dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)) :=
  biprod.inr_desc _ _

/-! ## The middle comparison isomorphism -/

/-- The identification of the homology of the middle biproduct of the relative small cochains with
the biproduct of the honest relative cohomologies of the two pieces. -/
noncomputable def hmvMidIso (k : ℕ) :
    ((relCohMVUUDual X A U V) ⊞ (relCohMVVVDual X A U V)).homology k
      ≅ pdCohBiprod X A U V k :=
  (homBiprodIso (relCohMVUUDual X A U V) (relCohMVVVDual X A U V) k).trans
    (biprod.mapIso (cmpUIso X A U V k) (cmpVIso X A U V k)).symm

theorem hmvMidIso_inv (k : ℕ) :
    (hmvMidIso X A U V k).inv
      = (biprod.mapIso (cmpUIso X A U V k) (cmpVIso X A U V k)).hom
        ≫ (homBiprodIso (relCohMVUUDual X A U V) (relCohMVVVDual X A U V) k).inv := by
  simp only [hmvMidIso, Iso.trans_inv, Iso.symm_inv]

/-! ## The honest relative Mayer–Vietoris sequence -/

/-- The first map of the honest relative Mayer–Vietoris sequence: the two restrictions. -/
noncomputable def honestF (k : ℕ) : pdCoh X A k ⟶ pdCohBiprod X A U V k :=
  biprod.lift (pdCohRes X A U k) (pdCohRes X A V k)

/-- The second map of the honest relative Mayer–Vietoris sequence: the difference of the two
restrictions to the overlap. -/
noncomputable def honestG (k : ℕ) : pdCohBiprod X A U V k ⟶ pdCohSub X A (U ∩ V) k :=
  biprod.desc (pdCohMap X A U (U ∩ V) Set.inter_subset_left k)
    (-(pdCohMap X A V (U ∩ V) Set.inter_subset_right k))

theorem honestF_fst (k : ℕ) :
    honestF X A U V k ≫ pdCohBiprodFst X A U V k = pdCohRes X A U k :=
  biprod.lift_fst _ _

theorem honestF_snd (k : ℕ) :
    honestF X A U V k ≫ pdCohBiprodSnd X A U V k = pdCohRes X A V k :=
  biprod.lift_snd _ _

theorem honestG_inl (k : ℕ) :
    pdCohBiprodInl X A U V k ≫ honestG X A U V k
      = pdCohMap X A U (U ∩ V) Set.inter_subset_left k :=
  biprod.inl_desc _ _

theorem honestG_inr (k : ℕ) :
    pdCohBiprodInr X A U V k ≫ honestG X A U V k
      = pdNeg (pdCohMap X A V (U ∩ V) Set.inter_subset_right k) :=
  biprod.inr_desc _ _

theorem honestF_fst' (k : ℕ) :
    honestF X A U V k
        ≫ (biprod.fst : pdCohSub X A U k ⊞ pdCohSub X A V k ⟶ pdCohSub X A U k)
      = pdCohRes X A U k :=
  biprod.lift_fst _ _

theorem honestF_snd' (k : ℕ) :
    honestF X A U V k
        ≫ (biprod.snd : pdCohSub X A U k ⊞ pdCohSub X A V k ⟶ pdCohSub X A V k)
      = pdCohRes X A V k :=
  biprod.lift_snd _ _

theorem honestG_inl' (k : ℕ) :
    (biprod.inl : pdCohSub X A U k ⟶ pdCohSub X A U k ⊞ pdCohSub X A V k) ≫ honestG X A U V k
      = pdCohMap X A U (U ∩ V) Set.inter_subset_left k :=
  biprod.inl_desc _ _

theorem honestG_inr' (k : ℕ) :
    (biprod.inr : pdCohSub X A V k ⟶ pdCohSub X A U k ⊞ pdCohSub X A V k) ≫ honestG X A U V k
      = -(pdCohMap X A V (U ∩ V) Set.inter_subset_right k) :=
  biprod.inr_desc _ _

theorem honestG_desc (k : ℕ) :
    honestG X A U V k = biprod.desc (pdCohMap X A U (U ∩ V) Set.inter_subset_left k)
      (-(pdCohMap X A V (U ∩ V) Set.inter_subset_right k)) := rfl

/-! ## The naturality squares of the comparison of the two sequences -/

/-- The naturality square of the comparison at the first map. -/
theorem honestSq₁ (k : ℕ) :
    HomologicalComplex.homologyMap (cmpX X A U V) k
        ≫ HomologicalComplex.homologyMap (hmvF X A U V) k
      = honestF X A U V k ≫ (hmvMidIso X A U V k).inv := by
  refine (cancel_mono (homBiprodIso (relCohMVUUDual X A U V) (relCohMVVVDual X A U V) k).hom).mp ?_
  rw [hmvMidIso_inv X A U V k]
  refine biprod.ext_to_iff.mpr ⟨?_, ?_⟩
  · simp only [Category.assoc]
    conv_lhs => rw [homBiprodIso_hom_fst]
    conv_lhs => rw [← HomologicalComplex.homologyMap_comp (hmvF X A U V)
      (biprod.fst : (relCohMVUUDual X A U V) ⊞ (relCohMVVVDual X A U V) ⟶
        relCohMVUUDual X A U V) k]
    conv_lhs => rw [hmvF_comp_fst X A U V]
    conv_rhs => rw [Iso.inv_hom_id_assoc]
    conv_rhs => rw [biprod.mapIso_hom]
    conv_rhs => rw [biprod.map_fst]
    conv_rhs => rw [← Category.assoc, honestF_fst' X A U V k]
    change HomologicalComplex.homologyMap (cmpX X A U V) k
        ≫ HomologicalComplex.homologyMap
            (dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V) (HMV.alphaU X A U V)) k
      = HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := TopCat.of U) (X₂ := X)
          (interAU A U) A (subtypeIncl X U) (fun y hy => hy)) k
        ≫ HomologicalComplex.homologyMap (cmpU X A U V) k
    exact (hmvNatU_hom X A U V k).symm
  · simp only [Category.assoc]
    conv_lhs => rw [homBiprodIso_hom_snd]
    conv_lhs => rw [← HomologicalComplex.homologyMap_comp (hmvF X A U V)
      (biprod.snd : (relCohMVUUDual X A U V) ⊞ (relCohMVVVDual X A U V) ⟶
        relCohMVVVDual X A U V) k]
    conv_lhs => rw [hmvF_comp_snd X A U V]
    conv_rhs => rw [Iso.inv_hom_id_assoc]
    conv_rhs => rw [biprod.mapIso_hom]
    conv_rhs => rw [biprod.map_snd]
    conv_rhs => rw [← Category.assoc, honestF_snd' X A U V k]
    change HomologicalComplex.homologyMap (cmpX X A U V) k
        ≫ HomologicalComplex.homologyMap
            (dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V) (HMV.alphaV X A U V)) k
      = HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := TopCat.of V) (X₂ := X)
          (interAU A V) A (subtypeIncl X V) (fun y hy => hy)) k
        ≫ HomologicalComplex.homologyMap (cmpV X A U V) k
    exact (hmvNatV_hom X A U V k).symm

/-- The naturality square of the comparison at the second map. -/
theorem honestSq₂ (k : ℕ) :
    (hmvMidIso X A U V k).inv ≫ HomologicalComplex.homologyMap (hmvG X A U V) k
      = honestG X A U V k ≫ (cmpWIso X A U V k).hom := by
  rw [hmvMidIso_inv X A U V k]
  refine biprod.ext_from_iff.mpr ⟨?_, ?_⟩
  · simp only [Category.assoc]
    rw [biprod.mapIso_hom, biprod.inl_map_assoc, homBiprodIso_inl_assoc,
      ← HomologicalComplex.homologyMap_comp, hmvG_comp_inl X A U V]
    rw [honestG_desc X A U V k, biprod.inl_desc_assoc]
    change HomologicalComplex.homologyMap (cmpU X A U V) k
        ≫ HomologicalComplex.homologyMap
            (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)) k
      = HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := topW X U V) (X₂ := TopCat.of U)
          (interAU A (U ∩ V)) (interAU A U) (pdIncl U (U ∩ V) Set.inter_subset_left)
          (fun y hy => hy)) k
        ≫ HomologicalComplex.homologyMap (cmpW X A U V) k
    exact (hmvNatWU_hom X A U V k).symm
  · simp only [Category.assoc]
    rw [biprod.mapIso_hom, biprod.inr_map_assoc, homBiprodIso_inr_assoc,
      ← HomologicalComplex.homologyMap_comp, hmvG_comp_inr X A U V,
      HomologicalComplex.homologyMap_neg, Preadditive.comp_neg]
    rw [honestG_desc X A U V k, biprod.inr_desc_assoc, Preadditive.neg_comp]
    change -(HomologicalComplex.homologyMap (cmpV X A U V) k
        ≫ HomologicalComplex.homologyMap
            (dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)) k)
      = -(HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := topW X U V) (X₂ := TopCat.of V)
          (interAU A (U ∩ V)) (interAU A V) (pdIncl V (U ∩ V) Set.inter_subset_right)
          (fun y hy => hy)) k
        ≫ HomologicalComplex.homologyMap (cmpW X A U V) k)
    exact congrArg (fun f => -f) (hmvNatWV_hom X A U V k).symm

/-! ## The three composites vanish -/

/-- `F k ≫ G k = 0`. -/
theorem honestFG (k : ℕ) : honestF X A U V k ≫ honestG X A U V k = 0 := by
  refine (cancel_mono (cmpWIso X A U V k).hom).mp ?_
  rw [zero_comp]
  rw [Category.assoc, ← honestSq₂ X A U V k, ← Category.assoc, ← honestSq₁ X A U V k,
    Category.assoc, ← HomologicalComplex.homologyMap_comp, hmv_comp,
    HomologicalComplex.homologyMap_zero, comp_zero]

/-- The connecting homomorphism of the honest relative Mayer–Vietoris sequence. -/
noncomputable def honestDelta (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    pdCohSub X A (U ∩ V) k ⟶ pdCoh X A (k + 1) :=
  (cmpWIso X A U V k).hom
    ≫ (hmv_shortExact X A U V).δ k (k + 1) (relCohMVUpRel k)
    ≫ (cmpXIso X A U V hU hV hcov (k + 1)).inv

/-- `G k ≫ δ k = 0`. -/
theorem honestGδ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    honestG X A U V k ≫ honestDelta X A U V hU hV hcov k = 0 := by
  have h : HomologicalComplex.homologyMap (hmvG X A U V) k
        ≫ (hmv_shortExact X A U V).δ k (k + 1) (relCohMVUpRel k)
        ≫ (cmpXIso X A U V hU hV hcov (k + 1)).inv
      = 0 ≫ (cmpXIso X A U V hU hV hcov (k + 1)).inv :=
    (hmv_shortExact X A U V).comp_δ_assoc k (k + 1) (relCohMVUpRel k)
      (cmpXIso X A U V hU hV hcov (k + 1)).inv
  rw [honestDelta, ← Category.assoc, ← honestSq₂ X A U V k, Category.assoc, h,
    zero_comp, comp_zero]

/-- `δ k ≫ F (k+1) = 0`. -/
theorem honestδF (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    honestDelta X A U V hU hV hcov k ≫ honestF X A U V (k + 1) = 0 := by
  have h : (hmv_shortExact X A U V).δ k (k + 1) (relCohMVUpRel k)
      ≫ HomologicalComplex.homologyMap (hmvF X A U V) (k + 1) = 0 :=
    (hmv_shortExact X A U V).δ_comp k (k + 1) (relCohMVUpRel k)
  refine (cancel_mono (hmvMidIso X A U V (k + 1)).inv).mp ?_
  rw [zero_comp]
  rw [Category.assoc, ← honestSq₁ X A U V (k + 1)]
  rw [honestDelta, Category.assoc, Category.assoc]
  change (cmpWIso X A U V k).hom
      ≫ ((hmv_shortExact X A U V).δ k (k + 1) (relCohMVUpRel k)
        ≫ ((cmpXIso X A U V hU hV hcov (k + 1)).inv
          ≫ ((cmpXIso X A U V hU hV hcov (k + 1)).hom
            ≫ HomologicalComplex.homologyMap (hmvF X A U V) (k + 1)))) = 0
  rw [Iso.inv_hom_id_assoc, h, comp_zero]

/-! ## The short complexes of the two sequences -/

/-- The degreewise part of the homology sequence of the small relative Mayer–Vietoris sequence. -/
noncomputable def hmvHomSC₂ (k : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (hmvF X A U V) k)
    (HomologicalComplex.homologyMap (hmvG X A U V) k)
    (by rw [← HomologicalComplex.homologyMap_comp, hmv_comp,
      HomologicalComplex.homologyMap_zero])

/-- The second short complex of the homology sequence. -/
noncomputable def hmvHomSC₃ (k : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (hmvG X A U V) k)
    ((hmv_shortExact X A U V).δ k (k + 1) (relCohMVUpRel k))
    ((hmv_shortExact X A U V).comp_δ k (k + 1) (relCohMVUpRel k))

/-- The third short complex of the homology sequence. -/
noncomputable def hmvHomSC₁ (k : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk ((hmv_shortExact X A U V).δ k (k + 1) (relCohMVUpRel k))
    (HomologicalComplex.homologyMap (hmvF X A U V) (k + 1))
    ((hmv_shortExact X A U V).δ_comp k (k + 1) (relCohMVUpRel k))

/-- The first short complex of the honest sequence. -/
noncomputable def honestSC₂ (k : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (honestF X A U V k) (honestG X A U V k) (honestFG X A U V k)

/-- The second short complex of the honest sequence. -/
noncomputable def honestSC₃ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (honestG X A U V k) (honestDelta X A U V hU hV hcov k)
    (honestGδ X A U V hU hV hcov k)

/-- The third short complex of the honest sequence. -/
noncomputable def honestSC₁ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (honestDelta X A U V hU hV hcov k) (honestF X A U V (k + 1))
    (honestδF X A U V hU hV hcov k)

/-! ## Comparison isomorphisms of the short complexes -/

/-- The comparison isomorphism at the first two terms. -/
noncomputable def honestIso₂ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    honestSC₂ X A U V k ≅ hmvHomSC₂ X A U V k :=
  ShortComplex.isoMk (cmpXIso X A U V hU hV hcov k) (hmvMidIso X A U V k).symm
    (cmpWIso X A U V k) (honestSq₁ X A U V k) (honestSq₂ X A U V k)

/-- The last square of the comparison, involving the connecting homomorphism. -/
theorem honestDeltaSq (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    (cmpWIso X A U V k).hom ≫ (hmv_shortExact X A U V).δ k (k + 1) (relCohMVUpRel k)
      = honestDelta X A U V hU hV hcov k ≫ (cmpXIso X A U V hU hV hcov (k + 1)).hom := by
  rw [honestDelta, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The comparison isomorphism at the last two terms. -/
noncomputable def honestIso₃ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    honestSC₃ X A U V hU hV hcov k ≅ hmvHomSC₃ X A U V k :=
  ShortComplex.isoMk (hmvMidIso X A U V k).symm (cmpWIso X A U V k)
    (cmpXIso X A U V hU hV hcov (k + 1)) (honestSq₂ X A U V k)
    (honestDeltaSq X A U V hU hV hcov k)

/-- The comparison isomorphism at the first and last terms. -/
noncomputable def honestIso₁ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    honestSC₁ X A U V hU hV hcov k ≅ hmvHomSC₁ X A U V k :=
  ShortComplex.isoMk (cmpWIso X A U V k) (cmpXIso X A U V hU hV hcov (k + 1))
    (hmvMidIso X A U V (k + 1)).symm (honestDeltaSq X A U V hU hV hcov k)
    (honestSq₁ X A U V (k + 1))

/-! ## Exactness -/

/-- Exactness at the middle term. -/
theorem honest_exact₂ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    (honestSC₂ X A U V k).Exact :=
  ShortComplex.exact_of_iso (honestIso₂ X A U V hU hV hcov k).symm
    ((hmv_shortExact X A U V).homology_exact₂ k)

/-- Exactness at the third term. -/
theorem honest_exact₃ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    (honestSC₃ X A U V hU hV hcov k).Exact :=
  ShortComplex.exact_of_iso (honestIso₃ X A U V hU hV hcov k).symm
    ((hmv_shortExact X A U V).homology_exact₃ k (k + 1) (relCohMVUpRel k))

/-- Exactness at the first term. -/
theorem honest_exact₁ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    (honestSC₁ X A U V hU hV hcov k).Exact :=
  ShortComplex.exact_of_iso (honestIso₁ X A U V hU hV hcov k).symm
    ((hmv_shortExact X A U V).homology_exact₁ k (k + 1) (relCohMVUpRel k))

end

end Work.Cohomology

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-- **The honest relative Mayer–Vietoris long exact sequence.** -/
theorem relCohMV_honest_les (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    ∃ (F : ∀ k, Work.Cohomology.pdMor (Work.Cohomology.pdCoh X A k)
          (Work.Cohomology.pdCohBiprod X A U V k))
      (G : ∀ k, Work.Cohomology.pdMor (Work.Cohomology.pdCohBiprod X A U V k)
          (Work.Cohomology.pdCohSub X A (U ∩ V) k))
      (δ : ∀ k, Work.Cohomology.pdMor (Work.Cohomology.pdCohSub X A (U ∩ V) k)
          (Work.Cohomology.pdCoh X A (k + 1)))
      (hFG : ∀ k, Work.Cohomology.pdComp (F k) (G k) = Work.Cohomology.pdZero _ _)
      (hGδ : ∀ k, Work.Cohomology.pdComp (G k) (δ k) = Work.Cohomology.pdZero _ _)
      (hδF : ∀ k, Work.Cohomology.pdComp (δ k) (F (k + 1)) = Work.Cohomology.pdZero _ _),
      (∀ k, Work.Cohomology.pdComp (F k) (Work.Cohomology.pdCohBiprodFst X A U V k)
        = Work.Cohomology.pdCohRes X A U k) ∧
      (∀ k, Work.Cohomology.pdComp (F k) (Work.Cohomology.pdCohBiprodSnd X A U V k)
        = Work.Cohomology.pdCohRes X A V k) ∧
      (∀ k, Work.Cohomology.pdComp (Work.Cohomology.pdCohBiprodInl X A U V k) (G k)
        = Work.Cohomology.pdCohMap X A U (U ∩ V) Set.inter_subset_left k) ∧
      (∀ k, Work.Cohomology.pdComp (Work.Cohomology.pdCohBiprodInr X A U V k) (G k)
        = Work.Cohomology.pdNeg (Work.Cohomology.pdCohMap X A V (U ∩ V) Set.inter_subset_right k)) ∧
      (∀ k, Work.Cohomology.pdExact (F k) (G k) (hFG k)) ∧
      (∀ k, Work.Cohomology.pdExact (G k) (δ k) (hGδ k)) ∧
      (∀ k, Work.Cohomology.pdExact (δ k) (F (k + 1)) (hδF k)) := by
  refine ⟨honestF X A U V, honestG X A U V, honestDelta X A U V hU hV hcov,
    honestFG X A U V, honestGδ X A U V hU hV hcov, honestδF X A U V hU hV hcov, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro k; exact honestF_fst X A U V k
  · intro k; exact honestF_snd X A U V k
  · intro k; exact honestG_inl X A U V k
  · intro k; exact honestG_inr X A U V k
  · intro k; exact honest_exact₂ X A U V hU hV hcov k
  · intro k; exact honest_exact₃ X A U V hU hV hcov k
  · intro k; exact honest_exact₁ X A U V hU hV hcov k

end

end Work.Cohomology
