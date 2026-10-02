import Mathlib
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.LerayHirsch.MvAux.HonestDegree
import Submission.Work.LerayHirsch.MvAux.Ladder
import Submission.Work.Thom.luThomGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [-instance] AddCommGroup.toIntModule

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section
variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## Cast bookkeeping -/

theorem eqToHom_self {C : Type*} [Category C] {X : C} (h : X = X) : eqToHom h = 𝟙 X := by
  rw [Subsingleton.elim h rfl, eqToHom_refl]

theorem pdCast_self (X : TopCat) (A : Set X) {k : ℕ} (h : k = k) : pdCast X A h = 𝟙 _ := by
  rw [pdCast]; exact eqToHom_self _

theorem pdSubCast_self (X : TopCat) (A U : Set X) {k : ℕ} (h : k = k) : pdSubCast X A U h = 𝟙 _ := by
  rw [pdSubCast]; exact eqToHom_self _

theorem pdCohMap_pdSubCast (X : TopCat) (A : Set X) (P W : Set X) (hPW : W ⊆ P) {k l : ℕ}
    (h : k = l) :
    pdSubCast X A P h ≫ pdCohMap X A P W hPW l
      = pdCohMap X A P W hPW k ≫ pdSubCast X A W h := by
  subst h
  simp only [pdSubCast, eqToHom_refl, Category.comp_id, Category.id_comp]

/-! ## Elementwise versions of the single-class squares -/

theorem luF_comp_applyAux {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) {P : Set X}
    (cP : pdCohSub (TopCat.of Y) A (π ⁻¹' P) n)
    (hcP : (pdCohRes (TopCat.of Y) A (π ⁻¹' P) n).hom c = cP) (k : ℕ)
    (a : ↑(pdCoh (TopCat.of X) (∅ : Set X) k)) :
    (luTU π A n cP k).hom ((pdCohRes (TopCat.of X) (∅ : Set X) P k).hom a)
      = (pdCohRes (TopCat.of Y) A (π ⁻¹' P) (k + n)).hom ((luTM π A n c k).hom a) := by
  have h := congrArg (fun (φ : pdCoh (TopCat.of X) (∅ : Set X) k ⟶
      pdCohSub (TopCat.of Y) A (π ⁻¹' P) (k + n)) => (ModuleCat.Hom.hom φ) a)
    (luF_comp π A n c cP hcP k)
  exact h

theorem luF_comp_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) {P : Set X} (k : ℕ)
    (a : ↑(pdCoh (TopCat.of X) (∅ : Set X) k)) :
    (luTU π A n ((pdCohRes (TopCat.of Y) A (π ⁻¹' P) n).hom c) k).hom
        ((pdCohRes (TopCat.of X) (∅ : Set X) P k).hom a)
      = (pdCohRes (TopCat.of Y) A (π ⁻¹' P) (k + n)).hom ((luTM π A n c k).hom a) :=
  luF_comp_applyAux π A n c ((pdCohRes (TopCat.of Y) A (π ⁻¹' P) n).hom c) rfl k a

/-! ## The `F`-square -/

/-- The `i`-th component of `MvTM`, restricted to the piece, is the `i`-th component of `MvTU`. -/
theorem MvCM_res_eq_MvCU (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U : Set B) (k : ℕ) (i : lhIdx m k)
    (a : ↑(pdCoh (TopCat.of B) (∅ : Set B) (k - 2 * (i : ℕ)))) :
    (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k).hom
        ((MvCM Z k i).hom a)
      = (MvCU Z U k i).hom
          ((pdCohRes (TopCat.of B) (∅ : Set B) U (k - 2 * (i : ℕ))).hom a) := by
  rw [show (MvCM Z k i).hom a
      = (pdCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((luTM (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRel Z i)
          (k - 2 * (i : ℕ))).hom a) from rfl]
  rw [← MvAux.pdCohRes_pdCast_apply]
  rw [show (MvCU Z U k i).hom ((pdCohRes (TopCat.of B) (∅ : Set B) U (k - 2*(i:ℕ))).hom a)
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z U i)
          (k - 2 * (i : ℕ))).hom
          ((pdCohRes (TopCat.of B) (∅ : Set B) U (k - 2 * (i : ℕ))).hom a)) from rfl]
  exact congrArg (fun w => (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U) (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom w)
    (luF_comp_applyAux (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRel Z i)
      (zetaRelPiece Z U i) rfl (k - 2 * (i : ℕ)) a).symm

/-- The first component of `MvTP` applied to an element of the `P`-term. -/
theorem MvTP_fst_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) (y : ↑(MvP B m k U V)) :
    (ModuleCat.Hom.hom (biprod.fst : pdCohBiprod (TopCat.of (ProjSpace Z))
        (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k ⟶
          pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k))
        ((MvTP Z U V k).hom y)
      = (MvTU Z U k).hom
          ((ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U)) y) := by
  rw [MvTP_def]
  have h := congrArg (fun (φ : MvP B m k U V ⟶ pdCohSub (TopCat.of (ProjSpace Z))
      (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k) => (ModuleCat.Hom.hom φ) y)
    (biprod.map_fst (MvTU Z U k) (MvTV Z V k))
  exact h

/-- The second component of `MvTP` applied to an element of the `P`-term. -/
theorem MvTP_snd_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) (y : ↑(MvP B m k U V)) :
    (ModuleCat.Hom.hom (biprod.snd : pdCohBiprod (TopCat.of (ProjSpace Z))
        (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k ⟶
          pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k))
        ((MvTP Z U V k).hom y)
      = (MvTV Z V k).hom
          ((ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V)) y) := by
  rw [MvTP_def]
  have h := congrArg (fun (φ : MvP B m k U V ⟶ pdCohSub (TopCat.of (ProjSpace Z))
      (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k) => (ModuleCat.Hom.hom φ) y)
    (biprod.map_snd (MvTU Z U k) (MvTV Z V k))
  exact h

/-- The first component of `MvF₂`. -/
theorem MvF₂_fst_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ)
    (y : ↑(pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k)) :
    (ModuleCat.Hom.hom (biprod.fst :
        pdCohBiprod (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
          (projMap Z ⁻¹' V) k ⟶ pdCohSub (TopCat.of (ProjSpace Z))
            (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k))
        ((MvF₂ Z U V k).hom y)
      = (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k).hom y := by
  have h := congrArg (fun (φ : pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k) =>
        (ModuleCat.Hom.hom φ) y)
    (honestF_fst' (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k)
  exact h

/-- The second component of `MvF₂`. -/
theorem MvF₂_snd_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ)
    (y : ↑(pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k)) :
    (ModuleCat.Hom.hom (biprod.snd :
        pdCohBiprod (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
          (projMap Z ⁻¹' V) k ⟶ pdCohSub (TopCat.of (ProjSpace Z))
            (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k))
        ((MvF₂ Z U V k).hom y)
      = (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k).hom y := by
  have h := congrArg (fun (φ : pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k) =>
        (ModuleCat.Hom.hom φ) y)
    (honestF_snd' (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k)
  exact h

/-- **The `M`-component of the `F`-square**: restricting `MvTM` to the piece over `U`. -/
theorem MvTM_res_U (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U : Set B) (k : ℕ) (x : ↑(MvM B m k)) :
    (MvTU Z U k).hom ((MvRes B m k U).hom x)
      = (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k).hom
          ((MvTM Z k).hom x) := by
  rw [MvTU_apply, MvTM_apply]
  rw [show (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k).hom
        (∑ i : lhIdx m k, (MvCM Z k i).hom (x i))
      = ∑ i : lhIdx m k, (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U) k).hom ((MvCM Z k i).hom (x i))
      from map_sum _ _ Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MvRes_apply]
  exact (MvCM_res_eq_MvCU Z U k i (x i)).symm

/-- **The `M`-component of the `F`-square**: restricting `MvTM` to the piece over `V`. -/
theorem MvTM_res_V (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (V : Set B) (k : ℕ) (x : ↑(MvM B m k)) :
    (MvTV Z V k).hom ((MvRes B m k V).hom x)
      = (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k).hom
          ((MvTM Z k).hom x) := by
  rw [MvTV_apply, MvTM_apply]
  rw [show (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k).hom
        (∑ i : lhIdx m k, (MvCM Z k i).hom (x i))
      = ∑ i : lhIdx m k, (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' V) k).hom ((MvCM Z k i).hom (x i))
      from map_sum _ _ Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MvRes_apply]
  exact (MvCM_res_eq_MvCU Z V k i (x i)).symm

/-- **The first square of the ladder.** -/
theorem MvF_square (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {U V : Set B} (k : ℕ) :
    MvF (B := B) m k U V ≫ MvTP Z U V k = MvTM Z k ≫ MvF₂ Z U V k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  rw [MvAux.eq_biprodPair_fst_snd ((MvTP Z U V k).hom ((MvF (B := B) m k U V).hom x)),
      MvAux.eq_biprodPair_fst_snd ((MvF₂ Z U V k).hom ((MvTM Z k).hom x))]
  congr 1
  · rw [MvTP_fst_apply, MvF₂_fst_apply]
    rw [show (ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U))
          ((MvF (B := B) m k U V).hom x) = (MvRes B m k U).hom x from by
      rw [← ModuleCat.comp_apply (MvF (B := B) m k U V) (biprod.fst) x, MvF_fst]]
    exact MvTM_res_U Z U k x
  · rw [MvTP_snd_apply, MvF₂_snd_apply]
    rw [show (ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V))
          ((MvF (B := B) m k U V).hom x) = (MvRes B m k V).hom x from by
      rw [← ModuleCat.comp_apply (MvF (B := B) m k U V) (biprod.snd) x, MvF_snd]]
    exact MvTM_res_V Z V k x

/-! ## The `G`-square -/

theorem luG_comp_applyAux {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {U V P : Set X} (hPV : U ∩ V ⊆ P)
    (cP : pdCohSub (TopCat.of Y) A (π ⁻¹' P) n)
    (hcP : (pdCohRes (TopCat.of Y) A (π ⁻¹' P) n).hom c = cP)
    (cUV : pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n)
    (hcUV : (pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c = cUV) (k : ℕ)
    (a : ↑(pdCohSub (TopCat.of X) (∅ : Set X) P k)) :
    (pdCohMap (TopCat.of Y) A (π ⁻¹' P) (π ⁻¹' U ∩ π ⁻¹' V)
        (fun _ hx => hPV ⟨hx.1, hx.2⟩) (k + n)).hom ((luTU π A n cP k).hom a)
      = (luTQ π A n cUV k).hom
          ((pdCohMap (TopCat.of X) (∅ : Set X) P (U ∩ V) hPV k).hom a) := by
  have h := congrArg (fun (φ : pdCohSub (TopCat.of X) (∅ : Set X) P k ⟶
      pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) (k + n)) => (ModuleCat.Hom.hom φ) a)
    (luG_comp π A n c hPV cP hcP cUV hcUV k)
  exact h.symm

theorem luG_comp_apply_left {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) {U V : Set X} (k : ℕ)
    (a : ↑(pdCohSub (TopCat.of X) (∅ : Set X) U k)) :
    (pdCohMap (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' U ∩ π ⁻¹' V)
        Set.inter_subset_left (k + n)).hom
      ((luTU π A n ((pdCohRes (TopCat.of Y) A (π ⁻¹' U) n).hom c) k).hom a)
      = (luTQ π A n ((pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c) k).hom
          ((pdCohMap (TopCat.of X) (∅ : Set X) U (U ∩ V) Set.inter_subset_left k).hom a) :=
  luG_comp_applyAux π A n c Set.inter_subset_left _ rfl _ rfl k a

theorem luG_comp_apply_right {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) {U V : Set X} (k : ℕ)
    (a : ↑(pdCohSub (TopCat.of X) (∅ : Set X) V k)) :
    (pdCohMap (TopCat.of Y) A (π ⁻¹' V) (π ⁻¹' U ∩ π ⁻¹' V)
        Set.inter_subset_right (k + n)).hom
      ((luTU π A n ((pdCohRes (TopCat.of Y) A (π ⁻¹' V) n).hom c) k).hom a)
      = (luTQ π A n ((pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c) k).hom
          ((pdCohMap (TopCat.of X) (∅ : Set X) V (U ∩ V) Set.inter_subset_right k).hom a) :=
  luG_comp_applyAux π A n c Set.inter_subset_right _ rfl _ rfl k a

/-- Pointwise addition in the `Q`-term. -/
theorem MvQ_add_apply (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B)
    (a b : ↑(MvQ B m k U V)) (i : lhIdx m k) : (a + b) i = a i + b i := rfl

/-- Pointwise negation in the `Q`-term. -/
theorem MvQ_neg_apply (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B)
    (a : ↑(MvQ B m k U V)) (i : lhIdx m k) : (-a) i = -(a i) := rfl

/-- The component formula for `MvG`. -/
theorem MvG_apply (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B)
    (w : ↑(MvP B m k U V)) :
    MvG (B := B) m k U V w
      = (fun i : lhIdx m k =>
          (pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left
              (k - 2 * (i : ℕ))).hom
            ((ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U)) w i)
          - (pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right
              (k - 2 * (i : ℕ))).hom
            ((ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V)) w i)) := by
  rw [show MvG (B := B) m k U V = biprod.desc (MvResOvlU B m k U V) (-(MvResOvlV B m k U V))
      from rfl, MvAux.biprod_desc_apply]
  funext i
  rw [MvQ_add_apply]
  rw [ModuleCat.hom_neg, LinearMap.neg_apply, MvQ_neg_apply, MvResOvlU_apply, MvResOvlV_apply]
  rw [sub_eq_add_neg]


/-- The component formula for `MvG₂`. -/
theorem MvG₂_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ)
    (z : ↑(pdCohBiprod (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k)) :
    (MvG₂ Z U V k).hom z
      = (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_left k).hom
          ((ModuleCat.Hom.hom (biprod.fst : pdCohBiprod (TopCat.of (ProjSpace Z))
            (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k ⟶
              pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k)) z)
        - (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_right k).hom
          ((ModuleCat.Hom.hom (biprod.snd : pdCohBiprod (TopCat.of (ProjSpace Z))
            (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k ⟶
              pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k)) z) := by
  change (honestG (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k).hom z = _
  rw [MvAux.eq_biprodPair_fst_snd z, MvAux.honestG_apply_pair, MvAux.biprodPair_fst,
    MvAux.biprodPair_snd]

/-- **The individual `MvCU` restricted to the overlap is `MvCQ`.** -/
theorem MvC_ovl_U (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) (i : lhIdx m k)
    (u : ↑(pdCohSub (TopCat.of B) (∅ : Set B) U (k - 2 * (i : ℕ)))) :
    (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_left k).hom ((MvCU Z U k i).hom u)
      = (MvCQ Z U V k i).hom
          ((pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left
            (k - 2 * (i : ℕ))).hom u) := by
  rw [show (MvCU Z U k i).hom u
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z U i)
          (k - 2 * (i : ℕ))).hom u) from rfl]
  rw [show (MvCQ Z U V k i).hom
        ((pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left
          (k - 2 * (i : ℕ))).hom u)
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((luTQ (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelOvl Z U V i)
          (k - 2 * (i : ℕ))).hom
          ((pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left
            (k - 2 * (i : ℕ))).hom u)) from rfl]
  rw [show (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_left k).hom
        ((pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
          ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z U i)
            (k - 2 * (i : ℕ))).hom u))
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_left
          (k - 2 * (i : ℕ) + 2 * (i : ℕ))).hom
          ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z U i)
            (k - 2 * (i : ℕ))).hom u))
      from congrArg (fun (φ : pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
            (projMap Z ⁻¹' U) (k - 2 * (i : ℕ) + 2 * (i : ℕ)) ⟶
              pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
                (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k) =>
          (ModuleCat.Hom.hom φ)
            ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z U i)
              (k - 2 * (i : ℕ))).hom u))
        (pdCohMap_pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_left
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k))]
  exact congrArg (fun w => (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom w)
    (luG_comp_apply_left (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRel Z i)
      (k - 2 * (i : ℕ)) u)

/-- **The individual `MvCV` restricted to the overlap is `MvCQ`.** -/
theorem MvC_ovl_V (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) (i : lhIdx m k)
    (v : ↑(pdCohSub (TopCat.of B) (∅ : Set B) V (k - 2 * (i : ℕ)))) :
    (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_right k).hom ((MvCV Z V k i).hom v)
      = (MvCQ Z U V k i).hom
          ((pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right
            (k - 2 * (i : ℕ))).hom v) := by
  rw [show (MvCV Z V k i).hom v
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z V i)
          (k - 2 * (i : ℕ))).hom v) from rfl]
  rw [show (MvCQ Z U V k i).hom
        ((pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right
          (k - 2 * (i : ℕ))).hom v)
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((luTQ (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelOvl Z U V i)
          (k - 2 * (i : ℕ))).hom
          ((pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right
            (k - 2 * (i : ℕ))).hom v)) from rfl]
  rw [show (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_right k).hom
        ((pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
          ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z V i)
            (k - 2 * (i : ℕ))).hom v))
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_right
          (k - 2 * (i : ℕ) + 2 * (i : ℕ))).hom
          ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z V i)
            (k - 2 * (i : ℕ))).hom v))
      from congrArg (fun (φ : pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
            (projMap Z ⁻¹' V) (k - 2 * (i : ℕ) + 2 * (i : ℕ)) ⟶
              pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
                (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k) =>
          (ModuleCat.Hom.hom φ)
            ((luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z V i)
              (k - 2 * (i : ℕ))).hom v))
        (pdCohMap_pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_right
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k))]
  exact congrArg (fun w => (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom w)
    (luG_comp_apply_right (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRel Z i)
      (k - 2 * (i : ℕ)) v)

/-- **The second square of the ladder.** -/
theorem MvG_square (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {U V : Set B} (k : ℕ) :
    MvG (B := B) m k U V ≫ MvTQ Z U V k = MvTP Z U V k ≫ MvG₂ Z U V k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  rw [MvTQ_apply]
  have hsum : (∑ i : lhIdx m k,
        (MvCQ Z U V k i).hom ((MvG (B := B) m k U V w) i))
      = ∑ i : lhIdx m k,
          ((MvCQ Z U V k i).hom
              ((pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left
                (k - 2 * (i : ℕ))).hom
                ((ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U)) w i))
            - (MvCQ Z U V k i).hom
              ((pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right
                (k - 2 * (i : ℕ))).hom
                ((ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V)) w i))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MvG_apply, map_sub]
  rw [hsum, Finset.sum_sub_distrib]
  rw [MvG₂_apply, MvTP_fst_apply, MvTP_snd_apply, MvTU_apply, MvTV_apply]
  rw [show (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_left k).hom
        (∑ i : lhIdx m k, (MvCU Z U k i).hom
          ((ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U)) w i))
      = ∑ i : lhIdx m k,
          (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
            (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_left k).hom
          ((MvCU Z U k i).hom
            ((ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U)) w i))
      from map_sum _ _ Finset.univ]
  rw [show (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_right k).hom
        (∑ i : lhIdx m k, (MvCV Z V k i).hom
          ((ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V)) w i))
      = ∑ i : lhIdx m k,
          (pdCohMap (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
            (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) Set.inter_subset_right k).hom
          ((MvCV Z V k i).hom
            ((ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V)) w i))
      from map_sum _ _ Finset.univ]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (MvC_ovl_U Z U V k i
      ((ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U)) w i)).symm
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (MvC_ovl_V Z U V k i
      ((ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V)) w i)).symm

/-! ## The `D`-square: cast bookkeeping -/

theorem pdCast_trans (X : TopCat) (A : Set X) {k l mm : ℕ} (p : k = l) (q : l = mm) :
    pdCast X A p ≫ pdCast X A q = pdCast X A (p.trans q) := by
  subst p; subst q
  simp [pdCast_self]

theorem pdCast_trans_apply (X : TopCat) (A : Set X) {k l mm : ℕ} (p : k = l) (q : l = mm)
    (x : ↑(pdCoh X A k)) :
    (pdCast X A q).hom ((pdCast X A p).hom x) = (pdCast X A (p.trans q)).hom x := by
  rw [← ModuleCat.comp_apply, pdCast_trans]

theorem pdSubCast_trans_apply (X : TopCat) (A U : Set X) {k l mm : ℕ} (p : k = l) (q : l = mm)
    (x : ↑(pdCohSub X A U k)) :
    (pdSubCast X A U q).hom ((pdSubCast X A U p).hom x) = (pdSubCast X A U (p.trans q)).hom x := by
  subst p; subst q
  simp [pdSubCast_self]

/-- The degree cast commutes with `luTM`. -/
theorem luTM_pdCast {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) {k k' : ℕ} (h : k = k')
    (a : ↑(pdCoh (TopCat.of X) (∅ : Set X) k)) :
    (luTM π A n c k').hom ((pdCast (TopCat.of X) (∅ : Set X) h).hom a)
      = (pdCast (TopCat.of Y) A (congrArg (fun t => t + n) h)).hom ((luTM π A n c k).hom a) := by
  subst h
  rw [pdCast_self, pdCast_self]
  simp

/-- The degree cast commutes with `honestDelta`. -/
theorem honestDelta_pdSubCast {X : TopCat} (A : Set X) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) {k k' : ℕ} (h : k = k')
    (y : ↑(pdCohSub X A (U ∩ V) k)) :
    (honestDelta X A U V hU hV hcov k').hom ((pdSubCast X A (U ∩ V) h).hom y)
      = (pdCast X A (congrArg (fun t => t + 1) h)).hom ((honestDelta X A U V hU hV hcov k).hom y) := by
  subst h
  rw [pdSubCast_self, pdCast_self]
  simp

/-- The transgression square of `Work.Thom.luDelta_square`, elementwise. -/
theorem luDelta_square_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) {U V : Set X}
    (cUV : pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n)
    (hcUV : (pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c = cUV)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (y : ↑(pdCohSub (TopCat.of X) (∅ : Set X) (U ∩ V) k)) :
    (luTM π A n c (k + 1)).hom
        ((honestDelta (TopCat.of X) (∅ : Set X) U V hU hV hcov k).hom y)
      = (eqToHom (congrArg (fun mm => pdCoh (TopCat.of Y) A mm)
            (by omega : k + n + 1 = (k + 1) + n))).hom
          ((honestDelta (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (hU.preimage π.continuous)
            (hV.preimage π.continuous)
            (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) (k + n)).hom
            ((luTQ π A n cUV k).hom y)) := by
  have h := congrArg (fun (φ : pdCohSub (TopCat.of X) (∅ : Set X) (U ∩ V) k ⟶
      pdCoh (TopCat.of Y) A ((k + 1) + n)) => (ModuleCat.Hom.hom φ) y)
    (luDelta_square π A n c cUV hcUV hU hV hcov k)
  exact h

/-- The `i`-th summand of the comparison map `MvCM`, unfolded. -/
theorem MvCM_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : lhIdx m k) (a : ↑(pdCoh (TopCat.of B) (∅ : Set B) (k - 2 * (i : ℕ)))) :
    (MvCM Z k i).hom a
      = (pdCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((luTM (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRel Z i)
          (k - 2 * (i : ℕ))).hom a) := rfl

/-- The `i`-th summand of the comparison map `MvCQ`, unfolded. -/
theorem MvCQ_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) (i : lhIdx m k)
    (a : ↑(pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) (k - 2 * (i : ℕ)))) :
    (MvCQ Z U V k i).hom a
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V)
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        ((luTQ (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelOvl Z U V i)
          (k - 2 * (i : ℕ))).hom a) := rfl


/-- Proof irrelevance for the degree cast on elements. -/
theorem pdCast_apply_congr' (X : TopCat) (A : Set X) {k l : ℕ} (p q : k = l)
    {z : ↑(pdCoh X A k)} : (pdCast X A p).hom z = (pdCast X A q).hom z :=
  MvAux.pdCast_apply_congr X A p q z

/-- The transgression square for the powers of `ζ`, in the shape used by the ladder. -/
theorem luDelta_square_zeta (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (j : lhIdx m (k + 1))
    (y : ↑(pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) (k - 2 * (j : ℕ)))) :
    (luTM (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (j : ℕ)) (zetaRel Z j)
        ((k - 2 * (j : ℕ)) + 1)).hom
        ((honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov (k - 2 * (j : ℕ))).hom y)
      = (pdCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (by omega : k - 2 * (j : ℕ) + 2 * (j : ℕ) + 1
            = ((k - 2 * (j : ℕ)) + 1) + 2 * (j : ℕ))).hom
          ((honestDelta (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
            (projMap Z ⁻¹' U) (projMap Z ⁻¹' V)
            (hU.preimage (projMap Z).continuous) (hV.preimage (projMap Z).continuous)
            (by rw [← Set.preimage_union, hcov, Set.preimage_univ])
            (k - 2 * (j : ℕ) + 2 * (j : ℕ))).hom
            ((luTQ (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (j : ℕ)) (zetaRelOvl Z U V j)
              (k - 2 * (j : ℕ))).hom y)) :=
  luDelta_square_apply (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (j : ℕ)) (zetaRel Z j)
    (zetaRelOvl Z U V j) rfl hU hV hcov (k - 2 * (j : ℕ)) y

/-- The connecting map `MvDeltaTwo` of the ladder, unfolded. -/
theorem MvDeltaTwo_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (y : ↑(pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k)) :
    (MvDeltaTwo Z hU hV hcov k).hom y
      = (honestDelta (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U) (projMap Z ⁻¹' V)
          (hU.preimage (projMap Z).continuous) (hV.preimage (projMap Z).continuous)
          (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) k).hom y := rfl

/-- The `i`-th component of `MvCM` followed by `MvD` is `honestDelta` followed by `MvCQ`. -/
theorem MvD_comp (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (i : lhIdx m k) (c : ↑(MvQ B m k U V)) :
    (MvCM Z (k + 1) (MvAux.lhIdxSucc i)).hom
        ((MvD B m k U V hU hV hcov).hom c (MvAux.lhIdxSucc i))
      = (honestDelta (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U) (projMap Z ⁻¹' V)
          (hU.preimage (projMap Z).continuous) (hV.preimage (projMap Z).continuous)
          (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) k).hom
          ((MvCQ Z U V k i).hom (c i)) := by
  rw [MvAux.MvD_apply_of_le hU hV hcov k c (MvAux.lhIdxSucc i) i.2
    (by rw [MvAux.lhIdxSucc_val]; omega)]
  rw [show c (⟨(MvAux.lhIdxSucc i).1, i.2⟩ : lhIdx m k) = c i from rfl]
  rw [MvCM_eq]
  rw [luTM_pdCast]
  rw [luDelta_square_zeta Z U V hU hV hcov k (MvAux.lhIdxSucc i) (c i)]
  rw [MvCQ_eq]
  rw [honestDelta_pdSubCast]
  rw [pdCast_trans_apply]
  rw [pdCast_trans_apply]
  exact pdCast_apply_congr' _ _ _ _

/-- Reindexing the sum in the `D`-square. -/
theorem MvD_sum_reindex (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (c : ↑(MvQ B m k U V)) :
    (∑ J : lhIdx m (k + 1),
        (MvCM Z (k + 1) J).hom ((MvD B m k U V hU hV hcov).hom c J))
      = ∑ i : lhIdx m k, (MvCM Z (k + 1) (MvAux.lhIdxSucc i)).hom
          ((MvD B m k U V hU hV hcov).hom c (MvAux.lhIdxSucc i)) := by
  have hzero : ∀ J : lhIdx m (k + 1), ¬ 2 * (J : ℕ) ≤ k →
      (MvCM Z (k + 1) J).hom ((MvD B m k U V hU hV hcov).hom c J) = 0 := by
    intro J hJ
    rw [MvAux.MvD_apply_of_gt hU hV hcov k c J hJ, map_zero]
  have hfilt : (Finset.univ : Finset (lhIdx m (k + 1))).sum
        (fun J => (MvCM Z (k + 1) J).hom ((MvD B m k U V hU hV hcov).hom c J))
      = ((Finset.univ : Finset (lhIdx m (k + 1))).filter
          (fun J : lhIdx m (k + 1) => 2 * (J : ℕ) ≤ k)).sum
        (fun J => (MvCM Z (k + 1) J).hom ((MvD B m k U V hU hV hcov).hom c J)) := by
    symm
    exact Finset.sum_filter_of_ne (fun J _ hJ => by
      by_contra hp
      exact hJ (hzero J hp))
  rw [hfilt]
  refine (Finset.sum_bij (fun (a : lhIdx m k) (_ : a ∈ Finset.univ) => MvAux.lhIdxSucc a)
    ?_ ?_ ?_ ?_).symm
  · intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact a.2
  · intro a₁ _ a₂ _ h
    exact Subtype.ext (congrArg (fun z : lhIdx m (k + 1) => (z : Fin m)) h)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b.1, hb⟩, Finset.mem_univ _, Subtype.ext rfl⟩
  · intro a _
    rfl

/-- **The third square of the ladder.** -/
theorem MvD_square (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∀ k : ℕ, MvD (B := B) m k U V hU hV hcov ≫ MvTM Z (k + 1)
      = MvTQ Z U V k ≫ MvDeltaTwo Z hU hV hcov k := by
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  rw [MvTM_apply, MvTQ_apply]
  rw [MvDeltaTwo_apply]
  rw [show (honestDelta (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U) (projMap Z ⁻¹' V)
        (hU.preimage (projMap Z).continuous) (hV.preimage (projMap Z).continuous)
        (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) k).hom
        (∑ i : lhIdx m k, (MvCQ Z U V k i).hom (c i))
      = ∑ i : lhIdx m k,
          (honestDelta (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
            (projMap Z ⁻¹' U) (projMap Z ⁻¹' V)
            (hU.preimage (projMap Z).continuous) (hV.preimage (projMap Z).continuous)
            (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) k).hom
            ((MvCQ Z U V k i).hom (c i))
      from map_sum _ _ Finset.univ]
  rw [MvD_sum_reindex Z U V hU hV hcov k c]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact MvD_comp Z U V hU hV hcov k i c

end

end Work.LerayHirsch
