import Mathlib
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.thomClass_of_cover_gen
import Submission.Work.Thom.nonempty_thomClass_of_compatible_local
import Submission.Work.Thom.transgressionSameSpace
import Submission.Work.Thom.transgressionNatural
import Submission.Work.Thom.transgressionPiAux
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Thom.localThomUnionAux
import Submission.Work.Thom.luThomGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Work.TangentClasses
open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

open Work.Thom (relCohMap relPb relToAbs mixedCupC Coh CohMap CohMap_comp CohMap_id pdCohIso subtypeMap)

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- The piece of `↥(W ∪ U)` over `W`. -/
abbrev luP₀ (W U : Set B) : Set ↥(W ∪ U) := (Subtype.val : ↥(W ∪ U) → B) ⁻¹' W

/-- The piece of `↥(W ∪ U)` over `U`. -/
abbrev luQ₀ (W U : Set B) : Set ↥(W ∪ U) := (Subtype.val : ↥(W ∪ U) → B) ⁻¹' U

/-- The piece of the total space over `W`. -/
abbrev luPW (Z : RealBundle B F ι) (W U : Set B) : Set ↥(Z.proj ⁻¹' (W ∪ U)) :=
  (Subtype.val : ↥(Z.proj ⁻¹' (W ∪ U)) → Z.TotalSpace) ⁻¹' (Z.proj ⁻¹' W)

/-- The piece of the total space over `U`. -/
abbrev luPU (Z : RealBundle B F ι) (W U : Set B) : Set ↥(Z.proj ⁻¹' (W ∪ U)) :=
  (Subtype.val : ↥(Z.proj ⁻¹' (W ∪ U)) → Z.TotalSpace) ⁻¹' (Z.proj ⁻¹' U)

/-- The piece of the total space over `W ∩ U`. -/
abbrev luPI (Z : RealBundle B F ι) (W U : Set B) : Set ↥(Z.proj ⁻¹' (W ∪ U)) :=
  luPW Z W U ∩ luPU Z W U

/-- The zero-complement inside the total space over `W ∪ U`. -/
abbrev luPA (Z : RealBundle B F ι) (W U : Set B) : Set ↥(Z.proj ⁻¹' (W ∪ U)) :=
  (Subtype.val : ↥(Z.proj ⁻¹' (W ∪ U)) → Z.TotalSpace) ⁻¹' (Work.Thom.zeroComplement Z)

/-- `Subsingleton` transfers along an isomorphism of `ℤ`-modules. -/
theorem subsingleton_of_iso_lu {M N : ModuleCat ℤ} (e : M ≅ N) (h : Subsingleton M) :
    Subsingleton N := by
  obtain ⟨-, hs⟩ := CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom
  exact ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    rw [Subsingleton.elim x y]⟩

/-- The pullback along a homeomorphism is bijective. -/
theorem bijective_CohMap_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ) : Function.Bijective (CohMap (e : C(X, Y)) ℤ k).hom := by
  have h1 : CohMap (e.symm : C(Y, X)) ℤ k ≫ CohMap (e : C(X, Y)) ℤ k = 𝟙 (Coh ℤ k X) := by
    rw [← CohMap_comp (e : C(X, Y)) (e.symm : C(Y, X))]
    have hc : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
      ext x; exact e.symm_apply_apply x
    rw [hc, CohMap_id]
  have h2 : CohMap (e : C(X, Y)) ℤ k ≫ CohMap (e.symm : C(Y, X)) ℤ k = 𝟙 (Coh ℤ k Y) := by
    rw [← CohMap_comp (e.symm : C(Y, X)) (e : C(X, Y))]
    have hc : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
      ext x; exact e.apply_symm_apply x
    rw [hc, CohMap_id]
  have hl1 : (CohMap (e.symm : C(Y, X)) ℤ k).hom.comp (CohMap (e : C(X, Y)) ℤ k).hom
      = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom h2
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  have hl2 : (CohMap (e : C(X, Y)) ℤ k).hom.comp (CohMap (e.symm : C(Y, X)) ℤ k).hom
      = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom h1
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  constructor
  · intro a b hab
    have ha := LinearMap.congr_fun hl1 a
    have hb := LinearMap.congr_fun hl1 b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [hab] at ha
    exact ha.symm.trans hb
  · intro b
    exact ⟨(CohMap (e.symm : C(Y, X)) ℤ k).hom b, LinearMap.congr_fun hl2 b⟩

end Work.Cohomology

namespace Work.Thom

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The transfer of the piece cup map along the base homeomorphism.** -/
theorem luCupMap_transfer (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ)
    {S W : Set B} (hWS : W ⊆ S) (cW : PieceCoh Z W n)
    (hcW : ∀ j, Function.Bijective (localThomMap Z n W cW j)) :
    ∀ k, Function.Bijective (Work.Cohomology.luCupMap (X := ↥S) (Y := ↥(Z.proj ⁻¹' S))
      (pieceProj Z S) ((Subtype.val : ↥(Z.proj ⁻¹' S) → Z.TotalSpace) ⁻¹' (zeroComplement Z)) n
      (U := (Subtype.val : ↥S → B) ⁻¹' W)
      ((Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Set.preimage_mono hWS) n).hom cW) k) := by
  set eB : ↥W ≃ₜ ↥((Subtype.val : ↥S → B) ⁻¹' W) := Work.Cohomology.luSubHomeo (X := B)
    (Set.preimage_mono hWS) with heB
  set eT : ↥((Subtype.val : ↥(Z.proj ⁻¹' S) → Z.TotalSpace) ⁻¹' (Z.proj ⁻¹' W)) ≃ₜ ↥(Z.proj ⁻¹' W) :=
    (Work.Cohomology.luSubHomeo (X := Z.TotalSpace) (Set.preimage_mono hWS)).symm with heT
  set A := Work.Cohomology.interAU (X := TopCat.of Z.TotalSpace) (zeroComplement Z)
    (Z.proj ⁻¹' W) with hA
  set B' := Work.Cohomology.interAU (X := TopCat.of (↥(Z.proj ⁻¹' S)))
    ((Subtype.val : ↥(Z.proj ⁻¹' S) → Z.TotalSpace) ⁻¹' (zeroComplement Z))
    ((Subtype.val : ↥(Z.proj ⁻¹' S) → Z.TotalSpace) ⁻¹' (Z.proj ⁻¹' W)) with hB'
  have hLHS : ∀ j, Function.Bijective (fun x : Coh ℤ j ↥((Subtype.val : ↥S → B) ⁻¹' W) =>
      (mixedCupC ℤ A j n) ((CohMap ((eB : C(↥W, ↥((Subtype.val : ↥S → B) ⁻¹' W))).comp
        (pieceProj Z W)) ℤ j).hom x) cW) := by
    intro j
    have h1 : Function.Bijective (fun x : Coh ℤ j ↥W =>
        (mixedCupC ℤ A j n) ((CohMap (pieceProj Z W) ℤ j).hom x) cW) := hcW j
    have h2 : Function.Bijective ((CohMap (eB : C(↥W, ↥((Subtype.val : ↥S → B) ⁻¹' W)))
        ℤ j).hom) := Work.Cohomology.bijective_CohMap_homeomorph eB j
    have h3 : (fun x : Coh ℤ j ↥((Subtype.val : ↥S → B) ⁻¹' W) =>
        (mixedCupC ℤ A j n) ((CohMap ((eB : C(↥W, ↥((Subtype.val : ↥S → B) ⁻¹' W))).comp
          (pieceProj Z W)) ℤ j).hom x) cW)
        = (fun x : Coh ℤ j ↥W => (mixedCupC ℤ A j n) ((CohMap (pieceProj Z W) ℤ j).hom x) cW)
          ∘ (CohMap (eB : C(↥W, ↥((Subtype.val : ↥S → B) ⁻¹' W))) ℤ j).hom := by
      funext x
      rw [Function.comp_apply, CohMap_comp]
      rfl
    rw [h3]
    exact h1.comp h2
  have key := Work.Thom.cupMap_transfer_iffA
    (X := ↥(Z.proj ⁻¹' W))
    (Y := ↥((Subtype.val : ↥(Z.proj ⁻¹' S) → Z.TotalSpace) ⁻¹' (Z.proj ⁻¹' W)))
    (Z := ↥((Subtype.val : ↥S → B) ⁻¹' W))
    (eT : C(↥((Subtype.val : ↥(Z.proj ⁻¹' S) → Z.TotalSpace) ⁻¹' (Z.proj ⁻¹' W)), ↥(Z.proj ⁻¹' W)))
    A B' (fun y hy => hy)
    (fun m => Work.Thom.bijective_relCohMap_of_homeomorphA _ _ eT
      (fun y => ⟨fun hy => hy, fun hy => hy⟩) ℤ m)
    ((eB : C(↥W, ↥((Subtype.val : ↥S → B) ⁻¹' W))).comp (pieceProj Z W))
    (Work.Cohomology.luFPiece (X := ↥S) (Y := ↥(Z.proj ⁻¹' S)) (pieceProj Z S)
      ((Subtype.val : ↥S → B) ⁻¹' W))
    (by ext y; rfl)
    n cW
  intro j
  exact key.mp hLHS j

theorem localThom_union
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    {W U : Set B} (hW : IsOpen W) (hU : IsOpen U)
    (cW : Work.Thom.PieceCoh Z W n)
    (hcW : ∀ j, Function.Bijective (Work.Thom.localThomMap Z n W cW j))
    (cU : Work.Thom.PieceCoh Z U n)
    (hcU : ∀ j, Function.Bijective (Work.Thom.localThomMap Z n U cU j))
    (cI : Work.Thom.PieceCoh Z (W ∩ U) n)
    (hcI : ∀ j, Function.Bijective (Work.Thom.localThomMap Z n (W ∩ U) cI j))
    (h1 : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' W) (Z.proj ⁻¹' (W ∩ U)) (Set.preimage_mono Set.inter_subset_left) n).hom cW
        = cI)
    (h2 : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' (W ∩ U)) (Set.preimage_mono Set.inter_subset_right) n).hom cU
        = cI)
    (hlow : Subsingleton (Work.Thom.PieceCoh Z (W ∩ U) (n - 1))) :
    ∃ c : Work.Thom.PieceCoh Z (W ∪ U) n,
      (∀ j, Function.Bijective (Work.Thom.localThomMap Z n (W ∪ U) c j)) ∧
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (W ∪ U)) (Z.proj ⁻¹' W) (Set.preimage_mono Set.subset_union_left) n).hom c
        = cW ∧
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (W ∪ U)) (Z.proj ⁻¹' U) (Set.preimage_mono Set.subset_union_right) n).hom c
        = cU := by
  classical
  have hPW : Z.proj ⁻¹' W ⊆ Z.proj ⁻¹' (W ∪ U) := Set.preimage_mono Set.subset_union_left
  have hQU : Z.proj ⁻¹' U ⊆ Z.proj ⁻¹' (W ∪ U) := Set.preimage_mono Set.subset_union_right
  have hIWs : Z.proj ⁻¹' (W ∩ U) ⊆ Z.proj ⁻¹' (W ∪ U) :=
    Set.preimage_mono (fun x hx => Or.inl hx.1)
  have hIW : Z.proj ⁻¹' (W ∩ U) ⊆ Z.proj ⁻¹' W := Set.preimage_mono Set.inter_subset_left
  have hIU : Z.proj ⁻¹' (W ∩ U) ⊆ Z.proj ⁻¹' U := Set.preimage_mono Set.inter_subset_right
  -- openness of the four pieces
  have hP₀open : IsOpen (Work.Cohomology.luP₀ W U) := hW.preimage continuous_subtype_val
  have hQ₀open : IsOpen (Work.Cohomology.luQ₀ W U) := hU.preimage continuous_subtype_val
  have hPopen : IsOpen (Work.Cohomology.luPW Z W U) :=
    (hW.preimage Z.continuous_proj).preimage continuous_subtype_val
  have hQopen : IsOpen (Work.Cohomology.luPU Z W U) :=
    (hU.preimage Z.continuous_proj).preimage continuous_subtype_val
  have hcov₀ : Work.Cohomology.luP₀ W U ∪ Work.Cohomology.luQ₀ W U = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases x.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcov : Work.Cohomology.luPW Z W U ∪ Work.Cohomology.luPU Z W U = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases x.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- the transported piece classes
  set cW' : Work.Cohomology.pdCohSub (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPW Z W U) n :=
    (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hPW n).hom cW with hcW'
  set cU' : Work.Cohomology.pdCohSub (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPU Z W U) n :=
    (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hQU n).hom cU with hcU'
  set cI' : Work.Cohomology.pdCohSub (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPI Z W U) n :=
    (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hIWs n).hom cI with hcI'
  -- the restriction of `cW'` to the overlap
  have hcW'_res : (Work.Cohomology.pdCohMap (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPW Z W U)
      (Work.Cohomology.luPI Z W U) (Set.preimage_mono (Set.preimage_mono Set.inter_subset_left)) n).hom cW' = cI' := by
    have h0 := congrArg ModuleCat.Hom.hom (Work.Cohomology.luHom_natural
      (TopCat.of Z.TotalSpace) (zeroComplement Z) hPW hIWs hIW n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h0
    have h := LinearMap.congr_fun h0 cW
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    erw [hcW', hcI', Work.Cohomology.luIso_hom, Work.Cohomology.luIso_hom, h, h1]
  -- the restriction of `cU'` to the overlap
  have hcU'_res : (Work.Cohomology.pdCohMap (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPU Z W U)
      (Work.Cohomology.luPI Z W U) (Set.preimage_mono (Set.preimage_mono Set.inter_subset_right)) n).hom cU' = cI' := by
    have h0 := congrArg ModuleCat.Hom.hom (Work.Cohomology.luHom_natural
      (TopCat.of Z.TotalSpace) (zeroComplement Z) hQU hIWs hIU n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h0
    have h := LinearMap.congr_fun h0 cU
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    erw [hcU', hcI', Work.Cohomology.luIso_hom, Work.Cohomology.luIso_hom, h, h2]
  -- compatibility of `cW'` and `cU'` on the overlap
  have hcompat : (Work.Cohomology.pdCohMap (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPW Z W U)
      (Work.Cohomology.luPW Z W U ∩ Work.Cohomology.luPU Z W U) Set.inter_subset_left n).hom cW'
      = (Work.Cohomology.pdCohMap (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
        (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPU Z W U)
        (Work.Cohomology.luPW Z W U ∩ Work.Cohomology.luPU Z W U) Set.inter_subset_right n).hom cU' :=
    hcW'_res.trans hcU'_res.symm
  -- the low-degree vanishing on the overlap
  have hlow' : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPI Z W U) (n - 1)) :=
    Work.Cohomology.subsingleton_of_iso_lu
      (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hIWs (n - 1)) hlow
  -- the glueing
  obtain ⟨c, hPc₀, hQc₀⟩ := Work.Cohomology.lu_exists_glue (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
    (Work.Cohomology.luPA Z W U) n hPopen hQopen hcov cW' cU' hcompat
  have hPc : (Work.Cohomology.pdCohRes (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPW Z W U) n).hom c = cW' := hPc₀
  have hQc : (Work.Cohomology.pdCohRes (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPU Z W U) n).hom c = cU' := hQc₀
  -- the restriction of the glued class to the overlap
  have hUVc : (Work.Thom.TsqH.relRestrOvl (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
      (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPW Z W U)
      (Work.Cohomology.luPU Z W U) n).hom c = cI' := by
    have h0 := congrArg ModuleCat.Hom.hom (Work.Cohomology.pdCohRes_comp
      (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U))) (Work.Cohomology.luPA Z W U)
      (Work.Cohomology.luPW Z W U) (Work.Cohomology.luPI Z W U)
      (Set.preimage_mono (Set.preimage_mono Set.inter_subset_left)) n)
    rw [ModuleCat.hom_comp] at h0
    have h := LinearMap.congr_fun h0 c
    rw [LinearMap.comp_apply] at h
    erw [show (Work.Thom.TsqH.relRestrOvl (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
        (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPW Z W U)
        (Work.Cohomology.luPU Z W U) n)
        = Work.Cohomology.pdCohRes (TopCat.of ↥(Z.proj ⁻¹' (W ∪ U)))
          (Work.Cohomology.luPA Z W U) (Work.Cohomology.luPI Z W U) n from rfl, h, hPc]
    exact hcW'_res
  -- the general ladder (proved in `Submission/Work/Thom/luThomGen.lean`)
  have hgen : ∀ k, Function.Bijective (fun x : Coh ℤ k ↥(W ∪ U) =>
      (mixedCupC ℤ (Work.Cohomology.luPA Z W U) k n)
        ((CohMap (pieceProj Z (W ∪ U)) ℤ k).hom x) c) := by
    exact Work.Thom.luThomGen (X := ↥(W ∪ U)) (Y := ↥(Z.proj ⁻¹' (W ∪ U)))
      (pieceProj Z (W ∪ U)) (Work.Cohomology.luPA Z W U) n hn
      hP₀open hQ₀open hcov₀ c cW'
      (Work.Thom.luCupMap_transfer Z n (S := W ∪ U) (W := W) Set.subset_union_left cW hcW)
      cU'
      (Work.Thom.luCupMap_transfer Z n (S := W ∪ U) (W := U) Set.subset_union_right cU hcU)
      cI'
      (Work.Thom.luCupMap_transfer Z n (S := W ∪ U) (W := W ∩ U)
        (fun x hx => Or.inl hx.1) cI hcI)
      hPc hQc hUVc hlow'
  -- the restriction of the glued class
  have hresW : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
      (Z.proj ⁻¹' (W ∪ U)) (Z.proj ⁻¹' W) (Set.preimage_mono Set.subset_union_left) n).hom c
      = cW := by
    have h0 := congrArg ModuleCat.Hom.hom (Work.Cohomology.luIso_res (TopCat.of Z.TotalSpace)
      (zeroComplement Z) hPW n)
    rw [ModuleCat.hom_comp] at h0
    have h := LinearMap.congr_fun h0 c
    rw [LinearMap.comp_apply] at h
    have h2 : (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hPW n).hom
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' (W ∪ U)) (Z.proj ⁻¹' W) (Set.preimage_mono Set.subset_union_left) n).hom c)
        = (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hPW n).hom cW := by
      erw [h, hPc, hcW']
    exact (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hPW n).hom).1 h2
  have hresU : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
      (Z.proj ⁻¹' (W ∪ U)) (Z.proj ⁻¹' U) (Set.preimage_mono Set.subset_union_right) n).hom c
      = cU := by
    have h0 := congrArg ModuleCat.Hom.hom (Work.Cohomology.luIso_res (TopCat.of Z.TotalSpace)
      (zeroComplement Z) hQU n)
    rw [ModuleCat.hom_comp] at h0
    have h := LinearMap.congr_fun h0 c
    rw [LinearMap.comp_apply] at h
    have h2 : (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hQU n).hom
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' (W ∪ U)) (Z.proj ⁻¹' U) (Set.preimage_mono Set.subset_union_right) n).hom c)
        = (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hQU n).hom cU := by
      erw [h, hQc, hcU']
    exact (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (Work.Cohomology.luIso (TopCat.of Z.TotalSpace) (zeroComplement Z) hQU n).hom).1 h2
  exact ⟨c, hgen, hresW, hresU⟩

end Work.Thom
