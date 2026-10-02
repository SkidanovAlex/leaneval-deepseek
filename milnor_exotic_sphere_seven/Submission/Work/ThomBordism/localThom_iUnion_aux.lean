import Mathlib
import Submission.Work.Thom.localThom_full
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.Thom.subsingleton_PieceCoh_of_lt_finrank
import Submission.Work.ThomBordism.chainSetup_cone
import Submission.Work.ThomBordism.coneCyclicPos_of_inj_surj
import Submission.Work.ThomBordism.coneCyclicZero_of_inj_surj
import Submission.Work.ThomBordism.Tower.ConeTheory
import Submission.Work.ThomBordism.Tower.BaseTheory
import Submission.Work.ThomBordism.iUnion.extra
import Submission.Work.Cohomology.rcKern_iUnion_limit
import Submission.Work.Cohomology.rcResLM_surjective
import Submission.Work.Thom.Coh_zero_cover_injective_gen
import Submission.Work.Thom.localThomMap_pdCohMap
import Submission.Work.Thom.thomClass_of_cover
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.pd_split_crux
import Submission.Work.ThomBordism.iUnion.psiInterface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# `Work.ThomBordism.localThom_iUnion_of_fibreGenerator`

The union/limit step of the Leray–Hirsch direction: if a class `σ ∈ H^n(X, X∖0)` (with `n = finrank ℝ F`)
restricts, over every member `W` of a chain `C` of open sets, to a *local Thom class* over `W`, then
it is a local Thom class over the union `U = ⋃₀ C`.

## Plan

The proof is a *degree induction* on the (augmented) mapping cone of the cochain-level Thom map
`ψ = psiAbs`, using Zorn's lemma:

* the pieces `W ∈ C` have exact cone complexes (this is `coneData_of_localThomMap`, the cohomological
  dictionary, applied to the hypothesis of the statement);
* every subfamily `D ⊆ C` has exact cone complex (here `⋃₀ D ⊆ U`): the Zorn argument glues
  primitives of a fixed cycle; the correction step at a new piece `W` needs the exactness one degree
  *below* (which is the induction hypothesis) together with the surjectivity of the restriction of
  cochains;
* the bottom of the induction (the `Extra` term, i.e. the injectivity of `ψ⁰`) is the one place where
  the *low-degree vanishing* `PieceCoh Z V (n-1) = 0` is used, which follows from `n = finrank ℝ F`
  (`Work.Thom.subsingleton_PieceCoh_of_lt_finrank`);
* finally the exactness over `U` is translated back into the bijectivity of `localThomMap`
  (`localThomMap_bijective_of_coneData`).

This file contains the infrastructure (gluing/separation of compatible families of cochains over an
increasing family indexed by an arbitrary linear order) and the proof.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The limit of a compatible family of cochains, for an arbitrary linear order

`Work.Cohomology.rcKern_iUnion_limit` carries an unused `WellFoundedLT J` hypothesis (it is never
used in the proof); the Zorn arguments below need the general form. -/

theorem rcKern_iUnion_limit_lin {X : Type} [TopologicalSpace X] (A : Set X) {J : Type}
    [LinearOrder J] (W : J → Set X) (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k)) :
    (∃! g : ↥(rcKern A (⋃ j, W j) k), ∀ j, rcResLM A (Set.subset_iUnion W j) k g = f j)
      ↔ (∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i) := by
  constructor
  · rintro ⟨g, hg, -⟩ i j hij
    have h1 : rcResLM A (hmono hij) k (f j)
        = rcResLM A ((hmono hij).trans (Set.subset_iUnion W j)) k g := by
      rw [← hg j, ← LinearMap.comp_apply,
        rcResLM_comp A (hmono hij) (Set.subset_iUnion W j) k]
    rw [h1, rcResLM_proof_irrel ((hmono hij).trans (Set.subset_iUnion W j))
      (Set.subset_iUnion W i) k]
    exact hg i
  · intro hf
    refine ⟨⟨rcGlueCochain A W hopen hmono k f hf, rcGlueCochain_mem A W hopen hmono k f hf⟩,
      ?_, ?_⟩
    · intro j
      exact rcGlueCochain_restrict A W hopen hmono k f hf j
    · intro y hy
      rw [← sub_eq_zero]
      apply rcRestrict_injective A W hopen hmono k
      intro j
      rw [map_sub, hy j, rcGlueCochain_restrict A W hopen hmono k f hf j, sub_self]

/-- A compatible family of relative cochains over an increasing family is the family of
restrictions of a unique cochain: existence form. -/
theorem rcKern_iUnion_limit_exists {X : Type} [TopologicalSpace X] (A : Set X) {J : Type}
    [LinearOrder J] (W : J → Set X) (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i) :
    ∃ g : ↥(rcKern A (⋃ j, W j) k), ∀ j, rcResLM A (Set.subset_iUnion W j) k g = f j :=
  ((rcKern_iUnion_limit_lin A W hopen hmono k f).mpr hf).exists

/-- Separation of relative cochains over an increasing family: a cochain over the union vanishing on
every piece vanishes. -/
theorem rcKern_iUnion_sep {X : Type} [TopologicalSpace X] (A : Set X) {J : Type} [LinearOrder J]
    (W : J → Set X) (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    {x : ↥(rcKern A (⋃ j, W j) k)}
    (h : ∀ j, rcResLM A (Set.subset_iUnion W j) k x = 0) : x = 0 := by
  have hf : ∀ i j (hij : i ≤ j),
      rcResLM A (hmono hij) k (rcResLM A (Set.subset_iUnion W j) k x)
        = rcResLM A (Set.subset_iUnion W i) k x := by
    intro i j hij
    rw [← LinearMap.comp_apply, rcResLM_comp A (hmono hij) (Set.subset_iUnion W j) k,
      Subsingleton.elim ((hmono hij).trans (Set.subset_iUnion W j)) (Set.subset_iUnion W i)]
  obtain ⟨g, -, huniq⟩ := (rcKern_iUnion_limit_lin A W hopen hmono k
    (fun j => rcResLM A (Set.subset_iUnion W j) k x)).mpr hf
  have hx : x = g := huniq x (fun j => rfl)
  have h0 : (0 : ↥(rcKern A (⋃ j, W j) k)) = g :=
    huniq 0 (fun j => by rw [map_zero]; exact (h j).symm)
  rw [hx, ← h0]

/-- Gluing of a compatible family of absolute cochains over an increasing family indexed by an
arbitrary linear order (`Work.ThomBordism.baseGlue` is the `ℕ`-indexed case). -/
theorem baseGlue_lin {J : Type} [LinearOrder J] (V : J → Set B)
    (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ) (f : (j : J) → BaseC (V j) k)
    (hf : ∀ i j (hij : i ≤ j), baseRes (hmono hij) k (f j) = f i) :
    ∃! g : BaseC (⋃ j, V j) k, ∀ j, baseRes (Set.subset_iUnion V j) k g = f j := by
  have hf' : ∀ i j (hij : i ≤ j),
      rcResLM (∅ : Set B) (hmono hij) k (toAbs (V j) k (f j)) = toAbs (V i) k (f i) := by
    intro i j hij
    apply Subtype.ext
    show (rcResLM (∅ : Set B) (hmono hij) k (toAbs (V j) k (f j))).1 = f i
    rw [← baseRes_eq (hmono hij) k (f j)]
    exact hf i j hij
  obtain ⟨g', hg', hguniq⟩ := (rcKern_iUnion_limit_lin (∅ : Set B) V hopen hmono k
    (fun j => toAbs (V j) k (f j))).mpr hf'
  refine ⟨ofAbs g', ?_, ?_⟩
  · intro j
    rw [baseRes_eq (Set.subset_iUnion V j) k (ofAbs g')]
    change (rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k (ofAbs g'))).1 = f j
    rw [toAbs_ofAbs]
    exact congrArg Subtype.val (hg' j)
  · intro y hy
    have hy' : ∀ j, rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k y)
        = toAbs (V j) k (f j) := by
      intro j
      apply Subtype.ext
      show (rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k y)).1 = f j
      rw [← baseRes_eq (Set.subset_iUnion V j) k y]
      exact hy j
    have huniq : toAbs (⋃ j, V j) k y = g' := hguniq _ hy'
    rw [← huniq]
    rfl

/-- Separation of absolute cochains over an increasing family. -/
theorem baseRes_sep_lin {J : Type} [LinearOrder J] (V : J → Set B)
    (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ)
    {x : BaseC (⋃ j, V j) k}
    (h : ∀ j, baseRes (Set.subset_iUnion V j) k x = 0) : x = 0 := by
  have hf : ∀ i j (hij : i ≤ j),
      baseRes (hmono hij) k (baseRes (Set.subset_iUnion V j) k x)
        = baseRes (Set.subset_iUnion V i) k x := by
    intro i j hij
    rw [← LinearMap.comp_apply, baseRes_comp,
      Subsingleton.elim ((hmono hij).trans (Set.subset_iUnion V j)) (Set.subset_iUnion V i)]
  obtain ⟨g, -, huniq⟩ := baseGlue_lin V hopen hmono k
    (fun j => baseRes (Set.subset_iUnion V j) k x) hf
  have hx : x = g := huniq x (fun j => rfl)
  have h0 : (0 : BaseC (⋃ j, V j) k) = g :=
    huniq 0 (fun j => by rw [map_zero]; exact (h j).symm)
  rw [hx, ← h0]

/-- Gluing of a compatible family of relative cochains of the Thom pair over an increasing family
indexed by an arbitrary linear order. -/
theorem totGlue_lin (Z : RealBundle B F ι) {J : Type} [LinearOrder J] (V : J → Set B)
    (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ)
    (f : (j : J) → TotC Z (V j) k)
    (hf : ∀ i j (hij : i ≤ j),
      rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (hmono hij)) k (f j) = f i) :
    ∃! g : TotC Z (⋃ j, V j) k,
      ∀ j, rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion V j)) k g
        = f j := by
  have hopenV : ∀ j, IsOpen (Z.proj ⁻¹' V j) :=
    fun j => (hopen j).preimage (RealBundle.continuous_proj Z)
  have hmonoV : Monotone (fun j => Z.proj ⁻¹' V j) :=
    fun a b hab => Set.preimage_mono (hmono hab)
  obtain ⟨g0, hg0, huniq⟩ := (rcKern_iUnion_limit_lin (Work.Thom.zeroComplement Z)
    (fun j => Z.proj ⁻¹' V j) hopenV hmonoV k f).mpr hf
  have hEU : Z.proj ⁻¹' (⋃ j, V j) ⊆ ⋃ j, Z.proj ⁻¹' V j := by
    intro x hx
    rw [Set.mem_preimage] at hx
    rw [Set.mem_iUnion] at hx ⊢
    exact hx
  have hUE : (⋃ j, Z.proj ⁻¹' V j) ⊆ Z.proj ⁻¹' (⋃ j, V j) := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    rw [Set.mem_preimage]
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  refine ⟨rcResLM (Work.Thom.zeroComplement Z) hEU k g0, ?_, ?_⟩
  · intro j
    have hcomp := DFunLike.congr_fun (rcResLM_comp (Work.Thom.zeroComplement Z)
      (Set.preimage_mono (Set.subset_iUnion V j)) hEU k) g0
    rw [LinearMap.comp_apply] at hcomp
    rw [hcomp]
    rw [rcResLM_proof_irrel _ (Set.subset_iUnion (fun m => Z.proj ⁻¹' V m) j) k]
    exact hg0 j
  · intro y hy
    have hy' : ∀ j, rcResLM (Work.Thom.zeroComplement Z)
        (Set.subset_iUnion (fun m => Z.proj ⁻¹' V m) j) k
        (rcResLM (Work.Thom.zeroComplement Z) hUE k y) = f j := by
      intro j
      have hcomp := DFunLike.congr_fun (rcResLM_comp (Work.Thom.zeroComplement Z)
        (Set.subset_iUnion (fun m => Z.proj ⁻¹' V m) j) hUE k) y
      rw [LinearMap.comp_apply] at hcomp
      rw [hcomp]
      rw [rcResLM_proof_irrel _ (Set.preimage_mono (Set.subset_iUnion V j)) k]
      exact hy j
    have h1 : rcResLM (Work.Thom.zeroComplement Z) hUE k y = g0 := huniq _ hy'
    have h2 : rcResLM (Work.Thom.zeroComplement Z) hEU k
        (rcResLM (Work.Thom.zeroComplement Z) hUE k y) = y := by
      have hcomp := DFunLike.congr_fun (rcResLM_comp (Work.Thom.zeroComplement Z) hEU hUE k) y
      rw [LinearMap.comp_apply] at hcomp
      rw [hcomp]
      exact rcResLM_self (Work.Thom.zeroComplement Z) (hEU.trans hUE) k y
    rw [← h2, h1]

/-- Separation of the relative cochains of the Thom pair over an increasing family. -/
theorem totRes_sep_lin (Z : RealBundle B F ι) {J : Type} [LinearOrder J] (V : J → Set B)
    (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ)
    {x : TotC Z (⋃ j, V j) k}
    (h : ∀ j, rcResLM (Work.Thom.zeroComplement Z)
      (Set.preimage_mono (Set.subset_iUnion V j)) k x = 0) : x = 0 := by
  have hf : ∀ i j (hij : i ≤ j),
      rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (hmono hij)) k
          (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion V j)) k x)
        = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion V i)) k x := by
    intro i j hij
    rw [← LinearMap.comp_apply,
      rcResLM_comp (Work.Thom.zeroComplement Z) (Set.preimage_mono (hmono hij))
        (Set.preimage_mono (Set.subset_iUnion V j)) k,
      Subsingleton.elim ((Set.preimage_mono (hmono hij)).trans
        (Set.preimage_mono (Set.subset_iUnion V j))) (Set.preimage_mono (Set.subset_iUnion V i))]
  obtain ⟨g, -, huniq⟩ := totGlue_lin Z V hopen hmono k
    (fun j => rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion V j)) k x) hf
  have hx : x = g := huniq x (fun j => rfl)
  have h0 : (0 : TotC Z (⋃ j, V j) k) = g :=
    huniq 0 (fun j => by rw [map_zero]; exact (h j).symm)
  rw [hx, ← h0]

end

end Work.ThomBordism



namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The class / coboundary dictionary

Two cycles of a cochain complex of `ℤ`-modules have the same class if and only if they differ by a
coboundary (`Work.Cohomology.pd_cochain_homologyπ_eq_zero_iff_d` + linearity of `homologyπ`), and a
cycle has vanishing class if and only if it is a coboundary.  These are the translations between the
cohomological statements (the hypothesis of the target) and the cochain-level statements (the cone
complexes) used below. -/

/-- Two cycles of a cochain complex of `ℤ`-modules have the same class iff they differ by a
coboundary. -/
theorem cochain_homologyπ_eq_iff_sub {C : CochainComplex (ModuleCat ℤ) ℕ}
    [∀ i, C.HasHomology i] (k : ℕ) (z z' : C.cycles (k+1)) :
    C.homologyπ (k+1) z = C.homologyπ (k+1) z' ↔
      ∃ w : C.X k, (C.d k (k+1)).hom w
        = (HomologicalComplex.iCycles C (k+1)).hom (z - z') := by
  have h1 : (C.homologyπ (k+1) z = C.homologyπ (k+1) z') ↔
      (ConcreteCategory.hom (C.homologyπ (k+1))) (z - z') = 0 := by
    constructor
    · intro h
      rw [map_sub (ConcreteCategory.hom (C.homologyπ (k+1))), h, sub_self]
    · intro h
      have h2 : (ConcreteCategory.hom (C.homologyπ (k+1))) z
          - (ConcreteCategory.hom (C.homologyπ (k+1))) z' = 0 := by
        rw [← map_sub (ConcreteCategory.hom (C.homologyπ (k+1)))]
        exact h
      exact sub_eq_zero.mp h2
  rw [h1]
  exact pd_cochain_homologyπ_eq_zero_iff_d (C := C) k (z - z')

/-- A cycle of a cochain complex of `ℤ`-modules has vanishing class iff it is a coboundary. -/
theorem cochain_homologyπ_eq_zero_iff {C : CochainComplex (ModuleCat ℤ) ℕ}
    [∀ i, C.HasHomology i] (k : ℕ) (z : C.cycles (k+1)) :
    C.homologyπ (k+1) z = 0 ↔
      ∃ w : C.X k, (C.d k (k+1)).hom w = (HomologicalComplex.iCycles C (k+1)).hom z :=
  pd_cochain_homologyπ_eq_zero_iff_d (C := C) k z

section Concrete

variable (Z : RealBundle B F ι)

/-- The class of a relative cocycle, as the homology class of the associated cycle (the definition,
as a rewriting lemma). -/
theorem relClassOf_eq_homologyπ' (W : Set B) (k : ℕ) (z : TotC Z W k)
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) k z = 0) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
      = ((relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).homologyπ k)
          (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz) := rfl

/-- The differential of the relative complex of the piece over `W` is `relDiffLM`. -/
theorem relComplex_d_apply (W : Set B) (k : ℕ) (w : TotC Z W k) :
    (ConcreteCategory.hom ((relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).d k (k+1))) w
      = relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) k w := by
  rw [relComplex_d]
  rfl

/-- A relative cocycle of a piece has vanishing class iff it is a coboundary. -/
theorem relClass_eq_zero_iff_coboundary (W : Set B) (k : ℕ) (z : TotC Z W (k+1))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (k+1) z = 0) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz = 0 ↔
      ∃ w : TotC Z W k, relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) k w = z := by
  rw [relClassOf_eq_homologyπ' Z W (k+1) z hz]
  rw [cochain_homologyπ_eq_zero_iff]
  rw [iCycles_relCocycleOf]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (relComplex_d_apply Z W k w).symm.trans hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (relComplex_d_apply Z W k w).trans hw⟩

/-- A relative coboundary has vanishing class. -/
theorem relClass_eq_zero_of_coboundary (W : Set B) (k : ℕ) (z : TotC Z W (k+1))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (k+1) z = 0)
    (w : TotC Z W k) (hw : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) k w = z) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz = 0 :=
  (relClass_eq_zero_iff_coboundary Z W k z hz).mpr ⟨w, hw⟩

/-- Two relative cocycles of a piece have the same class iff they differ by a coboundary. -/
theorem relClass_eq_iff_sub_coboundary (W : Set B) (k : ℕ) (z z' : TotC Z W (k+1))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (k+1) z = 0)
    (hz' : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (k+1) z' = 0) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
        = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz' ↔
      ∃ w : TotC Z W k, relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) k w = z - z' := by
  rw [relClassOf_eq_homologyπ' Z W (k+1) z hz, relClassOf_eq_homologyπ' Z W (k+1) z' hz']
  have h := cochain_homologyπ_eq_iff_sub
    (C := relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)) k
    (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz)
    (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz')
  have hsub : (HomologicalComplex.iCycles (relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W))
        (relPiece Z W)) (k+1)).hom
      (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
        - relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz') = z - z' := by
    rw [map_sub, iCycles_relCocycleOf, iCycles_relCocycleOf]
  rw [hsub] at h
  refine h.trans ?_
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (relComplex_d_apply Z W k w).symm.trans hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (relComplex_d_apply Z W k w).trans hw⟩

/-- The class of a base cocycle, as the homology class of the associated cycle (the definition, as a
rewriting lemma). -/
theorem cohomologyClassOf_eq_homologyπ' (W : Set B) (k : ℕ) (a : BaseC W k)
    (ha : cochainDiff ℤ (baseSSet W) a = 0) :
    cohomologyClassOf ℤ (baseSSet W) a ha
      = (SSetCochainComplex ℤ (baseSSet W)).homologyπ k
          (cocycleOf ℤ (baseSSet W) a ha) := rfl

/-- The differential of the singular cochain complex of `W` is `cochainDiff`. -/
theorem baseComplex_d_apply (W : Set B) (k : ℕ) (w : BaseC W k) :
    (ConcreteCategory.hom ((SSetCochainComplex ℤ (baseSSet W)).d k (k+1))) w
      = cochainDiff ℤ (baseSSet W) w := by
  rw [SSetCochainComplex_d]
  rfl

/-- A base cocycle has vanishing class iff it is a coboundary. -/
theorem baseClass_eq_zero_iff_coboundary (W : Set B) (k : ℕ) (a : BaseC W (k+1))
    (ha : cochainDiff ℤ (baseSSet W) a = 0) :
    cohomologyClassOf ℤ (baseSSet W) a ha = 0 ↔
      ∃ w : BaseC W k, cochainDiff ℤ (baseSSet W) w = a := by
  have h := cochain_homologyπ_eq_zero_iff (C := SSetCochainComplex ℤ (baseSSet W)) k
    (cocycleOf ℤ (baseSSet W) a ha)
  have h3 : (ConcreteCategory.hom
      (HomologicalComplex.iCycles (SSetCochainComplex ℤ (baseSSet W)) (k+1)))
        (cocycleOf ℤ (baseSSet W) a ha) = a := iCycles_cocycleOf ℤ (baseSSet W) a ha
  refine h.trans ?_
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [baseComplex_d_apply, h3] at hw
    exact hw
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [baseComplex_d_apply, h3]
    exact hw

/-- Two base cocycles have the same class iff they differ by a coboundary. -/
theorem baseClass_eq_iff_sub_coboundary (W : Set B) (k : ℕ) (a a' : BaseC W (k+1))
    (ha : cochainDiff ℤ (baseSSet W) a = 0) (ha' : cochainDiff ℤ (baseSSet W) a' = 0) :
    cohomologyClassOf ℤ (baseSSet W) a ha = cohomologyClassOf ℤ (baseSSet W) a' ha' ↔
      ∃ w : BaseC W k, cochainDiff ℤ (baseSSet W) w = a - a' := by
  have h := cochain_homologyπ_eq_iff_sub (C := SSetCochainComplex ℤ (baseSSet W)) k
    (cocycleOf ℤ (baseSSet W) a ha) (cocycleOf ℤ (baseSSet W) a' ha')
  have hsub : (ConcreteCategory.hom
      (HomologicalComplex.iCycles (SSetCochainComplex ℤ (baseSSet W)) (k+1)))
        (cocycleOf ℤ (baseSSet W) a ha - cocycleOf ℤ (baseSSet W) a' ha') = a - a' := by
    rw [map_sub, iCycles_cocycleOf, iCycles_cocycleOf]
  rw [hsub] at h
  refine h.trans ?_
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [baseComplex_d_apply] at hw
    exact hw
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [baseComplex_d_apply]
    exact hw

end Concrete


end

end Work.ThomBordism

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}


/-! ## The class / coboundary dictionary in general degree form -/

/-- The differential of a cochain has vanishing class. -/
theorem cochain_homologyπ_toCycles_eq_zero {C : CochainComplex (ModuleCat ℤ) ℕ}
    [∀ i, C.HasHomology i] (i j : ℕ) (w : C.X i) :
    C.homologyπ j (C.toCycles i j w) = 0 := by
  have h := congrArg (fun (f : C.X i ⟶ C.homology j) => f.hom w)
    (HomologicalComplex.toCycles_comp_homologyπ C i j)
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact h

/-- The underlying cochain of `toCycles i j w` is the differential of `w`. -/
theorem iCycles_toCycles' {C : CochainComplex (ModuleCat ℤ) ℕ} [∀ i, C.HasHomology i]
    (i j : ℕ) (w : C.X i) :
    C.iCycles j (C.toCycles i j w) = C.d i j w := by
  have h := congrArg (fun (f : C.X i ⟶ C.X j) => f.hom w)
    (HomologicalComplex.toCycles_i C i j)
  rw [ModuleCat.hom_comp] at h
  exact h

/-- A cycle of a cochain complex of `ℤ`-modules has vanishing class iff it is the differential of a
cochain, for an arbitrary pair of consecutive degrees. -/
theorem cochain_homologyπ_eq_zero_iff_rel {C : CochainComplex (ModuleCat ℤ) ℕ}
    [∀ i, C.HasHomology i] {i j : ℕ} (hij : (ComplexShape.up ℕ).Rel i j) (z : C.cycles j) :
    C.homologyπ j z = 0 ↔ ∃ w : C.X i, C.d i j w = C.iCycles j z := by
  have hp : (ComplexShape.up ℕ).prev j = i := ComplexShape.prev_eq' _ hij
  constructor
  · intro hz
    let S : ShortComplex (ModuleCat ℤ) :=
      ShortComplex.mk (C.toCycles i j) (C.homologyπ j) (C.toCycles_comp_homologyπ i j)
    have hS : S.Exact := S.exact_of_g_is_cokernel (C.homologyIsCokernel i j hp)
    have hrk : (C.toCycles i j).hom.range = (C.homologyπ j).hom.ker :=
      ShortComplex.Exact.moduleCat_range_eq_ker hS
    have hz' : z ∈ (C.homologyπ j).hom.ker := by
      rw [LinearMap.mem_ker]
      exact hz
    rw [← hrk] at hz'
    obtain ⟨w, hw⟩ := hz'
    refine ⟨w, ?_⟩
    have h3 := congrArg (fun (g : C.X i ⟶ C.X j) => g.hom w)
      (HomologicalComplex.toCycles_i C i j)
    rw [ModuleCat.hom_comp] at h3
    rw [← h3]
    change (ConcreteCategory.hom (C.iCycles j)) ((ModuleCat.Hom.hom (C.toCycles i j)) w)
      = (ConcreteCategory.hom (C.iCycles j)) z
    rw [hw]
  · rintro ⟨w, hw⟩
    have h1 : C.toCycles i j w = z := by
      apply iCycles_injective_K
      rw [iCycles_toCycles', hw]
    rw [← h1]
    exact cochain_homologyπ_toCycles_eq_zero i j w

/-- **A `totShiftD`-coboundary has vanishing class** (the Tot side of the dictionary, in the
indexing of the cone). -/
theorem relClass_eq_zero_of_totShiftD (Z : RealBundle B F ι) (W : Set B) (n m : ℕ)
    (b : TotC Z W (m+n)) (z : TotC Z W ((m+1)+n))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) ((m+1)+n) z = 0)
    (h : z = - totShiftD Z n W m b) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz = 0 := by
  have hcycle : relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
      = (relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).toCycles (m+n) ((m+1)+n) (-b) := by
    apply iCycles_injective_K
    rw [iCycles_relCocycleOf, iCycles_toCycles']
    rw [h]
    show - (totShiftD Z n W m b) = totShiftD Z n W m (-b)
    rw [totShiftD_neg]
  rw [relClassOf_eq_homologyπ' Z W ((m+1)+n) z hz, hcycle]
  exact cochain_homologyπ_toCycles_eq_zero
    (C := relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)) (m+n) ((m+1)+n) (-b)

/-- **A relative cocycle of vanishing class over a piece is a `totShiftD`-coboundary.** -/
theorem exists_totShiftD_of_relClass_eq_zero (Z : RealBundle B F ι) (W : Set B) (n m : ℕ)
    (z : TotC Z W ((m+1)+n))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) ((m+1)+n) z = 0)
    (h : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz = 0) :
    ∃ w : TotC Z W (m+n), totShiftD Z n W m w = z := by
  have hrel : (ComplexShape.up ℕ).Rel (m+n) ((m+1)+n) := by
    rw [ComplexShape.up_Rel]
    omega
  have key := (cochain_homologyπ_eq_zero_iff_rel (C := relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W))
    (relPiece Z W)) hrel
    (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz)).mp h
  obtain ⟨w, hw⟩ := key
  refine ⟨w, ?_⟩
  have h2 : (relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).iCycles ((m+1)+n)
      (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz) = z :=
    iCycles_relCocycleOf ℤ _ _ z hz
  rw [h2] at hw
  exact hw

/-- **Two relative cocycles of the same class differ by a `totShiftD`-coboundary.** -/
theorem exists_totShiftD_of_relClass_eq (Z : RealBundle B F ι) (W : Set B) (n m : ℕ)
    (z z' : TotC Z W ((m+1)+n))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) ((m+1)+n) z = 0)
    (hz' : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) ((m+1)+n) z' = 0)
    (h : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
      = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz') :
    ∃ w : TotC Z W (m+n), totShiftD Z n W m w = z - z' := by
  have hsub : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) ((m+1)+n) (z - z') = 0 := by
    rw [map_sub, hz, hz', sub_self]
  have hclass : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (z - z') hsub = 0 := by
    have hsubcyc : relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (z - z') hsub
        = relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
          - relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz' := by
      apply iCycles_injective_K
      rw [map_sub, iCycles_relCocycleOf, iCycles_relCocycleOf, iCycles_relCocycleOf]
    have hh : ((relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).homologyπ ((m+1)+n)).hom
          (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz)
        = ((relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).homologyπ ((m+1)+n)).hom
          (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz') := by
      rw [← relClassOf_eq_homologyπ' Z W ((m+1)+n) z hz,
        ← relClassOf_eq_homologyπ' Z W ((m+1)+n) z' hz']
      exact h
    rw [relClassOf_eq_homologyπ' Z W ((m+1)+n) (z - z') hsub, hsubcyc,
      map_sub, hh, sub_self]
  exact exists_totShiftD_of_relClass_eq_zero Z W n m (z - z') hsub hclass


/-! ## `totShiftD` in `relDiffLM` form, and the `TotC`-zero transport -/

theorem totC_cast_zero (Z : RealBundle B F ι) (W : Set B) {a b : ℕ} (h : a = b) :
    h ▸ (0 : TotC Z W a) = (0 : TotC Z W b) := by
  cases h
  rfl

/-- A `TotC`-element whose degree transport vanishes is zero. -/
theorem totC_cast_eq_zero (Z : RealBundle B F ι) (W : Set B) {a b : ℕ} (h : a = b)
    (x : TotC Z W a) (hb : (h ▸ x) = (0 : TotC Z W b)) : x = 0 := by
  cases h
  exact hb

/-- `totShiftD` is the transport of the consecutive relative differential. -/
theorem totShiftD_eq_relDiffLM (Z : RealBundle B F ι) (W : Set B) (n m : ℕ)
    (x : TotC Z W (m+n)) :
    totShiftD Z n W m x
      = (Nat.add_right_comm m 1 n).symm ▸
          (relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m+n) x) := by
  show ((TotComplex Z W).d (m+n) ((m+1)+n)).hom x = _
  rw [totComplex_d_transfer, totComplex_d_consecutive]

/-- A `totShiftD`-cycle is a relative cocycle. -/
theorem relDiffLM_eq_zero_of_totShiftD (Z : RealBundle B F ι) (W : Set B) (n m : ℕ)
    (x : TotC Z W (m+n)) (h : totShiftD Z n W m x = 0) :
    relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m+n) x = 0 := by
  rw [totShiftD_eq_relDiffLM] at h
  exact totC_cast_eq_zero Z W _ _ h

/-- **The class of a relative cocycle of a piece vanishes iff it is a `totDpred`-coboundary**
(the `Extra`-degree analogue of `exists_totShiftD_of_relClass_eq_zero`). -/
theorem exists_totDpred_of_relClass_eq_zero (Z : RealBundle B F ι) (W : Set B) (n : ℕ)
    (hn : 1 ≤ n) (z : TotC Z W (0+n))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (0+n) z = 0)
    (h : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz = 0) :
    ∃ w : TotC Z W (n-1), totDpred Z n W w = z := by
  have hrel : (ComplexShape.up ℕ).Rel (n-1) (0+n) := by
    rw [ComplexShape.up_Rel]
    omega
  have key := (cochain_homologyπ_eq_zero_iff_rel (C := relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W))
    (relPiece Z W)) hrel
    (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz)).mp h
  obtain ⟨w, hw⟩ := key
  refine ⟨w, ?_⟩
  have h2 : (relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).iCycles (0+n)
      (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz) = z :=
    iCycles_relCocycleOf ℤ _ _ z hz
  rw [h2] at hw
  exact hw

/-- Two relative cocycles of the same class in degree `0+n` differ by a `totDpred`-coboundary. -/
theorem exists_totDpred_of_relClass_eq (Z : RealBundle B F ι) (W : Set B) (n : ℕ) (hn : 1 ≤ n)
    (z z' : TotC Z W (0+n))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (0+n) z = 0)
    (hz' : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (0+n) z' = 0)
    (h : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
      = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz') :
    ∃ w : TotC Z W (n-1), totDpred Z n W w = z - z' := by
  have hsub : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (0+n) (z - z') = 0 := by
    rw [map_sub, hz, hz', sub_self]
  have hclass : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (z - z') hsub = 0 := by
    have hsubcyc : relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (z - z') hsub
        = relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
          - relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz' := by
      apply iCycles_injective_K
      rw [map_sub, iCycles_relCocycleOf, iCycles_relCocycleOf, iCycles_relCocycleOf]
    have hh : ((relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).homologyπ (0+n)).hom
          (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz)
        = ((relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).homologyπ (0+n)).hom
          (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz') := by
      rw [← relClassOf_eq_homologyπ' Z W (0+n) z hz,
        ← relClassOf_eq_homologyπ' Z W (0+n) z' hz']
      exact h
    rw [relClassOf_eq_homologyπ' Z W (0+n) (z - z') hsub, hsubcyc,
      map_sub, hh, sub_self]
  exact exists_totDpred_of_relClass_eq_zero Z W n hn (z - z') hsub hclass

/-! ## The cone over a piece is exact, from the local Thom property -/

/-- **Positive degrees.**  If `σ|_W` is a local Thom class over `W` (`1 ≤ n`) and the class of the
cochain-level cup `psiAbs` is the `localThomMap` (the interface `PsiClassHyp`), then the cone of the
cochain-level Thom map over `W` is cyclic in every positive degree. -/
theorem coneCyclicPos_of_localThomMap (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (hψ : PsiClassHyp Z n U τ W hW)
    (hbij : ∀ k, Function.Bijective (Work.Thom.localThomMap Z n W
      ((pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' W)
        (Set.preimage_mono hW) n).hom τ) k)) :
    ∀ m, ConeCyclicPos Z n U τ W hW m := by
  intro m
  refine coneCyclicPos_of_inj_surj Z n U τ W hW m ?_ ?_
  · rintro a b hcyc
    have ha : cochainDiff ℤ (baseSSet W) a = 0 :=
      coneCycle_fst Z n U τ W hW m hcyc
    have hsnd : psiAbsLM Z n U τ W hW ((m+1)+1) a + totShiftD Z n W (m+1) b = 0 :=
      coneCycle_snd Z n U τ W hW m hcyc
    have hneg : psiAbs Z n U τ W hW ((m+1)+1) a = - totShiftD Z n W (m+1) b :=
      eq_neg_of_add_eq_zero_left hsnd
    have hcycψ : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (((m+1)+1)+n)
        (psiAbs Z n U τ W hW ((m+1)+1) a) = 0 := by
      have h := psiAbs_relDiff Z n U τ W hW ((m+1)+1) a
      rw [ha] at h
      rw [show psiAbs Z n U τ W hW (((m+1)+1)+1) (0 : BaseC W (((m+1)+1)+1)) = 0 from
        map_zero (psiAbsLM Z n U τ W hW (((m+1)+1)+1))] at h
      exact h.trans (totC_cast_zero Z W (Nat.add_right_comm ((m+1)+1) 1 n))
    have hclass : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
        (psiAbs Z n U τ W hW ((m+1)+1) a) hcycψ = 0 :=
      relClass_eq_zero_of_totShiftD Z W n (m+1) b _ hcycψ hneg
    have hinj := (hbij ((m+1)+1)).1
    have hzero : cohomologyClassOf ℤ (baseSSet W) a ha = 0 := by
      apply hinj
      rw [← hψ ((m+1)+1) a ha hcycψ, hclass, map_zero]
    obtain ⟨w, hw⟩ := (baseClass_eq_zero_iff_coboundary W (m+1) a ha).mp hzero
    refine ⟨-w, ?_⟩
    have hw' : cochainDiffLM ℤ (baseSSet W) (m+1) w = a := hw
    rw [map_neg, hw']
  · rintro b hb
    have hbcocyc : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) ((m+1)+n) b = 0 :=
      relDiffLM_eq_zero_of_totShiftD Z W n (m+1) b hb
    obtain ⟨x, hx⟩ := (hbij (m+1)).2
      (relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) b hbcocyc)
    obtain ⟨a, ha, hca⟩ := exists_cohomologyClassOf ℤ (baseSSet W) (m+1) x
    have hcycψ : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) ((m+1)+n)
        (psiAbs Z n U τ W hW (m+1) a) = 0 := by
      have h := psiAbs_relDiff Z n U τ W hW (m+1) a
      rw [ha] at h
      rw [show psiAbs Z n U τ W hW ((m+1)+1) (0 : BaseC W ((m+1)+1)) = 0 from
        map_zero (psiAbsLM Z n U τ W hW ((m+1)+1))] at h
      exact h.trans (totC_cast_zero Z W (Nat.add_right_comm (m+1) 1 n))
    have hsame : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
          (psiAbs Z n U τ W hW (m+1) a) hcycψ
        = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) b hbcocyc := by
      rw [hψ (m+1) a ha hcycψ, hca]
      exact hx
    obtain ⟨w, hw⟩ := exists_totShiftD_of_relClass_eq Z W n m _ b hcycψ hbcocyc hsame
    refine ⟨(a, -w), ?_⟩
    rw [coneD_apply]
    have h1 : cochainDiffLM ℤ (baseSSet W) (m+1) a = 0 := ha
    rw [h1, neg_zero, totShiftD_neg, hw]
    refine Prod.ext rfl ?_
    show psiAbsLM Z n U τ W hW (m+1) a - (psiAbs Z n U τ W hW (m+1) a - b) = b
    rw [show psiAbsLM Z n U τ W hW (m+1) a = psiAbs Z n U τ W hW (m+1) a from rfl]
    abel

/-- **Degree zero.**  Every cone-`0`-cycle over a piece is an `Extra`-primitive (`1 ≤ n`). -/
theorem coneCyclicZero_of_localThomMap (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (hψ : PsiClassHyp Z n U τ W hW)
    (hbij : ∀ k, Function.Bijective (Work.Thom.localThomMap Z n W
      ((pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' W)
        (Set.preimage_mono hW) n).hom τ) k)) :
    ConeCyclicZero Z n U τ W hW := by
  refine coneCyclicZero_of_inj_surj Z n U τ W hW ?_ ?_
  · rintro a b hcyc
    have ha : cochainDiff ℤ (baseSSet W) a = 0 := coneCycleZero_fst Z n U τ W hW hcyc
    have hsnd : psiAbsLM Z n U τ W hW (0+1) a + totShiftD Z n W 0 b = 0 :=
      coneCycleZero_snd Z n U τ W hW hcyc
    have hneg : psiAbs Z n U τ W hW (0+1) a = - totShiftD Z n W 0 b :=
      eq_neg_of_add_eq_zero_left hsnd
    have hcycψ : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) ((0+1)+n)
        (psiAbs Z n U τ W hW (0+1) a) = 0 := by
      have h := psiAbs_relDiff Z n U τ W hW (0+1) a
      rw [ha] at h
      rw [show psiAbs Z n U τ W hW ((0+1)+1) (0 : BaseC W ((0+1)+1)) = 0 from
        map_zero (psiAbsLM Z n U τ W hW ((0+1)+1))] at h
      exact h.trans (totC_cast_zero Z W (Nat.add_right_comm (0+1) 1 n))
    have hclass : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
        (psiAbs Z n U τ W hW (0+1) a) hcycψ = 0 :=
      relClass_eq_zero_of_totShiftD Z W n 0 b _ hcycψ hneg
    have hinj := (hbij (0+1)).1
    have hzero : cohomologyClassOf ℤ (baseSSet W) a ha = 0 := by
      apply hinj
      rw [← hψ (0+1) a ha hcycψ, hclass, map_zero]
    obtain ⟨w, hw⟩ := (baseClass_eq_zero_iff_coboundary W 0 a ha).mp hzero
    refine ⟨-w, ?_⟩
    have hw' : cochainDiffLM ℤ (baseSSet W) 0 w = a := hw
    rw [map_neg, hw']
  · rintro b hb
    have hbcocyc : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (0+n) b = 0 :=
      relDiffLM_eq_zero_of_totShiftD Z W n 0 b hb
    obtain ⟨x, hx⟩ := (hbij 0).2
      (relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) b hbcocyc)
    obtain ⟨a, ha, hca⟩ := exists_cohomologyClassOf ℤ (baseSSet W) 0 x
    have hcycψ : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (0+n)
        (psiAbs Z n U τ W hW 0 a) = 0 := by
      have h := psiAbs_relDiff Z n U τ W hW 0 a
      rw [ha] at h
      rw [show psiAbs Z n U τ W hW (0+1) (0 : BaseC W (0+1)) = 0 from
        map_zero (psiAbsLM Z n U τ W hW (0+1))] at h
      exact h.trans (totC_cast_zero Z W (Nat.add_right_comm 0 1 n))
    have hsame : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
          (psiAbs Z n U τ W hW 0 a) hcycψ
        = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) b hbcocyc := by
      rw [hψ 0 a ha hcycψ, hca]
      exact hx
    obtain ⟨w, hw⟩ := exists_totDpred_of_relClass_eq Z W n hn _ b hcycψ hbcocyc hsame
    refine ⟨(a, -w), ?_⟩
    rw [extraD]
    have h1 : cochainDiffLM ℤ (baseSSet W) 0 a = 0 := ha
    rw [h1, neg_zero, totDpred_neg, hw]
    refine Prod.ext rfl ?_
    show psiAbsLM Z n U τ W hW 0 a - (psiAbs Z n U τ W hW 0 a - b) = b
    rw [show psiAbsLM Z n U τ W hW 0 a = psiAbs Z n U τ W hW 0 a from rfl]
    abel

end

end Work.ThomBordism

