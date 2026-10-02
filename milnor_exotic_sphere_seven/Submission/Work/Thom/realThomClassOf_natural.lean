import Mathlib
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.localThomOfChart_comap
import Submission.Work.Thom.exists_unique_pieceClass
import Submission.Work.Thom.exists_unique_thomClassOfLocalThomUniv
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.thomClassOf_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.defProp false

/-!
# The canonical Thom class of an oriented real bundle, and its naturality

`Work.Thom.thomClass_of_oriented_fintype` proves that an oriented real bundle of rank `n ≥ 1` over
gluing data with finite index type has a Thom class; the witness there is an opaque
`Classical.choice`, which is *not* natural.

This module replaces the choice by a **construction**, on the model of
`Work.Thom.localThomOfComplexCover`/`Work.Thom.thomClassOf`:

* the local data over each piece of the cover by the chart sets `Z.baseSet i` is the explicit chart
  class `Work.Thom.localThomOfChart` (with the identity identification of `ℝⁿ`);
* the compatibility of the chart classes on overlaps is positivity of the determinant of the
  transition function (`Work.Thom.localThomOfChart_eq_of_det_pos`) — the orientation hypothesis;
* the Mayer–Vietoris class over the union of the cover is the `Classical.choose` of the
  **`∃!`**-statement `Work.Thom.exists_unique_pieceClass` (unique by the low-degree vanishing
  `Work.Thom.subsingleton_PieceCoh_iUnion_finInter_clean`);
* the final passage to a `ThomClass` is the `Classical.choose` of the **`∃!`**-statement
  `Work.Thom.exists_unique_thomClassOfLocalThomUniv`.

The result `Work.Thom.realThomClassOf` is thus a *function* of the oriented bundle.  The main
theorem of the module, `Work.Thom.realThomClassOf_natural`, collects the naturality of this
canonical choice under pullback into the single statement needed by the rest of the chapter.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {B' : Type} [TopologicalSpace B']

/-! ## The reindexed chart cover -/

/-- The reindexing `Fin (card ι) → ι` of the chart cover. -/
def oriCC {ι : Type} [Fintype ι] : Fin (Fintype.card ι) → ι := fun k => (Fintype.equivFin ι).symm k

/-- The chart cover of a real bundle with fibre `ℝⁿ`, reindexed along `Fintype.equivFin`. -/
def oriU {ι : Type} [Fintype ι] {n : ℕ} (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) :
    Fin (Fintype.card ι) → Set B := fun k => Z.baseSet (oriCC (ι := ι) k)

/-- The identity identification of the fibre `ℝⁿ` with the model `ℝⁿ`. -/
def oriE (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearEquiv.refl ℝ _

theorem oriHU {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) : ∀ k, IsOpen (oriU Z k) :=
  fun k => Z.isOpen_baseSet (oriCC (ι := ι) k)

theorem oriHsub {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) :
    finInter (oriU Z) S ⊆ Z.baseSet (oriCC (ι := ι) hS.choose) :=
  fun _ hx => (mem_finInter.mp hx) hS.choose hS.choose_spec

/-- The prescribed local classes of the cover: the explicit chart classes. -/
def oriC {ι : Type} [Fintype ι] {n : ℕ} (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) :
    ∀ (S : Finset (Fin (Fintype.card ι))), S.Nonempty →
      PieceCoh Z (finInter (oriU Z) S) n :=
  fun S hS => (localThomOfChart Z n (oriE n) (oriCC (ι := ι) hS.choose)
    (finInter (oriU Z) S) (oriHsub Z S hS)).τ

/-- The local Thom isomorphism of the prescribed chart classes. -/
theorem oriHc {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) :
    ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (j : ℕ),
      Function.Bijective (localThomMap Z n (finInter (oriU Z) S) (oriC Z S hS) j) := by
  intro S hS j
  dsimp only [oriC]
  exact (localThomOfChart Z n (oriE n) (oriCC (ι := ι) hS.choose)
    (finInter (oriU Z) S) (oriHsub Z S hS)).isThom j

/-- The compatibility of the prescribed chart classes under restriction, using the orientation. -/
theorem oriHcompat {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    ∀ (S T : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T),
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' finInter (oriU Z) S) (Z.proj ⁻¹' finInter (oriU Z) T)
        (Set.preimage_mono (finInter_mono hST)) n).hom (oriC Z S hS) = oriC Z T hT := by
  intro S T hS hT hST
  have hsub' : finInter (oriU Z) T ⊆ finInter (oriU Z) S := finInter_mono hST
  have hTS : finInter (oriU Z) T ⊆ Z.baseSet (oriCC (ι := ι) hS.choose) :=
    hsub'.trans (oriHsub Z S hS)
  have hSS : finInter (oriU Z) S ⊆ Z.baseSet (oriCC (ι := ι) hS.choose) := oriHsub Z S hS
  have hW : finInter (oriU Z) T ⊆ Z.baseSet (oriCC (ι := ι) hS.choose)
      ∩ Z.baseSet (oriCC (ι := ι) hT.choose) :=
    fun x hx => ⟨hTS hx, oriHsub Z T hT hx⟩
  have hcS : oriC Z S hS
      = (localThomOfChart Z n (oriE n) (oriCC (ι := ι) hS.choose)
          (finInter (oriU Z) S) hSS).τ := by
    dsimp only [oriC]
  have hcT : oriC Z T hT
      = (localThomOfChart Z n (oriE n) (oriCC (ι := ι) hS.choose)
          (finInter (oriU Z) T) hTS).τ := by
    dsimp only [oriC]
    exact localThomOfChart_eq_of_det_pos Z n hn (oriE n) (oriCC (ι := ι) hS.choose)
      (oriCC (ι := ι) hT.choose) (finInter (oriU Z) T) hTS (oriHsub Z T hT) hW
      (fun x => hori (oriCC (ι := ι) hS.choose) (oriCC (ι := ι) hT.choose)
        ⟨(x : B), hW x.2⟩)
  rw [hcS, hcT]
  exact localThomOfChart_restrict Z n (oriE n) (oriCC (ι := ι) hS.choose)
    (finInter (oriU Z) T) (finInter (oriU Z) S) hTS hSS hsub'

/-- The low-degree vanishing of the cover (independent of the orientation). -/
theorem oriHlow {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) :
    ∀ (A : Finset (Finset (Fin (Fintype.card ι)))),
      (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (PieceCoh Z (⋃ S ∈ A, finInter (oriU Z) S) (n - 1)) :=
  fun A hA _ => subsingleton_PieceCoh_iUnion_finInter_clean Z (Fintype.card ι) (oriU Z)
    (oriHU Z) (oriCC (ι := ι)) (fun k => subset_rfl) A hA (m := n - 1) (by
      rw [finrank_euclideanSpace_fin]
      omega)

/-- The `∃!`-statement whose witness is the Mayer–Vietoris class of the finite chart cover. -/
noncomputable def oriExists {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :=
  exists_unique_pieceClass Z n hn (Fintype.card ι) (oriU Z) (oriHU Z) (oriC Z) (oriHc Z)
    (oriHcompat hn Z hori) (oriHlow hn Z)

/-- **The Mayer–Vietoris witness of the finite chart cover**, as a top-level definition: the
`Classical.choose`d class over the union of the cover. -/
def oriWitness {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    PieceCoh Z (⋃ k, oriU Z k) n :=
  Classical.choose (oriExists hn Z hori)

/-- **The restriction property of `oriWitness`**: its restriction to the piece of a nonempty finite
family `S` is the prescribed chart class `oriC`. -/
theorem oriWitness_restrict {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap))
    (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) :
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
      (Z.proj ⁻¹' (⋃ k, oriU Z k)) (Z.proj ⁻¹' (finInter (oriU Z) S))
      (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) n).hom (oriWitness hn Z hori)
      = oriC Z S hS :=
  (Classical.choose_spec (oriExists hn Z hori)).1.2 S hS

/-- **The local Thom isomorphism of `oriWitness`.** -/
theorem oriWitness_isThom {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) (j : ℕ) :
    Function.Bijective (localThomMap Z n (⋃ k, oriU Z k) (oriWitness hn Z hori) j) :=
  (Classical.choose_spec (oriExists hn Z hori)).1.1 j

/-- The cover equality of the chart cover: the base sets cover the base. -/
theorem oriHcover {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) : (⋃ k, oriU Z k) = Set.univ := by
  have h1 : (⋃ k : Fin (Fintype.card ι), Z.baseSet (oriCC (ι := ι) k))
      = ⋃ i : ι, Z.baseSet i := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨oriCC k, hk⟩
    · rintro ⟨i, hi⟩
      exact ⟨Fintype.equivFin ι i, by simpa only [oriCC, Equiv.symm_apply_apply] using hi⟩
  rw [show (⋃ k, oriU Z k)
    = ⋃ k : Fin (Fintype.card ι), Z.baseSet (oriCC (ι := ι) k) from rfl, h1]
  exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩

/-- **The canonical local Thom data over the whole base** of an oriented real bundle of rank
`n ≥ 1`: the cast of the Mayer–Vietoris witness of the chart cover. -/
def localThomOfOrientedCover {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    LocalThom Z n Set.univ :=
  ⟨oriHcover Z ▸ oriWitness hn Z hori,
    fun j => bijective_localThomMap_cast Z (oriHcover Z) (oriWitness hn Z hori) j
      (oriWitness_isThom hn Z hori j)⟩

/-- The defining equation of `localThomOfOrientedCover`. -/
theorem localThomOfOrientedCover_tau_eq {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    (localThomOfOrientedCover hn Z hori).τ = oriHcover Z ▸ oriWitness hn Z hori := rfl

/-- **The canonical Thom class of an oriented real bundle of rank `m ≥ 1` over gluing data with
finite index type**: the unique Thom class whose class restricts, over the whole base, to the local
data of `localThomOfOrientedCover`. -/
noncomputable def realThomClassOf {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    ThomClass Z n :=
  Classical.choose
    (exists_unique_thomClassOfLocalThomUniv Z (localThomOfOrientedCover hn Z hori))

/-- The defining equation of `realThomClassOf`. -/
theorem realThomClassOf_spec {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    (relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Z.proj ⁻¹' (Set.univ : Set B)), Z.TotalSpace))
      {y : ↥(Z.proj ⁻¹' (Set.univ : Set B)) | (y : Z.TotalSpace) ∈ zeroComplement Z}
      (zeroComplement Z) (fun _ hy => hy) ℤ n).hom
      (realThomClassOf hn Z hori).τ
    = (localThomOfOrientedCover hn Z hori).τ :=
  (Classical.choose_spec
    (exists_unique_thomClassOfLocalThomUniv Z (localThomOfOrientedCover hn Z hori))).1

/-! ## Naturality of the chart cover and of the chart classes under pullback -/

theorem oriU_comap {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (f : C(B', B))
    (k : Fin (Fintype.card ι)) : oriU (bundleComap Z f) k = f ⁻¹' oriU Z k := rfl

theorem finInter_oriU_comap {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (f : C(B', B))
    (S : Finset (Fin (Fintype.card ι))) :
    finInter (oriU (bundleComap Z f)) S = f ⁻¹' finInter (oriU Z) S := by
  ext x
  rw [mem_finInter, Set.mem_preimage, mem_finInter]
  constructor
  · intro h k hk
    have hk' := h k hk
    rw [oriU_comap Z f k] at hk'
    exact hk'
  · intro h k hk
    rw [oriU_comap Z f k]
    exact h k hk

theorem oriHfUnion {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (f : C(B', B)) :
    ∀ x ∈ ⋃ k, oriU (bundleComap Z f) k, f x ∈ ⋃ k, oriU Z k := by
  intro x hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨k, by rw [oriU_comap Z f k] at hk; exact hk⟩

theorem oriHfInter {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (f : C(B', B))
    (S : Finset (Fin (Fintype.card ι))) :
    ∀ x ∈ finInter (oriU (bundleComap Z f)) S, f x ∈ finInter (oriU Z) S := by
  intro x hx
  rw [finInter_oriU_comap Z f S] at hx
  exact hx

/-! ## The generic bookkeeping lemmas for `Work.Thom.pieceMap` -/

theorem pieceMap_mem {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] (Z : RealBundle B F ι)
    (f : C(B', B)) {W : Set B} {W' : Set B'} (hWf : ∀ x ∈ W', f x ∈ W) :
    ∀ p ∈ pieceZero (bundleComap Z f) W', pieceMap Z f hWf p ∈ pieceZero Z W := by
  intro p hp
  show (show F from ((pieceMap Z f hWf p : Z.TotalSpace)).2) ≠ 0
  have h1 : (show F from ((pieceMap Z f hWf p : Z.TotalSpace)).2) = (show F from p.1.2) := by
    rw [pieceMap_apply]
  rw [h1]
  exact hp

/-- **Casting the piece class from a union of the cover to the whole base commutes with the
pullback along the map of the total spaces.** -/
theorem pieceMap_cast_comm {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    {n : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (Z : RealBundle B F ι) (f : C(B', B))
    {V : Set B} {V' : Set B'} (hVf : ∀ x ∈ V', f x ∈ V)
    (hV : V = Set.univ) (hV' : V' = Set.univ) (cU : PieceCoh Z V n) :
    (relCohMap (pieceMap Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial))
      (pieceZero (bundleComap Z f) Set.univ) (pieceZero Z Set.univ)
      (pieceMap_mem Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial)) ℤ n).hom
        (hV ▸ cU)
    = hV' ▸ ((relCohMap (pieceMap Z f hVf)
        (pieceZero (bundleComap Z f) V') (pieceZero Z V)
        (pieceMap_mem Z f hVf) ℤ n).hom cU) := by
  subst hV
  subst hV'
  rfl

/-! ## Naturality of the chart classes and of the Mayer–Vietoris witness -/

/-- The restriction of `oriWitness` to a piece, in the `relCohMap` language. -/
theorem pieceIncl_oriWitness {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap))
    (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty)
    (w : RelCoh ℤ n ↥(Z.proj ⁻¹' (⋃ k, oriU Z k)) (pieceZero Z (⋃ k, oriU Z k)))
    (hw : w = oriWitness hn Z hori) :
    (relCohMap (pieceIncl Z (finInter (oriU Z) S) (⋃ k, oriU Z k)
        (finInter_nonempty_subset_iUnion hS))
      (pieceZero Z (finInter (oriU Z) S)) (pieceZero Z (⋃ k, oriU Z k))
      (pieceIncl_mem Z (finInter (oriU Z) S) (⋃ k, oriU Z k)
        (finInter_nonempty_subset_iUnion hS)) ℤ n).hom w
      = oriC Z S hS := by
  subst hw
  rw [← pdCohMap_eq_relCohMap Z (finInter (oriU Z) S) (⋃ k, oriU Z k)
    (finInter_nonempty_subset_iUnion hS) n]
  exact oriWitness_restrict hn Z hori S hS

/-- The pullback of the prescribed chart class is the prescribed chart class of the pullback. -/
theorem pieceMap_oriC {ι : Type} [Fintype ι] {n : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (f : C(B', B))
    (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty)
    (cS : RelCoh ℤ n ↥(Z.proj ⁻¹' (finInter (oriU Z) S))
      (pieceZero Z (finInter (oriU Z) S))) (hcS : cS = oriC Z S hS) :
    (relCohMap (pieceMap Z f (oriHfInter Z f S))
      (pieceZero (bundleComap Z f) (finInter (oriU (bundleComap Z f)) S))
      (pieceZero Z (finInter (oriU Z) S))
      (pieceMap_mem Z f (oriHfInter Z f S)) ℤ n).hom cS
      = oriC (bundleComap Z f) S hS := by
  subst hcS
  exact localThomOfChart_comap Z f (oriE n) (oriCC (ι := ι) hS.choose) (oriHsub Z S hS)
    (oriHsub (bundleComap Z f) S hS) (oriHfInter Z f S)

/-- **Naturality of the Mayer–Vietoris witness under pullback.** -/
theorem oriWitness_comap {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap))
    (f : C(B', B))
    (hori' : ∀ (i j : ι) (x : ↥((bundleComap Z f).baseSet i ∩ (bundleComap Z f).baseSet j)),
      0 < LinearMap.det (((bundleComap Z f).coordChange i j (x : B')).toLinearMap)) :
    (relCohMap (pieceMap Z f (oriHfUnion Z f))
      (pieceZero (bundleComap Z f) (⋃ k, oriU (bundleComap Z f) k))
      (pieceZero Z (⋃ k, oriU Z k))
      (pieceMap_mem Z f (oriHfUnion Z f)) ℤ n).hom (oriWitness hn Z hori)
      = oriWitness hn (bundleComap Z f) hori' := by
  let w : RelCoh ℤ n ↥(Z.proj ⁻¹' (⋃ k, oriU Z k)) (pieceZero Z (⋃ k, oriU Z k)) :=
    oriWitness hn Z hori
  let w' : RelCoh ℤ n ↥((bundleComap Z f).proj ⁻¹' (⋃ k, oriU (bundleComap Z f) k))
      (pieceZero (bundleComap Z f) (⋃ k, oriU (bundleComap Z f) k)) :=
    oriWitness hn (bundleComap Z f) hori'
  have hper : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty),
      (Work.Cohomology.pdCohMap (TopCat.of (bundleComap Z f).TotalSpace)
        (zeroComplement (bundleComap Z f))
        ((bundleComap Z f).proj ⁻¹' (⋃ k, oriU (bundleComap Z f) k))
        ((bundleComap Z f).proj ⁻¹' (finInter (oriU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) n).hom
        ((relCohMap (pieceMap Z f (oriHfUnion Z f))
          (pieceZero (bundleComap Z f) (⋃ k, oriU (bundleComap Z f) k))
          (pieceZero Z (⋃ k, oriU Z k))
          (pieceMap_mem Z f (oriHfUnion Z f)) ℤ n).hom w)
      = oriC (bundleComap Z f) S hS := by
    intro S hS
    let A : Set ↥((bundleComap Z f).proj ⁻¹' (finInter (oriU (bundleComap Z f)) S)) :=
      pieceZero (bundleComap Z f) (finInter (oriU (bundleComap Z f)) S)
    let Bs : Set ↥(Z.proj ⁻¹' (finInter (oriU Z) S)) :=
      pieceZero Z (finInter (oriU Z) S)
    let Bp : Set ↥((bundleComap Z f).proj ⁻¹' (⋃ k, oriU (bundleComap Z f) k)) :=
      pieceZero (bundleComap Z f) (⋃ k, oriU (bundleComap Z f) k)
    let C : Set ↥(Z.proj ⁻¹' (⋃ k, oriU Z k)) :=
      pieceZero Z (⋃ k, oriU Z k)
    let cS : RelCoh ℤ n ↥(Z.proj ⁻¹' (finInter (oriU Z) S)) Bs := oriC Z S hS
    let cS' : RelCoh ℤ n
        ↥((bundleComap Z f).proj ⁻¹' (finInter (oriU (bundleComap Z f)) S)) A :=
      oriC (bundleComap Z f) S hS
    let pmW : C(↥((bundleComap Z f).proj ⁻¹' (⋃ k, oriU (bundleComap Z f) k)),
        ↥(Z.proj ⁻¹' (⋃ k, oriU Z k))) := pieceMap Z f (oriHfUnion Z f)
    let pmS : C(↥((bundleComap Z f).proj ⁻¹' (finInter (oriU (bundleComap Z f)) S)),
        ↥(Z.proj ⁻¹' (finInter (oriU Z) S))) := pieceMap Z f (oriHfInter Z f S)
    let inclW' : C(↥((bundleComap Z f).proj ⁻¹' (finInter (oriU (bundleComap Z f)) S)),
        ↥((bundleComap Z f).proj ⁻¹' (⋃ k, oriU (bundleComap Z f) k))) :=
      pieceIncl (bundleComap Z f) (finInter (oriU (bundleComap Z f)) S)
        (⋃ k, oriU (bundleComap Z f) k) (finInter_nonempty_subset_iUnion hS)
    let inclW : C(↥(Z.proj ⁻¹' (finInter (oriU Z) S)),
        ↥(Z.proj ⁻¹' (⋃ k, oriU Z k))) :=
      pieceIncl Z (finInter (oriU Z) S) (⋃ k, oriU Z k) (finInter_nonempty_subset_iUnion hS)
    have hmemW : ∀ x ∈ Bp, pmW x ∈ C := pieceMap_mem Z f (oriHfUnion Z f)
    have hmemS : ∀ x ∈ A, pmS x ∈ Bs := pieceMap_mem Z f (oriHfInter Z f S)
    have hmemI' : ∀ x ∈ A, inclW' x ∈ Bp :=
      pieceIncl_mem (bundleComap Z f) (finInter (oriU (bundleComap Z f)) S)
        (⋃ k, oriU (bundleComap Z f) k) (finInter_nonempty_subset_iUnion hS)
    have hmemI : ∀ x ∈ Bs, inclW x ∈ C :=
      pieceIncl_mem Z (finInter (oriU Z) S) (⋃ k, oriU Z k)
        (finInter_nonempty_subset_iUnion hS)
    have hmap : pmW.comp inclW' = inclW.comp pmS := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      simp only [pmW, pmS, inclW', inclW, ContinuousMap.comp_apply, pieceIncl_apply,
        pieceMap_apply]
    have hgfW : ∀ x ∈ A, (pmW.comp inclW') x ∈ C :=
      fun x hx => hmemW (inclW' x) (hmemI' x hx)
    have hgfS : ∀ x ∈ A, (inclW.comp pmS) x ∈ C :=
      fun x hx => hmemI (pmS x) (hmemS x hx)
    have h1 : (relCohMap inclW' A Bp hmemI' ℤ n).hom
          ((relCohMap pmW Bp C hmemW ℤ n).hom w)
        = (relCohMap (pmW.comp inclW') A C hgfW ℤ n).hom w :=
      relCohMap_compA_apply A Bp C inclW' pmW hmemI' hmemW hgfW ℤ n w
    have hmor : relCohMap (pmW.comp inclW') A C hgfW ℤ n
        = relCohMap (inclW.comp pmS) A C hgfS ℤ n :=
      relCohMap_congrA A C hmap hgfW hgfS ℤ n
    have h2 : (relCohMap (pmW.comp inclW') A C hgfW ℤ n).hom w
        = (relCohMap (inclW.comp pmS) A C hgfS ℤ n).hom w :=
      congrArg (fun φ => φ.hom w) hmor
    have h3 : (relCohMap (inclW.comp pmS) A C hgfS ℤ n).hom w
        = (relCohMap pmS A Bs hmemS ℤ n).hom
            ((relCohMap inclW Bs C hmemI ℤ n).hom w) :=
      (relCohMap_compA_apply A Bs C pmS inclW hmemS hmemI hgfS ℤ n w).symm
    have h4 : (relCohMap inclW Bs C hmemI ℤ n).hom w = cS :=
      pieceIncl_oriWitness hn Z hori S hS w rfl
    have h5 : (relCohMap pmS A Bs hmemS ℤ n).hom cS = cS' :=
      pieceMap_oriC Z f S hS cS rfl
    have hstep : (relCohMap pmS A Bs hmemS ℤ n).hom
          ((relCohMap inclW Bs C hmemI ℤ n).hom w)
        = (relCohMap pmS A Bs hmemS ℤ n).hom cS :=
      congrArg (fun z => (relCohMap pmS A Bs hmemS ℤ n).hom z) h4
    show (Work.Cohomology.pdCohMap (TopCat.of (bundleComap Z f).TotalSpace)
        (zeroComplement (bundleComap Z f))
        ((bundleComap Z f).proj ⁻¹' (⋃ k, oriU (bundleComap Z f) k))
        ((bundleComap Z f).proj ⁻¹' (finInter (oriU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) n).hom
        ((relCohMap pmW Bp C hmemW ℤ n).hom w) = cS'
    rw [pdCohMap_eq_relCohMap (bundleComap Z f)
      (finInter (oriU (bundleComap Z f)) S) (⋃ k, oriU (bundleComap Z f) k)
      (finInter_nonempty_subset_iUnion hS) n]
    exact h1.trans (h2.trans (h3.trans (hstep.trans h5)))
  refine sub_eq_zero.mp ?_
  apply pdCohMap_finInter_eq_zero (bundleComap Z f) n (Fintype.card ι)
    (oriU (bundleComap Z f)) (oriHU (bundleComap Z f)) (oriHlow hn (bundleComap Z f))
  intro S hS
  rw [map_sub,
    show (Work.Cohomology.pdCohMap (TopCat.of (bundleComap Z f).TotalSpace)
        (zeroComplement (bundleComap Z f))
        ((bundleComap Z f).proj ⁻¹' (⋃ k, oriU (bundleComap Z f) k))
        ((bundleComap Z f).proj ⁻¹' (finInter (oriU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) n).hom
        ((relCohMap (pieceMap Z f (oriHfUnion Z f))
          (pieceZero (bundleComap Z f) (⋃ k, oriU (bundleComap Z f) k))
          (pieceZero Z (⋃ k, oriU Z k))
          (pieceMap_mem Z f (oriHfUnion Z f)) ℤ n).hom w)
        = oriC (bundleComap Z f) S hS from hper S hS,
    show (Work.Cohomology.pdCohMap (TopCat.of (bundleComap Z f).TotalSpace)
        (zeroComplement (bundleComap Z f))
        ((bundleComap Z f).proj ⁻¹' (⋃ k, oriU (bundleComap Z f) k))
        ((bundleComap Z f).proj ⁻¹' (finInter (oriU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) n).hom w'
        = oriC (bundleComap Z f) S hS from oriWitness_restrict hn (bundleComap Z f) hori' S hS,
    sub_self]

/-! ## Naturality of the canonical Thom class -/

theorem realThomClassOf_comap {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap))
    (f : C(B', B))
    (hori' : ∀ (i j : ι)
      (x : ↥((bundleComap Z f).baseSet i ∩ (bundleComap Z f).baseSet j)),
      0 < LinearMap.det (((bundleComap Z f).coordChange i j (x : B')).toLinearMap)) :
    (relCohMap (totalMap Z f) (zeroComplement (bundleComap Z f)) (zeroComplement Z)
      (totalMap_mem_zeroComplement Z f) ℤ n).hom (realThomClassOf hn Z hori).τ
    = (realThomClassOf hn (bundleComap Z f) hori').τ := by
  classical
  let pzZ : Set ↥(Z.proj ⁻¹' (Set.univ : Set B)) := pieceZero Z (Set.univ : Set B)
  let pzX : Set ↥((bundleComap Z f).proj ⁻¹' (Set.univ : Set B')) :=
    pieceZero (bundleComap Z f) (Set.univ : Set B')
  let univZ : C(↥(Z.proj ⁻¹' (Set.univ : Set B)), Z.TotalSpace) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let univX : C(↥((bundleComap Z f).proj ⁻¹' (Set.univ : Set B')),
      (bundleComap Z f).TotalSpace) := ⟨Subtype.val, continuous_subtype_val⟩
  let pm : C(↥((bundleComap Z f).proj ⁻¹' (Set.univ : Set B')),
      ↥(Z.proj ⁻¹' (Set.univ : Set B))) :=
    pieceMap Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial)
  let tZ : OpenThom Z n := (realThomClassOf hn Z hori).τ
  let tX : OpenThom (bundleComap Z f) n := (realThomClassOf hn (bundleComap Z f) hori').τ
  let TZ : PieceCoh Z (Set.univ : Set B) n := (localThomOfOrientedCover hn Z hori).τ
  let TX : PieceCoh (bundleComap Z f) (Set.univ : Set B') n :=
    (localThomOfOrientedCover hn (bundleComap Z f) hori').τ
  have hmemR : ∀ x ∈ pzX, pm x ∈ pzZ :=
    pieceMap_mem Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial)
  have hmemX : ∀ x ∈ pzX, univX x ∈ zeroComplement (bundleComap Z f) := fun _ hx => hx
  have hmemZ : ∀ x ∈ pzZ, univZ x ∈ zeroComplement Z := fun _ hx => hx
  have hmemT : ∀ x ∈ zeroComplement (bundleComap Z f), totalMap Z f x ∈ zeroComplement Z :=
    totalMap_mem_zeroComplement Z f
  have hspecZ := realThomClassOf_spec hn Z hori
  have hspecX := realThomClassOf_spec hn (bundleComap Z f) hori'
  have hcast := pieceMap_cast_comm Z f (oriHfUnion Z f) (oriHcover Z)
    (oriHcover (bundleComap Z f)) (oriWitness hn Z hori)
  have hcompmap : (totalMap Z f).comp univX = univZ.comp pm := by
    apply ContinuousMap.ext
    intro q
    show (totalMap Z f) (univX q) = univZ (pm q)
    rw [show univZ (pm q) = (pm q : Z.TotalSpace) from rfl]
    rw [totalMap_apply, pieceMap_apply]
    rfl
  have hanat : (relCohMap pm pzX pzZ hmemR ℤ n).hom TZ = TX := by
    have h2 := congrArg (fun z => (oriHcover (bundleComap Z f) ▸ z :
        RelCoh ℤ n ↥((bundleComap Z f).proj ⁻¹' (Set.univ : Set B'))
          (pieceZero (bundleComap Z f) (Set.univ : Set B'))))
      (oriWitness_comap hn Z hori f hori')
    have h3 : ((oriHcover (bundleComap Z f) ▸ oriWitness hn (bundleComap Z f) hori' :
        RelCoh ℤ n ↥((bundleComap Z f).proj ⁻¹' (Set.univ : Set B'))
          (pieceZero (bundleComap Z f) (Set.univ : Set B')))) = TX := rfl
    exact hcast.trans (h2.trans h3)
  let eX : ↥((bundleComap Z f).proj ⁻¹' (Set.univ : Set B')) ≃ₜ (bundleComap Z f).TotalSpace :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p, Set.mem_univ p⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun p => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk (fun _ => trivial) }
  have hbij := bijective_relCohMap_of_homeomorphA pzX (zeroComplement (bundleComap Z f)) eX
    (fun y => Iff.rfl) ℤ n
  change (relCohMap (totalMap Z f) (zeroComplement (bundleComap Z f)) (zeroComplement Z)
    hmemT ℤ n).hom tZ = tX
  refine hbij.1 ?_
  have hgf1 : ∀ x ∈ pzX, ((totalMap Z f).comp univX) x ∈ zeroComplement Z :=
    fun x hx => hmemT (univX x) hx
  have hgf2 : ∀ x ∈ pzX, (univZ.comp pm) x ∈ zeroComplement Z :=
    fun x hx => hmemZ (pm x) (hmemR x hx)
  calc (relCohMap univX pzX (zeroComplement (bundleComap Z f)) hmemX ℤ n).hom
        ((relCohMap (totalMap Z f) (zeroComplement (bundleComap Z f)) (zeroComplement Z)
          hmemT ℤ n).hom tZ)
      = (relCohMap ((totalMap Z f).comp univX) pzX (zeroComplement Z) hgf1 ℤ n).hom tZ :=
        relCohMap_compA_apply pzX (zeroComplement (bundleComap Z f)) (zeroComplement Z)
          univX (totalMap Z f) hmemX hmemT hgf1 ℤ n tZ
    _ = (relCohMap (univZ.comp pm) pzX (zeroComplement Z) hgf2 ℤ n).hom tZ :=
        congrArg (fun φ => φ.hom tZ)
          (relCohMap_congrA pzX (zeroComplement Z) hcompmap hgf1 hgf2 ℤ n)
    _ = (relCohMap pm pzX pzZ hmemR ℤ n).hom
          ((relCohMap univZ pzZ (zeroComplement Z) hmemZ ℤ n).hom tZ) :=
        (relCohMap_compA_apply pzX pzZ (zeroComplement Z) pm univZ hmemR hmemZ hgf2
          ℤ n tZ).symm
    _ = (relCohMap pm pzX pzZ hmemR ℤ n).hom TZ :=
        congrArg (fun z => (relCohMap pm pzX pzZ hmemR ℤ n).hom z) hspecZ
    _ = (relCohMap univX pzX (zeroComplement (bundleComap Z f)) hmemX ℤ n).hom tX :=
        hanat.trans hspecX.symm

theorem realThomClassOf_natural (n : ℕ) (hn : 1 ≤ n) :
    ∃ cT : ∀ {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
        (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
        (_hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
          0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)),
        Work.Thom.ThomClass Z n,
      ∀ {B : Type} [TopologicalSpace B] {B' : Type} [TopologicalSpace B']
        {ι : Type} [Fintype ι]
        (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
        (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
          0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap))
        (f : C(B', B))
        (_hori' : ∀ (i j : ι)
          (x : ↥((Work.Thom.bundleComap Z f).baseSet i ∩ (Work.Thom.bundleComap Z f).baseSet j)),
          0 < LinearMap.det (((Work.Thom.bundleComap Z f).coordChange i j (x : B')).toLinearMap)),
        (Work.Thom.relCohMap (Work.Thom.totalMap Z f)
          (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f)) (Work.Thom.zeroComplement Z)
          (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom (cT Z hori).τ
        = (cT (Work.Thom.bundleComap Z f) _hori').τ :=
  ⟨fun Z hori => realThomClassOf hn Z hori,
   fun Z hori f hori' => realThomClassOf_comap hn Z hori f hori'⟩

end

end Work.Thom
