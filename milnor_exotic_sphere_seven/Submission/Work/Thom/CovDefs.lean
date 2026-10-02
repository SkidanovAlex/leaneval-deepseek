import Mathlib
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.exists_unique_pieceClass
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Gen.RifStd

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
# The concrete data of the finite-cover construction of `localThomOfComplexCover`

`Work.Thom.localThomOfComplexCover` builds its local data with a chain of local `let`s, so the
witness of `Work.Thom.exists_unique_pieceClass` that it uses is not accessible from the outside.
This module exposes the *same* data as top-level definitions (`covCC`, `covZR`, `covU`, `covC`,
`covExists`, `covWitness`, ...) and records the definitional identity

`(localThomOfComplexCover hm Z).τ = covHcover Z ▸ covWitness hm Z`,

together with the characterising properties of `covWitness` (the ones coming from the
`∃!`-statement `Work.Thom.exists_unique_pieceClass`).  These are the inputs of the naturality of
the local data under pullback.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- The permutation `Fin (card ι) → ι` used by `localThomOfComplexCover`. -/
def covCC : Fin (Fintype.card ι) → ι := fun k => (Fintype.equivFin ι).symm k

/-- The realification of `Z`, as a top-level definition. -/
def covZR {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    RealBundle B (EuclideanSpace ℂ (Fin m)) ι := realification Z

/-- The cover of `B` by the base sets of `Z`, indexed by `Fin (card ι)`. -/
def covU {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Fin (Fintype.card ι) → Set B := fun k => (covZR Z).baseSet (covCC k)

/-- The inclusion of a finite intersection into the chart of its chosen index. -/
def covHsub {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) :
    finInter (covU Z) S ⊆ (covZR Z).baseSet (covCC hS.choose) :=
  fun x hx => (mem_finInter.mp hx) hS.choose hS.choose_spec

/-- The continuous linear equivalence `ℂᵐ ≃ ℝ^{2m}` used by `localThomOfComplexCover`. -/
def covE {m : ℕ} : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
  Work.Gen.rifStd m

/-- The prescribed local classes of the finite cover: the explicit chart classes. -/
def covC {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ∀ (S : Finset (Fin (Fintype.card ι))), S.Nonempty →
      PieceCoh (covZR Z) (finInter (covU Z) S) (2 * m) :=
  fun S hS => (localThomOfChart (covZR Z) (2 * m) covE (covCC hS.choose)
    (finInter (covU Z) S) (covHsub Z S hS)).τ

/-- The openness of the pieces of the cover. -/
def covHU {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ∀ k, IsOpen (covU Z k) := fun k => (covZR Z).isOpen_baseSet (covCC k)

/-- The Thom isomorphism of the prescribed chart classes. -/
def covHc {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (j : ℕ),
      Function.Bijective (localThomMap (covZR Z) (2 * m) (finInter (covU Z) S)
        (covC Z S hS) j) := by
  intro S hS j
  dsimp only [covC]
  exact (localThomOfChart (covZR Z) (2 * m) covE (covCC hS.choose)
    (finInter (covU Z) S) (covHsub Z S hS)).isThom j

/-- The compatibility of the prescribed chart classes under restriction. -/
def covHcompat {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ∀ (S T : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (hT : T.Nonempty)
      (hST : S ⊆ T),
      (Work.Cohomology.pdCohMap (TopCat.of (covZR Z).TotalSpace) (zeroComplement (covZR Z))
        ((covZR Z).proj ⁻¹' finInter (covU Z) S) ((covZR Z).proj ⁻¹' finInter (covU Z) T)
        (Set.preimage_mono (finInter_mono hST)) (2 * m)).hom (covC Z S hS) = covC Z T hT := by
  intro S T hS hT hST
  have hn : 1 ≤ 2 * m := by omega
  have hZR : covZR Z = realification Z := rfl
  have hsub : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty),
      finInter (covU Z) S ⊆ (covZR Z).baseSet (covCC hS.choose) := covHsub Z
  have hsub' : finInter (covU Z) T ⊆ finInter (covU Z) S := finInter_mono hST
  have hTS : finInter (covU Z) T ⊆ (covZR Z).baseSet (covCC hS.choose) :=
    hsub'.trans (hsub S hS)
  have hSS : finInter (covU Z) S ⊆ (covZR Z).baseSet (covCC hS.choose) := hsub S hS
  have hW : finInter (covU Z) T ⊆ (covZR Z).baseSet (covCC hS.choose)
      ∩ (covZR Z).baseSet (covCC hT.choose) :=
    fun x hx => ⟨hTS hx, hsub T hT hx⟩
  have hW' : finInter (covU Z) T ⊆ (realification Z).baseSet (covCC hS.choose)
      ∩ (realification Z).baseSet (covCC hT.choose) := by
    rw [← hZR]
    exact hW
  have hcS : covC Z S hS
      = (localThomOfChart (covZR Z) (2 * m) covE (covCC hS.choose)
          (finInter (covU Z) S) hSS).τ := rfl
  have hcT : covC Z T hT
      = (localThomOfChart (covZR Z) (2 * m) covE (covCC hS.choose)
          (finInter (covU Z) T) hTS).τ := by
    dsimp only [covC]
    exact localThomOfChart_eq_of_det_pos (covZR Z) (2 * m) hn covE (covCC hS.choose)
      (covCC hT.choose) (finInter (covU Z) T) hTS (hsub T hT) hW
      (fun x => det_realification_coordChange_pos Z (covCC hS.choose) (covCC hT.choose) hW' x)
  rw [hcS, hcT]
  exact localThomOfChart_restrict (covZR Z) (2 * m) covE (covCC hS.choose)
    (finInter (covU Z) T) (finInter (covU Z) S) hTS hSS hsub'

/-- The low-degree vanishing of the cover. -/
def covHlow {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ∀ (A : Finset (Finset (Fin (Fintype.card ι)))),
      (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (PieceCoh (covZR Z) (⋃ S ∈ A, finInter (covU Z) S) (2 * m - 1)) :=
  fun A hA _ => subsingleton_PieceCoh_iUnion_finInter_clean (covZR Z) (Fintype.card ι)
    (covU Z) (covHU Z) (covCC) (fun k => subset_rfl) A hA (m := 2 * m - 1) (by
      rw [finrank_real_euclidean_complex m]
      omega)

/-- The `∃!`-statement whose witness is the Mayer–Vietoris class of the finite cover. -/
def covExists {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :=
  exists_unique_pieceClass (covZR Z) (2 * m) (by omega) (Fintype.card ι) (covU Z)
    (covHU Z) (covC Z) (covHc Z) (covHcompat hm Z) (covHlow hm Z)

/-- **The Mayer–Vietoris witness of `localThomOfComplexCover`**, as a top-level definition: the
`Classical.choose`d class over the union of the cover. -/
def covWitness {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    PieceCoh (covZR Z) (⋃ k, covU Z k) (2 * m) :=
  Classical.choose (covExists hm Z)

/-- The cover equality of `localThomOfComplexCover`: the cover is everything. -/
theorem covHcover {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (⋃ k, covU Z k) = Set.univ := by
  have hZR : covZR Z = realification Z := rfl
  have h1 : (⋃ k : Fin (Fintype.card ι), (covZR Z).baseSet (covCC k))
      = ⋃ i : ι, (covZR Z).baseSet i := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨covCC k, hk⟩
    · rintro ⟨i, hi⟩
      exact ⟨Fintype.equivFin ι i, by simpa only [covCC, Equiv.symm_apply_apply] using hi⟩
  have h2 : (⋃ i : ι, (covZR Z).baseSet i) = ⋃ i : ι, Z.baseSet i := by
    rw [hZR, realification_baseSet]
  rw [show (⋃ k, covU Z k)
    = ⋃ k : Fin (Fintype.card ι), (covZR Z).baseSet (covCC k) from rfl, h1, h2]
  exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩

/-- **The local data of `localThomOfComplexCover` is the cast of the top-level witness.** -/
theorem localThomOfComplexCover_tau_eq {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (localThomOfComplexCover hm Z).τ = covHcover Z ▸ covWitness hm Z := rfl

/-- **The restriction property of `covWitness`**: its restriction to the piece of a nonempty
finite family `S` is the prescribed chart class `covC`. -/
theorem covWitness_restrict {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) :
    (Work.Cohomology.pdCohMap (TopCat.of (covZR Z).TotalSpace) (zeroComplement (covZR Z))
      ((covZR Z).proj ⁻¹' (⋃ k, covU Z k)) ((covZR Z).proj ⁻¹' (finInter (covU Z) S))
      (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom (covWitness hm Z)
      = covC Z S hS :=
  (Classical.choose_spec (covExists hm Z)).1.2 S hS

/-- **The local Thom isomorphism of `covWitness`.** -/
theorem covWitness_isThom {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (j : ℕ) :
    Function.Bijective (localThomMap (covZR Z) (2 * m) (⋃ k, covU Z k)
      (covWitness hm Z) j) :=
  (Classical.choose_spec (covExists hm Z)).1.1 j

end

end Work.Thom
