import Mathlib
import Submission.Work.Thom.thomClass_of_complex_fintype
import Submission.Work.Thom.exists_unique_pieceClass
import Submission.Work.Thom.exists_unique_thomClassOfLocalThomUniv
import Submission.Work.Gen.RifStd

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# The canonical Thom class of the realification of a complex bundle

`Work.Thom.thomClass_of_complex_fintype` proves `Nonempty (ThomClass (realification Z) (2 * m))`,
and `Work.Thom.thomClassRank` extracted a witness by `Classical.choice`.  That choice is *not*
natural: two bundles (or a bundle and its pullback) receive independently chosen Thom classes, whose
Euler classes differ by a unit of `H⁰`.

This module replaces the choice by a **construction**:

* every step of the proof of `thomClass_of_complex_fintype` is a *definition*
  (`localThomOfChart` is a `def`; the local data over the intersections is its `τ`; the
  compatibility, the low-degree vanishing and the cover are lemmas);
* the one genuinely existential step — the Mayer–Vietoris witness over the union of the cover — is
  replaced by `Classical.choose` of the **`∃!`**-statement `Work.Thom.exists_unique_pieceClass`
  (whose uniqueness is `Work.Thom.pdCohMap_finInter_eq_zero`), and is therefore *invariant under the
  proof*: a function of the input data alone;
* the final passage from the local data over `Set.univ` to a `ThomClass` is
  `Classical.choose` of the **`∃!`**-statement
  `Work.Thom.exists_unique_thomClassOfLocalThomUniv`, whose witness is pinned down by the equation
  `(relCohMap …).hom τ = T.τ` (unique because `relCohMap` along a homeomorphism of pairs is a
  bijection).

The result, `Work.Thom.thomClassOf`, is thus a *function* of the complex bundle: the surviving
`Classical.choose`s are canonical.  `Work.Thom.thomClassRank` of `Submission/Work/Thom/chernClass.lean`
is defined to be `thomClassOf`, so the top Chern class — and with it `p₁`, `p₂`, `p1Tangent'` — is
canonical up to equivalence of the construction (see `README.md` ADDENDUM 21).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- **The canonical local Thom data over the whole base** for the realification of a complex bundle
of rank `m ≥ 1`, built by the finite-cover Mayer–Vietoris induction of
`Work.Thom.thomClass_of_complex_fintype`, with the induction's witness taken from the
**uniqueness**-backed `Work.Thom.exists_unique_pieceClass`. -/
noncomputable def localThomOfComplexCover [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    LocalThom (realification Z) (2 * m) Set.univ := by
  classical
  have hn : 1 ≤ 2 * m := by omega
  let ZR : RealBundle B (EuclideanSpace ℂ (Fin m)) ι := realification Z
  have hZR : ZR = realification Z := rfl
  -- THE CURE (see `Submission/Work/Gen/RifStd.lean`, `Submission/Work/Whitney/_tcm/FINDING.md`):
  -- the chart linear equivalence is the *canonical, sum-compatible* realification
  -- `Work.Gen.rifStd` (interleaved real and imaginary parts), not the opaque
  -- `ContinuousLinearEquiv.ofFinrankEq`, whose orientation sign would be an independent free
  -- parameter for each rank.  The term must be *the same* as `Work.Thom.covE`
  -- (`Submission/Work/Thom/CovDefs.lean`), which the `rfl`-proof
  -- `Work.Thom.localThomOfComplexCover_tau_eq` relies on.
  let e : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
    Work.Gen.rifStd m
  let cc : Fin (Fintype.card ι) → ι := fun k => (Fintype.equivFin ι).symm k
  let U : Fin (Fintype.card ι) → Set B := fun k => ZR.baseSet (cc k)
  have hU : ∀ k, IsOpen (U k) := fun k => ZR.isOpen_baseSet (cc k)
  have hsub : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty),
      finInter U S ⊆ ZR.baseSet (cc hS.choose) := fun S hS x hx =>
    (mem_finInter.mp hx) hS.choose hS.choose_spec
  let c : ∀ (S : Finset (Fin (Fintype.card ι))), S.Nonempty →
      PieceCoh ZR (finInter U S) (2 * m) := fun S hS =>
    (localThomOfChart ZR (2 * m) e (cc hS.choose) (finInter U S) (hsub S hS)).τ
  have hc : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (j : ℕ),
      Function.Bijective (localThomMap ZR (2 * m) (finInter U S) (c S hS) j) := by
    intro S hS j
    dsimp only [c]
    exact (localThomOfChart ZR (2 * m) e (cc hS.choose)
      (finInter U S) (hsub S hS)).isThom j
  have hcompat : ∀ (S T : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (hT : T.Nonempty)
      (hST : S ⊆ T),
      (Work.Cohomology.pdCohMap (TopCat.of ZR.TotalSpace) (zeroComplement ZR)
        (ZR.proj ⁻¹' finInter U S) (ZR.proj ⁻¹' finInter U T)
        (Set.preimage_mono (finInter_mono hST)) (2 * m)).hom (c S hS) = c T hT := by
    intro S T hS hT hST
    have hsub' : finInter U T ⊆ finInter U S := finInter_mono hST
    have hTS : finInter U T ⊆ ZR.baseSet (cc hS.choose) := hsub'.trans (hsub S hS)
    have hSS : finInter U S ⊆ ZR.baseSet (cc hS.choose) := hsub S hS
    have hW : finInter U T ⊆ ZR.baseSet (cc hS.choose) ∩ ZR.baseSet (cc hT.choose) :=
      fun x hx => ⟨hTS hx, hsub T hT hx⟩
    have hW' : finInter U T ⊆ (realification Z).baseSet (cc hS.choose)
        ∩ (realification Z).baseSet (cc hT.choose) := by
      rw [← hZR]
      exact hW
    have hcS : c S hS
        = (localThomOfChart ZR (2 * m) e (cc hS.choose) (finInter U S) hSS).τ := by
      dsimp only [c]
    have hcT : c T hT
        = (localThomOfChart ZR (2 * m) e (cc hS.choose) (finInter U T) hTS).τ := by
      dsimp only [c]
      exact localThomOfChart_eq_of_det_pos ZR (2 * m) hn e (cc hS.choose) (cc hT.choose)
        (finInter U T) hTS (hsub T hT) hW
        (fun x => det_realification_coordChange_pos Z (cc hS.choose) (cc hT.choose) hW' x)
    rw [hcS, hcT]
    exact localThomOfChart_restrict ZR (2 * m) e (cc hS.choose) (finInter U T) (finInter U S)
      hTS hSS hsub'
  have hlow : ∀ (A : Finset (Finset (Fin (Fintype.card ι)))),
      (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (PieceCoh ZR (⋃ S ∈ A, finInter U S) (2 * m - 1)) :=
    fun A hA _ => subsingleton_PieceCoh_iUnion_finInter_clean ZR (Fintype.card ι) U hU cc
      (fun k => subset_rfl) A hA (m := 2 * m - 1) (by
        rw [finrank_real_euclidean_complex m]
        omega)
  have hcover : (⋃ k, U k) = Set.univ := by
    have h1 : (⋃ k : Fin (Fintype.card ι), ZR.baseSet (cc k)) = ⋃ i : ι, ZR.baseSet i := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨cc k, hk⟩
      · rintro ⟨i, hi⟩
        exact ⟨Fintype.equivFin ι i, by simpa only [cc, Equiv.symm_apply_apply] using hi⟩
    have h2 : (⋃ i : ι, ZR.baseSet i) = ⋃ i : ι, Z.baseSet i := by
      rw [hZR, realification_baseSet]
    rw [show (⋃ k, U k) = ⋃ k : Fin (Fintype.card ι), ZR.baseSet (cc k) from rfl, h1, h2]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩
  let cU := Classical.choose
    (exists_unique_pieceClass ZR (2 * m) hn (Fintype.card ι) U hU c hc hcompat hlow)
  have hcU : ∀ j : ℕ,
      Function.Bijective (localThomMap ZR (2 * m) (⋃ k, U k) cU j) := by
    have h := (Classical.choose_spec
      (exists_unique_pieceClass ZR (2 * m) hn (Fintype.card ι) U hU c hc hcompat hlow)).1
    simp only [] at h
    exact h.1
  exact ⟨hcover ▸ cU, fun j => bijective_localThomMap_cast ZR hcover cU j (hcU j)⟩

/-- **The canonical Thom class of the realification of a complex bundle of rank `m ≥ 1`**: the
uniqueness-backed choice from the local data `Work.Thom.localThomOfComplexCover`. -/
noncomputable def thomClassOf [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ThomClass (realification Z) (2 * m) :=
  Classical.choose
    (exists_unique_thomClassOfLocalThomUniv (realification Z) (localThomOfComplexCover hm Z))

/-- The defining equation of `Work.Thom.thomClassOf`: it is the (unique) Thom class whose
restriction to the piece over `Set.univ` is the local data of
`Work.Thom.localThomOfComplexCover`. -/
theorem thomClassOf_spec [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((realification Z).proj ⁻¹' (Set.univ : Set B)), (realification Z).TotalSpace))
      {y : ↥((realification Z).proj ⁻¹' (Set.univ : Set B)) |
        (y : (realification Z).TotalSpace) ∈ zeroComplement (realification Z)}
      (zeroComplement (realification Z)) (fun y hy => hy) ℤ (2 * m)).hom
      (thomClassOf hm Z).τ
    = (localThomOfComplexCover hm Z).τ :=
  (Classical.choose_spec
    (exists_unique_thomClassOfLocalThomUniv (realification Z)
      (localThomOfComplexCover hm Z))).1

end

end Work.Thom
