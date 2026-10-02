import Mathlib
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.CovDefs
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.localThomOfChart_realif_comap
import Submission.Work.Thom.exists_unique_pieceClass
import Submission.Work.Thom.ChartOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} [Fintype ι]

/-! ## Naturality of the Mayer--Vietoris witness of `localThomOfComplexCover`

The Mayer--Vietoris witness `Work.Thom.covWitness` of the finite-cover construction lives over the
union `⋃ k, covU Z k` of the cover of `B` by the base sets of `Z`.  Its naturality under a pullback
`bundleComap Z f` along a continuous map `f` is proved here, independently of
`Submission/Work/Thom/CovComap.lean`: the witness is separated on the pieces of the cover by
`Work.Thom.pdCohMap_finInter_eq_zero`, and on each piece the computation is the naturality of the
prescribed chart classes (`Work.Thom.localThomOfChart_realif_comap`) together with the
compatibility of the restriction with the pullback.
-/

/-- The cover of the pullback bundle is the preimage of the cover of the original bundle. -/
theorem ltcc_covU_comap {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    (k : Fin (Fintype.card ι)) :
    covU (bundleComap Z f) k = f ⁻¹' covU Z k := by
  simp only [covU, covZR, realification_bundleComap, bundleComap_baseSet]

/-- The finite intersections of the pullback cover are the preimages of those of the cover. -/
theorem ltcc_finInter_comap {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    (S : Finset (Fin (Fintype.card ι))) :
    finInter (covU (bundleComap Z f)) S = f ⁻¹' finInter (covU Z) S := by
  ext x
  rw [mem_finInter, Set.mem_preimage, mem_finInter]
  constructor
  · intro h k hk
    have hk' := h k hk
    rw [ltcc_covU_comap Z f k] at hk'
    exact hk'
  · intro h k hk
    rw [ltcc_covU_comap Z f k]
    exact h k hk

/-- The membership of a point of the union of the pullback cover in the union of the cover. -/
theorem ltcc_covHfUnion {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    ∀ x ∈ ⋃ k, covU (bundleComap Z f) k, f x ∈ ⋃ k, covU Z k := by
  intro x hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨k, by rw [ltcc_covU_comap Z f k] at hk; exact hk⟩

/-- The membership of a point of an intersection of the pullback cover in the intersection. -/
theorem ltcc_covHfInter {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    (S : Finset (Fin (Fintype.card ι))) :
    ∀ x ∈ finInter (covU (bundleComap Z f)) S, f x ∈ finInter (covU Z) S := by
  intro x hx
  rw [ltcc_finInter_comap Z f S] at hx
  exact hx

/-- **Naturality of the Mayer--Vietoris witness under pullback.** -/
theorem ltcc_covWitness_comap {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    (relCohMap (pieceMapR Z f (ltcc_covHfUnion Z f))
      (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
      (pieceZero (realification Z) (⋃ k, covU Z k))
      (fun _ hp => hp) ℤ (2 * m)).hom (covWitness hm Z)
      = covWitness hm (bundleComap Z f) := by
  let w : RelCoh ℤ (2 * m) ↥((realification Z).proj ⁻¹' (⋃ k, covU Z k))
      (pieceZero (realification Z) (⋃ k, covU Z k)) := covWitness hm Z
  let w' : RelCoh ℤ (2 * m) ↥((realification (bundleComap Z f)).proj ⁻¹'
      (⋃ k, covU (bundleComap Z f) k))
      (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k)) :=
    covWitness hm (bundleComap Z f)
  change (relCohMap (pieceMapR Z f (ltcc_covHfUnion Z f))
      (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
      (pieceZero (realification Z) (⋃ k, covU Z k))
      (fun _ hp => hp) ℤ (2 * m)).hom w = w'
  have hper : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty),
      (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom
        ((relCohMap (pieceMapR Z f (ltcc_covHfUnion Z f))
          (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
          (pieceZero (realification Z) (⋃ k, covU Z k))
          (fun _ hp => hp) ℤ (2 * m)).hom w)
      = covC (bundleComap Z f) S hS := by
    intro S hS
    let A : Set ↥((realification (bundleComap Z f)).proj ⁻¹'
        finInter (covU (bundleComap Z f)) S) :=
      pieceZero (realification (bundleComap Z f)) (finInter (covU (bundleComap Z f)) S)
    let Bs : Set ↥((realification Z).proj ⁻¹' finInter (covU Z) S) :=
      pieceZero (realification Z) (finInter (covU Z) S)
    let Bp : Set ↥((realification (bundleComap Z f)).proj ⁻¹' ⋃ k, covU (bundleComap Z f) k) :=
      pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k)
    let C : Set ↥((realification Z).proj ⁻¹' ⋃ k, covU Z k) :=
      pieceZero (realification Z) (⋃ k, covU Z k)
    let cS : RelCoh ℤ (2 * m) ↥((realification Z).proj ⁻¹' finInter (covU Z) S)
        (pieceZero (realification Z) (finInter (covU Z) S)) := covC Z S hS
    let cS' : RelCoh ℤ (2 * m)
        ↥((realification (bundleComap Z f)).proj ⁻¹' finInter (covU (bundleComap Z f)) S)
        (pieceZero (realification (bundleComap Z f)) (finInter (covU (bundleComap Z f)) S)) :=
      covC (bundleComap Z f) S hS
    let pmW : C(↥((realification (bundleComap Z f)).proj ⁻¹'
          (⋃ k, covU (bundleComap Z f) k)),
        ↥((realification Z).proj ⁻¹' (⋃ k, covU Z k))) :=
      pieceMapR Z f (ltcc_covHfUnion Z f)
    let pmS : C(↥((realification (bundleComap Z f)).proj ⁻¹'
          (finInter (covU (bundleComap Z f)) S)),
        ↥((realification Z).proj ⁻¹' (finInter (covU Z) S))) :=
      pieceMapR Z f (ltcc_covHfInter Z f S)
    let inclW' : C(↥((realification (bundleComap Z f)).proj ⁻¹'
          (finInter (covU (bundleComap Z f)) S)),
        ↥((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))) :=
      pieceIncl (realification (bundleComap Z f)) (finInter (covU (bundleComap Z f)) S)
        (⋃ k, covU (bundleComap Z f) k) (finInter_nonempty_subset_iUnion hS)
    let inclW : C(↥((realification Z).proj ⁻¹' (finInter (covU Z) S)),
        ↥((realification Z).proj ⁻¹' (⋃ k, covU Z k))) :=
      pieceIncl (realification Z) (finInter (covU Z) S) (⋃ k, covU Z k)
        (finInter_nonempty_subset_iUnion hS)
    have hmemW : ∀ x ∈ Bp, pmW x ∈ C := pieceMapR_mem Z f (ltcc_covHfUnion Z f)
    have hmemS : ∀ x ∈ A, pmS x ∈ Bs := pieceMapR_mem Z f (ltcc_covHfInter Z f S)
    have hmemI' : ∀ x ∈ A, inclW' x ∈ Bp :=
      pieceIncl_mem (realification (bundleComap Z f)) (finInter (covU (bundleComap Z f)) S)
        (⋃ k, covU (bundleComap Z f) k) (finInter_nonempty_subset_iUnion hS)
    have hmemI : ∀ x ∈ Bs, inclW x ∈ C :=
      pieceIncl_mem (realification Z) (finInter (covU Z) S) (⋃ k, covU Z k)
        (finInter_nonempty_subset_iUnion hS)
    have hmap : pmW.comp inclW' = inclW.comp pmS := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      rfl
    have h1 : (relCohMap inclW' A Bp hmemI' ℤ (2 * m)).hom
          ((relCohMap pmW Bp C hmemW ℤ (2 * m)).hom w)
        = (relCohMap (pmW.comp inclW') A C (fun _ hp => hp) ℤ (2 * m)).hom w :=
      relCohMap_compA_apply A Bp C inclW' pmW hmemI' hmemW (fun _ hp => hp) ℤ (2 * m) w
    have hmor : relCohMap (pmW.comp inclW') A C (fun _ hp => hp) ℤ (2 * m)
        = relCohMap (inclW.comp pmS) A C (fun _ hp => hp) ℤ (2 * m) :=
      relCohMap_congrA A C hmap (fun _ hp => hp) (fun _ hp => hp) ℤ (2 * m)
    have h2 : (relCohMap (pmW.comp inclW') A C (fun _ hp => hp) ℤ (2 * m)).hom w
        = (relCohMap (inclW.comp pmS) A C (fun _ hp => hp) ℤ (2 * m)).hom w :=
      congrArg (fun φ => φ.hom w) hmor
    have h3 : (relCohMap (inclW.comp pmS) A C (fun _ hp => hp) ℤ (2 * m)).hom w
        = (relCohMap pmS A Bs hmemS ℤ (2 * m)).hom
            ((relCohMap inclW Bs C hmemI ℤ (2 * m)).hom w) :=
      (relCohMap_compA_apply A Bs C pmS inclW hmemS hmemI (fun _ hp => hp) ℤ (2 * m) w).symm
    have h4 : (relCohMap inclW Bs C hmemI ℤ (2 * m)).hom w = cS :=
      covWitness_restrict hm Z S hS
    have h5 : (relCohMap pmS A Bs hmemS ℤ (2 * m)).hom cS = cS' :=
      localThomOfChart_realif_comap Z f covE (covCC hS.choose) (covHsub Z S hS)
        (covHsub (bundleComap Z f) S hS) (ltcc_covHfInter Z f S)
    have hstep : (relCohMap pmS A Bs hmemS ℤ (2 * m)).hom
          ((relCohMap inclW Bs C hmemI ℤ (2 * m)).hom w)
        = (relCohMap pmS A Bs hmemS ℤ (2 * m)).hom cS :=
      congrArg (fun z => (relCohMap pmS A Bs hmemS ℤ (2 * m)).hom z) h4
    show (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom
        ((relCohMap pmW Bp C hmemW ℤ (2 * m)).hom w) = cS'
    exact h1.trans (h2.trans (h3.trans (hstep.trans h5)))
  have hzero : (relCohMap (pieceMapR Z f (ltcc_covHfUnion Z f))
      (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
      (pieceZero (realification Z) (⋃ k, covU Z k))
      (fun _ hp => hp) ℤ (2 * m)).hom w - w' = 0 := by
    apply pdCohMap_finInter_eq_zero (realification (bundleComap Z f)) (2 * m)
      (Fintype.card ι) (covU (bundleComap Z f)) (covHU (bundleComap Z f))
      (covHlow hm (bundleComap Z f))
    intro S hS
    have hA : (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom
        ((relCohMap (pieceMapR Z f (ltcc_covHfUnion Z f))
          (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
          (pieceZero (realification Z) (⋃ k, covU Z k))
          (fun _ hp => hp) ℤ (2 * m)).hom w)
        = covC (bundleComap Z f) S hS := hper S hS
    have hB : (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom w'
        = covC (bundleComap Z f) S hS := covWitness_restrict hm (bundleComap Z f) S hS
    have hAB : (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom
        ((relCohMap (pieceMapR Z f (ltcc_covHfUnion Z f))
          (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
          (pieceZero (realification Z) (⋃ k, covU Z k))
          (fun _ hp => hp) ℤ (2 * m)).hom w)
        = (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom w' :=
      hA.trans hB.symm
    rw [map_sub, hAB, sub_self]
  exact sub_eq_zero.mp hzero

/-- **Casting the base set of the local data to `Set.univ` commutes with the pullback.**  The
Mayer--Vietoris witness lives over the union `⋃ k, covU Z k` of the cover, while the local Thom data
of `localThomOfComplexCover` lives over `Set.univ`; the two descriptions differ only by the
transport along the equality of the cover with the whole base. -/
theorem pieceMapR_relCohMap_cast_univ {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    {V : Set B} {V' : Set B'} (hV : V = Set.univ) (hV' : V' = Set.univ)
    (hVf : ∀ x ∈ V', f x ∈ V) (c : PieceCoh (realification Z) V (2 * m)) :
    (relCohMap (pieceMapR Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial))
      (pieceZero (realification (bundleComap Z f)) Set.univ)
      (pieceZero (realification Z) Set.univ)
      (pieceMapR_mem Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial)) ℤ (2 * m)).hom
        (hV ▸ c)
      = hV' ▸ (relCohMap (pieceMapR Z f hVf)
          (pieceZero (realification (bundleComap Z f)) V')
          (pieceZero (realification Z) V)
          (fun _ hp => hp) ℤ (2 * m)).hom c := by
  subst hV
  subst hV'
  rfl

end

theorem localThomOfComplexCover_comap {m : ℕ} {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] {ι : Type} [Fintype ι] (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    (Work.Thom.relCohMap
      (Work.Thom.pieceMapR Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial))
      (Work.Thom.pieceZero (Work.Thom.realification (Work.Thom.bundleComap Z f)) Set.univ)
      (Work.Thom.pieceZero (Work.Thom.realification Z) Set.univ)
      (Work.Thom.pieceMapR_mem Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial))
      ℤ (2 * m)).hom
        (Work.Thom.localThomOfComplexCover hm Z).τ
      = (Work.Thom.localThomOfComplexCover hm (Work.Thom.bundleComap Z f)).τ := by
  have hcast := pieceMapR_relCohMap_cast_univ (Z := Z) (f := f)
    (V := ⋃ k, covU Z k) (V' := ⋃ k, covU (bundleComap Z f) k)
    (covHcover Z) (covHcover (bundleComap Z f)) (ltcc_covHfUnion Z f) (covWitness hm Z)
  rw [localThomOfComplexCover_tau_eq hm Z,
    localThomOfComplexCover_tau_eq hm (bundleComap Z f)]
  rw [hcast]
  rw [ltcc_covWitness_comap hm Z f]

end Work.Thom
