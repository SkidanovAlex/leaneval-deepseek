import Mathlib
import Submission.Work.Thom.CovDefs
import Submission.Work.Thom.localThomOfChart_realif_comap
import Submission.Work.Thom.pdCohMap_finInter_eq_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Naturality of the local Mayer–Vietoris class of `localThomOfComplexCover`

This module proves that the Mayer–Vietoris witness `Work.Thom.covWitness` of the finite-cover
construction is natural under a pullback of complex gluing data along a continuous map, and
deduces from it the naturality of the canonical Thom class
(`Work.Thom.thomClassOf_comap`).

The proof has three layers:

* the cover transforms as `covU (bundleComap Z f) k = f ⁻¹' covU Z k`, so its finite intersections
  are the preimages of those of `Z`;
* the *prescribed* chart classes are natural under the pullback
  (`Work.Thom.localThomOfChart_realif_comap`);
* the witness is separated on the pieces: `Work.Thom.pdCohMap_finInter_eq_zero` says that a class
  whose restriction to every piece `finInter (covU · ) S` vanishes is zero, and the restriction of
  the pullback of `covWitness hm Z` to such a piece is the pullback of the restriction of
  `covWitness hm Z` — which, by the characterising property of the witness, is the prescribed chart
  class `covC Z S hS`, whose pullback is `covC (bundleComap Z f) S hS`, again by the characterising
  property.  No bijectivity of any transfer is needed.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {B' : Type} [TopologicalSpace B']
variable {ι : Type} [Fintype ι]

/-- The cover of the pullback bundle is the preimage of the cover of the original bundle. -/
theorem covU_comap {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (k : Fin (Fintype.card ι)) :
    covU (bundleComap Z f) k = f ⁻¹' covU Z k := by
  simp only [covU, covZR, realification_bundleComap, bundleComap_baseSet]

/-- The finite intersections of the pullback cover are the preimages of those of the cover. -/
theorem finInter_covU_comap {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (S : Finset (Fin (Fintype.card ι))) :
    finInter (covU (bundleComap Z f)) S = f ⁻¹' finInter (covU Z) S := by
  ext x
  rw [mem_finInter, Set.mem_preimage, mem_finInter]
  constructor
  · intro h k hk
    have hk' := h k hk
    rw [covU_comap Z f k] at hk'
    exact hk'
  · intro h k hk
    rw [covU_comap Z f k]
    exact h k hk

/-- The membership of a point of the union of the pullback cover in the union of the cover. -/
theorem covHfUnion {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) :
    ∀ x ∈ ⋃ k, covU (bundleComap Z f) k, f x ∈ ⋃ k, covU Z k := by
  intro x hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨k, by rw [covU_comap Z f k] at hk; exact hk⟩

/-- The membership of a point of an intersection of the pullback cover in the intersection. -/
theorem covHfInter {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (S : Finset (Fin (Fintype.card ι))) :
    ∀ x ∈ finInter (covU (bundleComap Z f)) S, f x ∈ finInter (covU Z) S := by
  intro x hx
  rw [finInter_covU_comap Z f S] at hx
  exact hx



/-! ## The two characterising properties, in `relCohMap` form -/

/-- The restriction of `covWitness` to a piece, in the `relCohMap` language. -/
theorem pieceIncl_covWitness {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty)
    (w : RelCoh ℤ (2 * m) ↥((realification Z).proj ⁻¹' (⋃ k, covU Z k))
      (pieceZero (realification Z) (⋃ k, covU Z k))) (hw : w = covWitness hm Z) :
    (relCohMap (pieceIncl (realification Z) (finInter (covU Z) S) (⋃ k, covU Z k)
        (finInter_nonempty_subset_iUnion hS))
      (pieceZero (realification Z) (finInter (covU Z) S))
      (pieceZero (realification Z) (⋃ k, covU Z k))
      (pieceIncl_mem (realification Z) (finInter (covU Z) S) (⋃ k, covU Z k)
        (finInter_nonempty_subset_iUnion hS)) ℤ (2 * m)).hom w
      = covC Z S hS := by
  subst hw
  rw [← pdCohMap_eq_relCohMap (realification Z) (finInter (covU Z) S) (⋃ k, covU Z k)
    (finInter_nonempty_subset_iUnion hS) (2 * m)]
  exact covWitness_restrict hm Z S hS

/-- The pullback of the prescribed chart class is the prescribed chart class of the pullback. -/
theorem pieceMapR_covC {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty)
    (cS : RelCoh ℤ (2 * m) ↥((realification Z).proj ⁻¹' (finInter (covU Z) S))
      (pieceZero (realification Z) (finInter (covU Z) S))) (hcS : cS = covC Z S hS) :
    (relCohMap (pieceMapR Z f (covHfInter Z f S))
      (pieceZero (realification (bundleComap Z f)) (finInter (covU (bundleComap Z f)) S))
      (pieceZero (realification Z) (finInter (covU Z) S))
      (pieceMapR_mem Z f (covHfInter Z f S)) ℤ (2 * m)).hom cS
      = covC (bundleComap Z f) S hS := by
  subst hcS
  exact localThomOfChart_realif_comap Z f covE (covCC hS.choose) (covHsub Z S hS)
    (covHsub (bundleComap Z f) S hS) (covHfInter Z f S)

/-! ## Naturality of the witness -/

/-- **Naturality of the Mayer–Vietoris witness under pullback.** -/
theorem covWitness_comap {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    (relCohMap (pieceMapR Z f (covHfUnion Z f))
      (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
      (pieceZero (realification Z) (⋃ k, covU Z k))
      (pieceMapR_mem Z f (covHfUnion Z f)) ℤ (2 * m)).hom (covWitness hm Z)
      = covWitness hm (bundleComap Z f) := by
  let w : RelCoh ℤ (2 * m) ↥((realification Z).proj ⁻¹' (⋃ k, covU Z k))
      (pieceZero (realification Z) (⋃ k, covU Z k)) := covWitness hm Z
  let w' : RelCoh ℤ (2 * m) ↥((realification (bundleComap Z f)).proj ⁻¹'
      (⋃ k, covU (bundleComap Z f) k))
      (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k)) :=
    covWitness hm (bundleComap Z f)
  have hper : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty),
      (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom
        ((relCohMap (pieceMapR Z f (covHfUnion Z f))
          (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
          (pieceZero (realification Z) (⋃ k, covU Z k))
          (pieceMapR_mem Z f (covHfUnion Z f)) ℤ (2 * m)).hom w)
      = covC (bundleComap Z f) S hS := by
    intro S hS
    let A : Set ↥((realification (bundleComap Z f)).proj ⁻¹'
        (finInter (covU (bundleComap Z f)) S)) :=
      pieceZero (realification (bundleComap Z f)) (finInter (covU (bundleComap Z f)) S)
    let Bs : Set ↥((realification Z).proj ⁻¹' (finInter (covU Z) S)) :=
      pieceZero (realification Z) (finInter (covU Z) S)
    let Bp : Set ↥((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k)) :=
      pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k)
    let C : Set ↥((realification Z).proj ⁻¹' (⋃ k, covU Z k)) :=
      pieceZero (realification Z) (⋃ k, covU Z k)
    let cS : RelCoh ℤ (2 * m) ↥((realification Z).proj ⁻¹' (finInter (covU Z) S)) Bs :=
      covC Z S hS
    let cS' : RelCoh ℤ (2 * m)
        ↥((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S)) A :=
      covC (bundleComap Z f) S hS
    let pmW : C(↥((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k)),
        ↥((realification Z).proj ⁻¹' (⋃ k, covU Z k))) := pieceMapR Z f (covHfUnion Z f)
    let pmS : C(↥((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S)),
        ↥((realification Z).proj ⁻¹' (finInter (covU Z) S))) := pieceMapR Z f (covHfInter Z f S)
    let inclW' : C(↥((realification (bundleComap Z f)).proj ⁻¹'
          (finInter (covU (bundleComap Z f)) S)),
        ↥((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))) :=
      pieceIncl (realification (bundleComap Z f)) (finInter (covU (bundleComap Z f)) S)
        (⋃ k, covU (bundleComap Z f) k) (finInter_nonempty_subset_iUnion hS)
    let inclW : C(↥((realification Z).proj ⁻¹' (finInter (covU Z) S)),
        ↥((realification Z).proj ⁻¹' (⋃ k, covU Z k))) :=
      pieceIncl (realification Z) (finInter (covU Z) S) (⋃ k, covU Z k)
        (finInter_nonempty_subset_iUnion hS)
    have hmemW : ∀ x ∈ Bp, pmW x ∈ C := pieceMapR_mem Z f (covHfUnion Z f)
    have hmemS : ∀ x ∈ A, pmS x ∈ Bs := pieceMapR_mem Z f (covHfInter Z f S)
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
      simp only [pmW, pmS, inclW', inclW, ContinuousMap.comp_apply, pieceIncl_apply,
        pieceMapR_apply]
    -- the map from `A`-pieces to `C`-pieces, the two ways
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
      pieceIncl_covWitness hm Z S hS w rfl
    have h5 : (relCohMap pmS A Bs hmemS ℤ (2 * m)).hom cS = cS' :=
      pieceMapR_covC Z f S hS cS rfl
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
    rw [pdCohMap_eq_relCohMap (realification (bundleComap Z f))
      (finInter (covU (bundleComap Z f)) S) (⋃ k, covU (bundleComap Z f) k)
      (finInter_nonempty_subset_iUnion hS) (2 * m)]
    exact h1.trans (h2.trans (h3.trans (hstep.trans h5)))
  refine sub_eq_zero.mp ?_
  apply pdCohMap_finInter_eq_zero (realification (bundleComap Z f)) (2 * m)
    (Fintype.card ι) (covU (bundleComap Z f)) (covHU (bundleComap Z f))
    (covHlow hm (bundleComap Z f))
  intro S hS
  rw [map_sub,
    show (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom
        ((relCohMap (pieceMapR Z f (covHfUnion Z f))
          (pieceZero (realification (bundleComap Z f)) (⋃ k, covU (bundleComap Z f) k))
          (pieceZero (realification Z) (⋃ k, covU Z k))
          (pieceMapR_mem Z f (covHfUnion Z f)) ℤ (2 * m)).hom w)
        = covC (bundleComap Z f) S hS from hper S hS,
    show (Work.Cohomology.pdCohMap (TopCat.of (realification (bundleComap Z f)).TotalSpace)
        (zeroComplement (realification (bundleComap Z f)))
        ((realification (bundleComap Z f)).proj ⁻¹' (⋃ k, covU (bundleComap Z f) k))
        ((realification (bundleComap Z f)).proj ⁻¹' (finInter (covU (bundleComap Z f)) S))
        (Set.preimage_mono (finInter_nonempty_subset_iUnion hS)) (2 * m)).hom w'
        = covC (bundleComap Z f) S hS from covWitness_restrict hm (bundleComap Z f) S hS,
    sub_self]

/-! ## The cast from the union of the cover to the whole base -/

/-- **Casting the witness from the union of the cover to the whole base commutes with the pullback
along the map of the total spaces.**  With `V` and `V'` the unions of the two covers (both equal to
`Set.univ`), the pullback of the cast of `cU` is the cast of the pullback of `cU`. -/
theorem pieceMapR_cast_comm {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    {V : Set B} {V' : Set B'} (hVf : ∀ x ∈ V', f x ∈ V)
    (hV : V = Set.univ) (hV' : V' = Set.univ)
    (cU : Work.Thom.PieceCoh (realification Z) V (2 * m)) :
    (relCohMap (pieceMapR Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial))
      (pieceZero (realification (bundleComap Z f)) Set.univ)
      (pieceZero (realification Z) Set.univ)
      (pieceMapR_mem Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial)) ℤ (2 * m)).hom
        (hV ▸ cU)
      = hV' ▸ ((relCohMap (pieceMapR Z f hVf)
          (pieceZero (realification (bundleComap Z f)) V')
          (pieceZero (realification Z) V)
          (pieceMapR_mem Z f hVf) ℤ (2 * m)).hom cU) := by
  subst hV
  subst hV'
  rfl

end

end Work.Thom
