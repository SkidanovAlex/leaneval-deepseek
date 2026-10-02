import Mathlib
import Submission.Work.Thom.thomClass_of_finite_cover
import Submission.Work.Thom.complexDet
import Submission.Work.Thom.realification
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.complexBundleAux
import Submission.Work.Thom.ATools
import Submission.Work.Thom.subsingleton_PieceCoh_iUnion_finInter_clean
import Submission.Work.Thom.nonempty_thomClass_of_localThom_univ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- **The real determinant of a transition function of the realification of a complex bundle is
positive.**  The transition function `Z.coordChange i j x` is `ℂ`-linear and bijective on
`baseSet i ∩ baseSet j`, so its real determinant is `|det_ℂ|² > 0`
(`Work.Thom.det_restrictScalars_pos`, `Work.Thom.det_restrictScalars_eq_normSq`). -/
theorem det_realification_coordChange_pos {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i j : ι) {W : Set B}
    (hW : W ⊆ (realification Z).baseSet i ∩ (realification Z).baseSet j)
    (x : ↥W) : 0 < LinearMap.det ((realification Z).coordChange i j (x : B)).toLinearMap := by
  have hx : (x : B) ∈ Z.baseSet i ∩ Z.baseSet j := by
    have h := hW x.2
    rw [realification_baseSet] at h
    exact h
  have hcoord : (realification Z).coordChange i j (x : B)
      = (Z.coordChange i j (x : B)).restrictScalars ℝ := by
    ext v
    rw [realification_coordChange]
    rfl
  rw [hcoord]
  exact det_restrictScalars_pos (coordChange_bijective Z i j hx)

/-- **The Thom class of the realification of a complex vector bundle of finite gluing-data cover.**
Any complex vector bundle `Z` of rank `m ≥ 1` over a topological space, presented by gluing data
over a *finite* index type `ι`, is canonically oriented (its transition functions are `ℂ`-linear,
hence have positive real determinant), so its realification of rank `2 * m` carries an integral Thom
class.  This generalises `Work.Thom.nonempty_thomClass_of_complex_cover` (the two-chart case) to an
arbitrary finite cover, which is what the tower of tautological quotients needs at every stage.

Proof route: the cover of `B` by the pieces `Z.baseSet i` (reindexed along `Fintype.equivFin ι`)
satisfies the hypotheses of `Work.Thom.thomClass_of_finite_cover`:
* the local Thom data over `finInter U S` is `Work.Thom.localThomOfChart Z_ℝ (2*m) e (cc k) _ _`
  for any `k ∈ S`, where `e : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin (2*m))`
  (`Work.Thom.finrank_real_euclidean_complex`) and `cc` is the chart index;
* the compatibility of nested intersections is `Work.Thom.localThomOfChart_restrict` (same chart)
  composed with `Work.Thom.localThomOfChart_eq_of_det_pos` (different charts), the determinant being
  positive by `Work.Thom.det_restrictScalars_pos` (`Work.Thom.det_restrictScalars_eq_normSq`);
* the vanishing on finite unions of intersections is `Work.Thom.subsingleton_PieceCoh_iUnion_finInter`
  in degree `2 * m - 1 < 2 * m`.
Finally transport `LocalThom Z_ℝ (2*m) univ` (the union of the pieces is `univ`) to a `ThomClass`
along the homeomorphism `↥(univ : Set B) ≃ B` (`relCohomology_homeomorph_pairs`).

NOTE (import islands): `Work.Thom.subsingleton_PieceCoh_iUnion_finInter` lies in the import island
of `Submission.Work.Cohomology.subsingleton_pdCohSub_union`, incompatible with the island of
`Work.Thom.thomClass_of_finite_cover` (the duplicate `Work.Cohomology.Yt`).  If importing both
fails, reprove the finite-union vanishing inside this file from the honest Mayer--Vietoris comparison
`Work.Cohomology.honest_exact₁`/`honest_exact₂` (`Submission.Work.Cohomology.relCohMV_honest_les`),
which is available in this island: an induction on the number of pieces, the base case being
`Work.Thom.subsingleton_PieceCoh_genFibre` on a chart piece and the step the honest MV LES. -/
theorem thomClass_of_complex_fintype
    {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Nonempty (Work.Thom.ThomClass (Work.Thom.realification Z) (2 * m)) := by
  classical
  have hn : 1 ≤ 2 * m := by omega
  -- the realification, viewed as an opaque real bundle
  let ZR : RealBundle B (EuclideanSpace ℂ (Fin m)) ι := realification Z
  have hZR : ZR = realification Z := rfl
  -- a real-linear identification of the fibre `ℂ^m` with `ℝ^(2m)`
  have hfr : Module.finrank ℝ (EuclideanSpace ℂ (Fin m))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * m))) := by
    rw [finrank_real_euclidean_complex m, finrank_euclideanSpace_fin]
  let e : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
    ContinuousLinearEquiv.ofFinrankEq hfr
  -- the cover by the pieces `Z.baseSet i`, reindexed along `Fintype.equivFin ι`
  let cc : Fin (Fintype.card ι) → ι := fun k => (Fintype.equivFin ι).symm k
  let U : Fin (Fintype.card ι) → Set B := fun k => ZR.baseSet (cc k)
  have hU : ∀ k, IsOpen (U k) := fun k => ZR.isOpen_baseSet (cc k)
  -- every nonempty intersection lies in the chart of any of its members
  have hsub : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty),
      finInter U S ⊆ ZR.baseSet (cc hS.choose) := fun S hS x hx =>
    (mem_finInter.mp hx) hS.choose hS.choose_spec
  -- the local Thom data over the pieces of the cover
  let c : ∀ (S : Finset (Fin (Fintype.card ι))), S.Nonempty →
      PieceCoh ZR (finInter U S) (2 * m) := fun S hS =>
    (localThomOfChart ZR (2 * m) e (cc hS.choose) (finInter U S) (hsub S hS)).τ
  have hc : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (j : ℕ),
      Function.Bijective (localThomMap ZR (2 * m) (finInter U S) (c S hS) j) := by
    intro S hS j
    dsimp only [c]
    exact (localThomOfChart ZR (2 * m) e (cc hS.choose)
      (finInter U S) (hsub S hS)).isThom j
  -- compatibility of the local data over nested intersections
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
    -- rewrite the two local classes in the chart of the first piece
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
  -- the low-degree vanishing on finite unions of intersections
  have hlow : ∀ (A : Finset (Finset (Fin (Fintype.card ι)))),
      (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (PieceCoh ZR (⋃ S ∈ A, finInter U S) (2 * m - 1)) :=
    fun A hA _ => subsingleton_PieceCoh_iUnion_finInter_clean ZR (Fintype.card ι) U hU cc
      (fun k => subset_rfl) A hA (m := 2 * m - 1) (by
        rw [finrank_real_euclidean_complex m]
        omega)
  -- the union of the pieces is all of the base
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
  obtain ⟨cU, hcU, _hres⟩ :=
    thomClass_of_finite_cover ZR (2 * m) hn (Fintype.card ι) U hU c hc hcompat hlow
  -- `cU` is local Thom data over the whole base
  have hlc : LocalThom ZR (2 * m) Set.univ :=
    ⟨hcover ▸ cU, fun j => bijective_localThomMap_cast ZR hcover cU j (hcU j)⟩
  exact nonempty_thomClass_of_localThom_univ ZR hlc

end

end Work.Thom
