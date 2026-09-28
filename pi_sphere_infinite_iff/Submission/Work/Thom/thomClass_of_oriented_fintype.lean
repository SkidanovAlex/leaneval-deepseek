import Mathlib
import Submission.Work.Thom.thomClass_of_complex_fintype

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **An oriented real vector bundle of rank `n ≥ 1` over gluing data with finite index type has
an integral Thom class.**  The orientation hypothesis is that every transition function
`Z.coordChange i j` has positive determinant at every point of `baseSet i ∩ baseSet j`; this is
exactly what is needed for the chart-trivialisations of the natural model Thom class to agree on
overlaps (`Work.Thom.localThomOfChart_eq_of_det_pos`).

The proof is the real counterpart of `Work.Thom.thomClass_of_complex_fintype`: the cover by the
pieces `Z.baseSet i`, reindexed along `Fintype.equivFin ι`, satisfies the hypotheses of
`Work.Thom.thomClass_of_finite_cover`, the local data over `finInter U S` being
`Work.Thom.localThomOfChart Z n e (cc k) _` with `e` the identity (the fibre already being
`ℝⁿ`); compatibility of nested intersections is `Work.Thom.localThomOfChart_restrict` composed
with `Work.Thom.localThomOfChart_eq_of_det_pos`; the vanishing on finite unions of intersections
is `Work.Thom.subsingleton_PieceCoh_iUnion_finInter_clean` in degree `n - 1 < n`. -/
theorem thomClass_of_oriented_fintype {B : Type} [TopologicalSpace B] {ι : Type}
    [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    Nonempty (Work.Thom.ThomClass Z n) := by
  classical
  -- the identity identification of the fibre with the model `ℝⁿ`
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.refl ℝ _
  -- the cover by the pieces `Z.baseSet i`, reindexed along `Fintype.equivFin ι`
  let cc : Fin (Fintype.card ι) → ι := fun k => (Fintype.equivFin ι).symm k
  let U : Fin (Fintype.card ι) → Set B := fun k => Z.baseSet (cc k)
  have hU : ∀ k, IsOpen (U k) := fun k => Z.isOpen_baseSet (cc k)
  -- every nonempty intersection lies in the chart of any of its members
  have hsub : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty),
      finInter U S ⊆ Z.baseSet (cc hS.choose) := fun S hS x hx =>
    (mem_finInter.mp hx) hS.choose hS.choose_spec
  -- the local Thom data over the pieces of the cover
  let c : ∀ (S : Finset (Fin (Fintype.card ι))), S.Nonempty →
      PieceCoh Z (finInter U S) n := fun S hS =>
    (localThomOfChart Z n e (cc hS.choose) (finInter U S) (hsub S hS)).τ
  have hc : ∀ (S : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (j : ℕ),
      Function.Bijective (localThomMap Z n (finInter U S) (c S hS) j) := by
    intro S hS j
    dsimp only [c]
    exact (localThomOfChart Z n e (cc hS.choose)
      (finInter U S) (hsub S hS)).isThom j
  -- compatibility of the local data over nested intersections
  have hcompat : ∀ (S T : Finset (Fin (Fintype.card ι))) (hS : S.Nonempty) (hT : T.Nonempty)
      (hST : S ⊆ T),
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' finInter U S) (Z.proj ⁻¹' finInter U T)
        (Set.preimage_mono (finInter_mono hST)) n).hom (c S hS) = c T hT := by
    intro S T hS hT hST
    have hsub' : finInter U T ⊆ finInter U S := finInter_mono hST
    have hTS : finInter U T ⊆ Z.baseSet (cc hS.choose) := hsub'.trans (hsub S hS)
    have hSS : finInter U S ⊆ Z.baseSet (cc hS.choose) := hsub S hS
    have hW : finInter U T ⊆ Z.baseSet (cc hS.choose) ∩ Z.baseSet (cc hT.choose) :=
      fun x hx => ⟨hTS hx, hsub T hT hx⟩
    -- rewrite the two local classes in the chart of the first piece
    have hcS : c S hS
        = (localThomOfChart Z n e (cc hS.choose) (finInter U S) hSS).τ := by
      dsimp only [c]
    have hcT : c T hT
        = (localThomOfChart Z n e (cc hS.choose) (finInter U T) hTS).τ := by
      dsimp only [c]
      exact localThomOfChart_eq_of_det_pos Z n hn e (cc hS.choose) (cc hT.choose)
        (finInter U T) hTS (hsub T hT) hW
        (fun x => hori (cc hS.choose) (cc hT.choose) ⟨(x : B), hW x.2⟩)
    rw [hcS, hcT]
    exact localThomOfChart_restrict Z n e (cc hS.choose) (finInter U T) (finInter U S)
      hTS hSS hsub'
  -- the low-degree vanishing on finite unions of intersections
  have hlow : ∀ (A : Finset (Finset (Fin (Fintype.card ι)))),
      (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (PieceCoh Z (⋃ S ∈ A, finInter U S) (n - 1)) :=
    fun A hA _ => subsingleton_PieceCoh_iUnion_finInter_clean Z (Fintype.card ι) U hU cc
      (fun k => subset_rfl) A hA (m := n - 1) (by
        rw [finrank_euclideanSpace_fin]
        omega)
  -- the union of the pieces is all of the base
  have hcover : (⋃ k, U k) = Set.univ := by
    have h1 : (⋃ k : Fin (Fintype.card ι), Z.baseSet (cc k)) = ⋃ i : ι, Z.baseSet i := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨cc k, hk⟩
      · rintro ⟨i, hi⟩
        exact ⟨Fintype.equivFin ι i, by simpa only [cc, Equiv.symm_apply_apply] using hi⟩
    rw [show (⋃ k, U k) = ⋃ k : Fin (Fintype.card ι), Z.baseSet (cc k) from rfl, h1]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩
  obtain ⟨cU, hcU, _hres⟩ :=
    thomClass_of_finite_cover Z n hn (Fintype.card ι) U hU c hc hcompat hlow
  -- `cU` is local Thom data over the whole base
  have hlc : LocalThom Z n Set.univ :=
    ⟨hcover ▸ cU, fun j => bijective_localThomMap_cast Z hcover cU j (hcU j)⟩
  exact nonempty_thomClass_of_localThom_univ Z hlc

end

end Work.Thom
