import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGeom
import Submission.Work.Serre.csrAssembly
import Submission.Work.Serre.csrPerCell
import Submission.Work.Serre.csrSigmaAdditivity
import Submission.Work.Cohomology.relChainsMapOf_comp

/-!
# The cell-wise comparison over the union of the open half-balls

For `Z = attachCells n Y ι f`, `o i = csrOpenBall n Y ι f i` the open half-ball around the centre of
the `i`-th cell, `U = ⋃ i, o i` and `V = csrV n Y ι f` the complement of the centres, the map of
pairs `(q⁻¹U, q⁻¹(U ∩ V)) → (U, U ∩ V)` induced by a Serre fibration `q` with rationally acyclic
fibres is an isomorphism on relative rational homology in the range of the cell step.

The pieces `o i` are pairwise disjoint open sets, so `U` is homeomorphic to the disjoint union
`Σ i, ↥(o i)` and `q⁻¹U` to `Σ i, ↥(q⁻¹(o i))`; under these homeomorphisms the map becomes the
disjoint union of the per-cell maps, whose isomorphy in the range is `Work.Serre.csrPerCell`
together with the additivity `Work.Serre.csrSigmaAdditivity`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

/-- **Continuity of the canonical map from a space covered by disjoint open pieces to the disjoint
union of the pieces.**  For a family `o : ι → Set Z` of pairwise disjoint open sets and a set
`S ⊆ Z` covered by them, the map `z ↦ (i, z)` — with `i` the (unique, by disjointness) index of a
piece containing `z` — is continuous: near `z` it agrees with `y ↦ ⟨i, y⟩` on the open piece
`o i ∩ S`, which is a neighbourhood of `z`. -/
theorem csrUnionStep_cont_toFun {ι Z : Type} [TopologicalSpace Z] {S : Set Z}
    (o : ι → Set Z) (hopen : ∀ i, IsOpen (o i)) (hdisj : ∀ i j, i ≠ j → Disjoint (o i) (o j))
    (hcov : ∀ z ∈ S, ∃ i, z ∈ o i) :
    Continuous fun z : ↥S => (⟨Classical.choose (hcov z.1 z.2),
      ⟨z.1, Classical.choose_spec (hcov z.1 z.2)⟩⟩ : Σ i, ↥(o i)) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hzi : z.1 ∈ o (Classical.choose (hcov z.1 z.2)) :=
    Classical.choose_spec (hcov z.1 z.2)
  have hU : IsOpen ({w : ↥S | w.1 ∈ o (Classical.choose (hcov z.1 z.2))}) :=
    (hopen _).preimage continuous_subtype_val
  have hmodel : Continuous (fun w : {w : ↥S | w.1 ∈ o (Classical.choose (hcov z.1 z.2))} =>
      (⟨Classical.choose (hcov z.1 z.2), ⟨(w.1 : Z), w.2⟩⟩ : Σ j, ↥(o j))) :=
    continuous_sigmaMk.comp (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) (fun w => w.2))
  have hEqOn : ∀ w : {w : ↥S | w.1 ∈ o (Classical.choose (hcov z.1 z.2))},
      (fun z : ↥S => (⟨Classical.choose (hcov z.1 z.2),
        ⟨z.1, Classical.choose_spec (hcov z.1 z.2)⟩⟩ : Σ i, ↥(o i))) w.1
      = (⟨Classical.choose (hcov z.1 z.2), ⟨(w.1 : Z), w.2⟩⟩ : Σ j, ↥(o j)) := by
    intro w
    have h : Classical.choose (hcov w.1.1 w.1.2) = Classical.choose (hcov z.1 z.2) := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj _ _ hne)
        (Classical.choose_spec (hcov w.1.1 w.1.2)) w.2
    have hiff : ∀ y : Z, y ∈ o (Classical.choose (hcov w.1.1 w.1.2))
        ↔ y ∈ o (Classical.choose (hcov z.1 z.2)) :=
      fun y => ⟨fun hy => by rw [← h]; exact hy, fun hy => by rw [h]; exact hy⟩
    show (⟨Classical.choose (hcov w.1.1 w.1.2),
      ⟨(w.1 : Z), Classical.choose_spec (hcov w.1.1 w.1.2)⟩⟩ : Σ j, ↥(o j))
      = ⟨Classical.choose (hcov z.1 z.2), ⟨(w.1 : Z), w.2⟩⟩
    exact Sigma.ext h ((Subtype.heq_iff_coe_eq hiff).mpr rfl)
  have hcontOn : ContinuousOn (fun z : ↥S => (⟨Classical.choose (hcov z.1 z.2),
      ⟨z.1, Classical.choose_spec (hcov z.1 z.2)⟩⟩ : Σ i, ↥(o i)))
      {w : ↥S | w.1 ∈ o (Classical.choose (hcov z.1 z.2))} := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hmodel.congr (fun w => (hEqOn w).symm)
  exact hcontOn.continuousAt (hU.mem_nhds hzi)

/-- **A union of pairwise disjoint open pieces is the disjoint union of the pieces.**  The canonical
homeomorphism `↥S ≃ₜ Σ i, ↥(o i)`, `z ↦ (i, z)` with `i` the index (unique, by disjointness) of a
piece containing `z`. -/
noncomputable def csrUnionStep_homeo {ι Z : Type} [TopologicalSpace Z] {S : Set Z} (o : ι → Set Z)
    (hopen : ∀ i, IsOpen (o i)) (hdisj : ∀ i j, i ≠ j → Disjoint (o i) (o j))
    (hsub : ∀ i, o i ⊆ S) (hcov : ∀ z ∈ S, ∃ i, z ∈ o i) :
    ↥S ≃ₜ (Σ i, ↥(o i)) where
  toFun := fun z => ⟨Classical.choose (hcov z.1 z.2),
    ⟨z.1, Classical.choose_spec (hcov z.1 z.2)⟩⟩
  invFun := fun x => ⟨x.2.1, hsub x.1 x.2.2⟩
  left_inv := fun z => Subtype.ext rfl
  right_inv := by
    intro x
    obtain ⟨i, y⟩ := x
    have h : Classical.choose (hcov (y : Z) (hsub i y.2)) = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj (Classical.choose (hcov (y : Z) (hsub i y.2))) i hne)
        (Classical.choose_spec (hcov (y : Z) (hsub i y.2))) y.2
    have hiff : ∀ z : Z, z ∈ o (Classical.choose (hcov (y : Z) (hsub i y.2))) ↔ z ∈ o i :=
      fun z => ⟨fun hz => by rw [← h]; exact hz, fun hz => by rw [h]; exact hz⟩
    show (⟨Classical.choose (hcov (y : Z) (hsub i y.2)),
      ⟨(y : Z), Classical.choose_spec (hcov (y : Z) (hsub i y.2))⟩⟩ : Σ i, ↥(o i)) = ⟨i, y⟩
    exact Sigma.ext h ((Subtype.heq_iff_coe_eq hiff).mpr rfl)
  continuous_toFun := csrUnionStep_cont_toFun o hopen hdisj hcov
  continuous_invFun := by
    refine continuous_sigma ?_
    intro i
    exact Continuous.subtype_mk continuous_subtype_val _


/-! ## The cell-wise comparison over the union of the open half-balls -/

/-- **The comparison over the union of the open half-balls is an isomorphism in the range.** -/
theorem csrUnionStep (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (N : ℕ)
    (hacyc : ∀ z : Work.RatHurewicz.attachCells n Y ι f,
      (∀ k : ℕ, 0 < k → k ≤ N → CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology k)) ∧
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ))
    (m : ℕ) (hm : m ≤ N) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (X := ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)))
        (Y := ↥(⋃ i, csrOpenBall n Y ι f i))
        {x : ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)) |
          (x : E) ∈ q ⁻¹' ((⋃ i, csrOpenBall n Y ι f i) ∩ csrV n Y ι f)}
        {x : ↥(⋃ i, csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            (⋃ i, csrOpenBall n Y ι f i) ∩ csrV n Y ι f}
        (csrRestrict q (⋃ i, csrOpenBall n Y ι f i)) (by intro x hx; exact hx)) m) := by
  classical
  obtain ⟨hopen, -, -, -, hcentre, -, hdisj, -, -, -, hcover, hcap⟩ := csrGeom n Y ι f
  let o : ι → Set (Work.RatHurewicz.attachCells n Y ι f) := fun i => csrOpenBall n Y ι f i
  let U : Set (Work.RatHurewicz.attachCells n Y ι f) := ⋃ i, o i
  let V : Set (Work.RatHurewicz.attachCells n Y ι f) := csrV n Y ι f
  let W : Set E := q ⁻¹' U
  let AU : Set ↥W := {x | (x : E) ∈ q ⁻¹' (U ∩ V)}
  let BU : Set ↥U := {x | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ U ∩ V}
  let X : ι → Type := fun i => ↥(q ⁻¹' o i)
  let Wp : ι → Type := fun i => ↥(o i)
  let Ae : ∀ i, Set (X i) := fun i => {u : X i | (u : E) ∈ q ⁻¹' (o i \ {csrCentre n Y ι f i})}
  let Be : ∀ i, Set (Wp i) := fun i =>
    {v : Wp i | (v : Work.RatHurewicz.attachCells n Y ι f) ∈ o i \ {csrCentre n Y ι f i}}
  let gs : ∀ i, C(X i, Wp i) := fun i => csrRestrict q (o i)
  have hdisjW : ∀ i j, i ≠ j → Disjoint (q ⁻¹' o i) (q ⁻¹' o j) :=
    fun i j hij => (hdisj i j hij).preimage q
  let ΦW : ↥U ≃ₜ (Σ i, Wp i) :=
    csrUnionStep_homeo o hopen hdisj (fun i => Set.subset_iUnion o i)
      (fun z hz => Set.mem_iUnion.mp hz)
  let ΦX : ↥W ≃ₜ (Σ i, X i) :=
    csrUnionStep_homeo (fun i => q ⁻¹' o i) (fun i => (hopen i).preimage q.continuous) hdisjW
      (fun i x hx => Set.mem_iUnion.mpr ⟨i, hx⟩)
      (fun z hz => Set.mem_iUnion.mp (Set.preimage_iUnion ▸ hz))
  let cW : C(↥U, Σ i, Wp i) := ⟨fun x => ΦW x, ΦW.continuous_toFun⟩
  let cWi : C(Σ i, Wp i, ↥U) := ⟨fun x => ΦW.symm x, ΦW.continuous_invFun⟩
  let cX : C(↥W, Σ i, X i) := ⟨fun x => ΦX x, ΦX.continuous_toFun⟩
  let cXi : C(Σ i, X i, ↥W) := ⟨fun x => ΦX.symm x, ΦX.continuous_invFun⟩
  have hvalW : ∀ x : Σ i, Wp i, (cWi x).1 = x.2.1 := fun x => rfl
  have hvalX : ∀ x : Σ i, X i, (cXi x).1 = x.2.1 := fun x => rfl
  have hΦW : Set.MapsTo cW BU {x : Σ i, Wp i | x.2 ∈ Be x.1} := by
    intro x hx
    refine ⟨(cW x).2.2, fun hc => ?_⟩
    rw [show ((cW x).2 : Work.RatHurewicz.attachCells n Y ι f) = x.1 from rfl] at hc
    exact hx.2 ⟨(cW x).1, hc.symm⟩
  have hΦWi : Set.MapsTo cWi {x : Σ i, Wp i | x.2 ∈ Be x.1} BU := by
    intro x hx
    refine ⟨(cWi x).2, fun hc => ?_⟩
    obtain ⟨j, hj⟩ := hc
    rcases eq_or_ne j x.1 with h | h
    · exact hx.2 ((hvalW x).symm.trans ((h ▸ hj).symm))
    · exact (Set.disjoint_left.mp (hdisj x.1 j (Ne.symm h)) hx.1) (hj ▸ hcentre j)
  have hΦX : Set.MapsTo cX AU {x : Σ i, X i | x.2 ∈ Ae x.1} := by
    intro x hx
    refine ⟨(cX x).2.2, fun hc => ?_⟩
    rw [show q ((cX x).2 : E) = q x.1 from rfl] at hc
    exact hx.2 ⟨(cX x).1, hc.symm⟩
  have hΦXi : Set.MapsTo cXi {x : Σ i, X i | x.2 ∈ Ae x.1} AU := by
    intro x hx
    refine ⟨(cXi x).2, fun hc => ?_⟩
    obtain ⟨j, hj⟩ := hc
    rcases eq_or_ne j x.1 with h | h
    · exact hx.2 ((congrArg (fun w => q w) (hvalX x)).symm.trans ((h ▸ hj).symm))
    · exact (Set.disjoint_left.mp (hdisj x.1 j (Ne.symm h)) hx.1) (hj ▸ hcentre j)
  have hqU : Set.MapsTo (csrRestrict q U) AU BU := fun x hx => hx
  have hgS : Set.MapsTo (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ :
      C(Σ i, X i, Σ i, Wp i)) {x : Σ i, X i | x.2 ∈ Ae x.1} {x : Σ i, Wp i | x.2 ∈ Be x.1} :=
    fun x hx => hx
  let PX := relChainsRPairMap AU {x : Σ i, X i | x.2 ∈ Ae x.1} cX hΦX
  let PXi := relChainsRPairMap {x : Σ i, X i | x.2 ∈ Ae x.1} AU cXi hΦXi
  let PY := relChainsRPairMap BU {x : Σ i, Wp i | x.2 ∈ Be x.1} cW hΦW
  let PYi := relChainsRPairMap {x : Σ i, Wp i | x.2 ∈ Be x.1} BU cWi hΦWi
  let M := relChainsRPairMap AU BU (csrRestrict q U) (by intro x hx; exact hx)
  let σM := relChainsRPairMap {x : Σ i, X i | x.2 ∈ Ae x.1} {x : Σ i, Wp i | x.2 ∈ Be x.1}
      ⟨Sigma.map id (fun i => gs i), by fun_prop⟩ (fun x hx => hx)
  have hPX : PX ≫ PXi = 𝟙 _ := by
    rw [csrAsm_pair_comp (A := AU) (B := {x : Σ i, X i | x.2 ∈ Ae x.1}) (C := AU)
      cX cXi hΦX hΦXi (hg'' := fun x hx => hΦXi (hΦX hx))]
    exact (csrAsm_pair_congr (ContinuousMap.ext (fun x => ΦX.symm_apply_apply x))
      (fun x hx => hΦXi (hΦX hx)) (fun x hx => hx)).trans (csrAsm_pair_id AU _)
  have hPXi : PXi ≫ PX = 𝟙 _ := by
    rw [csrAsm_pair_comp (A := {x : Σ i, X i | x.2 ∈ Ae x.1}) (B := AU)
      (C := {x : Σ i, X i | x.2 ∈ Ae x.1}) cXi cX hΦXi hΦX
      (hg'' := fun x hx => hΦX (hΦXi hx))]
    exact (csrAsm_pair_congr (ContinuousMap.ext (fun x => ΦX.apply_symm_apply x))
      (fun x hx => hΦX (hΦXi hx)) (fun x hx => hx)).trans
      (csrAsm_pair_id {x : Σ i, X i | x.2 ∈ Ae x.1} _)
  have hPY : PY ≫ PYi = 𝟙 _ := by
    rw [csrAsm_pair_comp (A := BU) (B := {x : Σ i, Wp i | x.2 ∈ Be x.1}) (C := BU)
      cW cWi hΦW hΦWi (hg'' := fun x hx => hΦWi (hΦW hx))]
    exact (csrAsm_pair_congr (ContinuousMap.ext (fun x => ΦW.symm_apply_apply x))
      (fun x hx => hΦWi (hΦW hx)) (fun x hx => hx)).trans (csrAsm_pair_id BU _)
  have hPYi : PYi ≫ PY = 𝟙 _ := by
    rw [csrAsm_pair_comp (A := {x : Σ i, Wp i | x.2 ∈ Be x.1}) (B := BU)
      (C := {x : Σ i, Wp i | x.2 ∈ Be x.1}) cWi cW hΦWi hΦW
      (hg'' := fun x hx => hΦW (hΦWi hx))]
    exact (csrAsm_pair_congr (ContinuousMap.ext (fun x => ΦW.apply_symm_apply x))
      (fun x hx => hΦW (hΦWi hx)) (fun x hx => hx)).trans
      (csrAsm_pair_id {x : Σ i, Wp i | x.2 ∈ Be x.1} _)
  haveI hIPX : CategoryTheory.IsIso PX := ⟨PXi, hPX, hPXi⟩
  haveI hIPY : CategoryTheory.IsIso PY := ⟨PYi, hPY, hPYi⟩
  have hcomp : (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ :
        C(Σ i, X i, Σ i, Wp i)).comp cX = cW.comp (csrRestrict q U) := by
    apply ContinuousMap.ext
    intro x
    rfl
  have hsq : PX ≫ σM = M ≫ PY := by
    rw [csrAsm_pair_comp (A := AU) (B := {x : Σ i, X i | x.2 ∈ Ae x.1})
      (C := {x : Σ i, Wp i | x.2 ∈ Be x.1})
      cX ⟨Sigma.map id (fun i => gs i), by fun_prop⟩ hΦX hgS
      (hg'' := fun x hx => hgS (hΦX hx))]
    rw [csrAsm_pair_congr hcomp (fun x hx => hgS (hΦX hx))
      (fun x hx => hΦW (hqU hx))]
    exact (csrAsm_pair_comp (A := AU) (B := BU) (C := {x : Σ i, Wp i | x.2 ∈ Be x.1})
      (csrRestrict q U) cW hqU hΦW (hg'' := fun x hx => hΦW (hqU hx))).symm
  haveI hIσM : CategoryTheory.IsIso (HomologicalComplex.homologyMap σM m) :=
    csrSigmaAdditivity (X := X) (Y := Wp) (A := Ae) (B := Be) (g := gs)
      (hg := fun i => by intro x hx; exact hx) m
      (fun i => csrPerCell n Y ι f q hq N hacyc i m hm)
  haveI hPXm : CategoryTheory.IsIso (HomologicalComplex.homologyMap PX m) :=
    (HomologicalComplex.homologyMapIso (asIso PX) m).isIso_hom
  haveI hPYm : CategoryTheory.IsIso (HomologicalComplex.homologyMap PY m) :=
    (HomologicalComplex.homologyMapIso (asIso PY) m).isIso_hom
  have hsq' := congrArg (fun φ => HomologicalComplex.homologyMap φ m) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq'
  haveI hMPY : CategoryTheory.IsIso (HomologicalComplex.homologyMap M m
      ≫ HomologicalComplex.homologyMap PY m) := by
    rw [← hsq']; infer_instance
  exact CategoryTheory.IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap M m)
    (HomologicalComplex.homologyMap PY m)

end

end Work.Serre
