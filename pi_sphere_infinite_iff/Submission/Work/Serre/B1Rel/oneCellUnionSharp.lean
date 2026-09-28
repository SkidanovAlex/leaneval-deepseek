import Mathlib
import Submission.Work.Serre.B1Rel.Defs
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.CsrSharp.Sigma.sigmaSharp
import Submission.Work.Serre.OneCell.OneCellGeom

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

/-- **The cell-wise comparison over the union of the open `1`-cells, sharp form.**  If the per-cell
comparison `perCellMapOne` is an isomorphism on rational homology in degrees `< 1 + φ` and
surjective in degree `1 + φ` for every cell, then the same holds for the comparison `midUMapOne`
over the union of all the open cells.

This is the `1`-cell analogue of `Work.Serre.CsrSharp.unionIso`
(`Submission/Work/Serre/CsrSharp/Union.lean`): the union of the (pairwise disjoint) open cells is
the disjoint union of the pieces
(`Work.Serre.CsrSharp.Tools.sigmaPiecesHomeo`), over which the comparison is the coproduct of the
per-cell comparisons, whose homology is computed by the additivity of relative homology over a
disjoint union (`Work.Serre.CsrSharp.Sigma.sigmaSharp`). -/
theorem oneCellUnionSharp (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (φ : ℕ)
    (hcell : ∀ i : ι, (∀ m : ℕ, m < 1 + φ → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.Serre.B1Rel.perCellMapOne Y ι f q i) m)) ∧
      Function.Surjective (HomologicalComplex.homologyMap (Work.Serre.B1Rel.perCellMapOne Y ι f q i)
        (1 + φ)).hom) :
    (∀ m : ℕ, m < 1 + φ → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.B1Rel.midUMapOne Y ι f q) m)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (Work.Serre.B1Rel.midUMapOne Y ι f q)
      (1 + φ)).hom := by
  classical
  -- ## The geometry and the two sigma-decompositions
  have hopen : ∀ i : ι, IsOpen (Work.Serre.OneCell.cellInteriorOne Y ι f i) := fun i =>
    Work.Serre.OneCell.isOpen_cellImage f i (fun _ hx => hx)
      (isOpen_lt continuous_subtype_val.norm continuous_const)
  have hdisjO : ∀ i j : ι, i ≠ j →
      Disjoint (Work.Serre.OneCell.cellInteriorOne Y ι f i)
        (Work.Serre.OneCell.cellInteriorOne Y ι f j) :=
    fun i j hij => Work.Serre.OneCell.disjoint_cellInteriorOne f hij
  have hcentre : ∀ i : ι,
      Work.Serre.OneCell.oneCellCentreOne Y ι f i ∈ Work.Serre.OneCell.cellInteriorOne Y ι f i :=
    fun i => Work.Serre.OneCell.oneCellCentreOne_mem_cellInteriorOne f i
  let o : ι → Set (Work.Serre.attachOneCells Y ι f) :=
    fun i => Work.Serre.OneCell.cellInteriorOne Y ι f i
  let ctr : ι → Work.Serre.attachOneCells Y ι f :=
    fun i => Work.Serre.OneCell.oneCellCentreOne Y ι f i
  let U : Set (Work.Serre.attachOneCells Y ι f) := ⋃ i, o i
  let V : Set (Work.Serre.attachOneCells Y ι f) :=
    (Work.Serre.OneCell.oneCellCentresOne Y ι f)ᶜ
  let X : ι → Type := fun i => ↥(q ⁻¹' o i)
  let W : ι → Type := fun i => ↥(o i)
  let A : ∀ i, Set (X i) := fun i =>
    {u : X i | (u : E) ∈ q ⁻¹' (o i \ {ctr i})}
  let Bm : ∀ i, Set (W i) := fun i =>
    {v : W i | (v : Work.Serre.attachOneCells Y ι f) ∈ o i \ {ctr i}}
  let AU : Set ↥(q ⁻¹' U) := {x | (x : E) ∈ q ⁻¹' V}
  let BU : Set ↥U := {x | (x : Work.Serre.attachOneCells Y ι f) ∈ V}
  let gs : ∀ i, C(X i, W i) := fun i => Work.Serre.csrRestrict q (o i)
  let qU : C(↥(q ⁻¹' U), ↥U) := Work.Serre.csrRestrict q U
  let ΦW : ↥U ≃ₜ (Σ i, W i) :=
    Work.Serre.CsrSharp.Tools.sigmaPiecesHomeo o hopen hdisjO
      (fun i x hx => Set.mem_iUnion.mpr ⟨i, hx⟩) (fun z hz => Set.mem_iUnion.mp hz)
  let ΦX : ↥(q ⁻¹' U) ≃ₜ (Σ i, X i) :=
    Work.Serre.CsrSharp.Tools.sigmaPiecesHomeo (fun i => q ⁻¹' o i)
      (fun i => (hopen i).preimage q.continuous)
      (fun i j hij => (hdisjO i j hij).preimage (⇑q))
      (fun i x hx => Set.mem_iUnion.mpr ⟨i, hx⟩)
      (fun z hz => Set.mem_iUnion.mp (Set.preimage_iUnion ▸ hz))
  let cW : C(↥U, Σ i, W i) := ⟨fun x => ΦW x, ΦW.continuous_toFun⟩
  let cWi : C(Σ i, W i, ↥U) := ⟨fun x => ΦW.symm x, ΦW.continuous_invFun⟩
  let cX : C(↥(q ⁻¹' U), Σ i, X i) := ⟨fun x => ΦX x, ΦX.continuous_toFun⟩
  let cXi : C(Σ i, X i, ↥(q ⁻¹' U)) := ⟨fun x => ΦX.symm x, ΦX.continuous_invFun⟩
  have hvalW : ∀ x : Σ i, W i, (cWi x).1 = x.2.1 := fun x => rfl
  have hvalX : ∀ x : Σ i, X i, (cXi x).1 = x.2.1 := fun x => rfl
  -- the comparisons of the pairs
  have hΦW : Set.MapsTo cW BU {x : Σ i, W i | x.2 ∈ Bm x.1} := by
    intro x hx
    refine ⟨(cW x).2.2, fun hc => ?_⟩
    rw [show ((cW x).2 : Work.Serre.attachOneCells Y ι f) = x.1 from rfl] at hc
    exact hx ⟨(cW x).1, hc.symm⟩
  have hΦWi : Set.MapsTo cWi {x : Σ i, W i | x.2 ∈ Bm x.1} BU := by
    intro x hx hc
    obtain ⟨j, hj⟩ := hc
    rcases eq_or_ne j x.1 with h | h
    · exact hx.2 ((hvalW x).symm.trans ((h ▸ hj).symm))
    · exact (Set.disjoint_left.mp (hdisjO x.1 j (Ne.symm h)) hx.1) (hj ▸ hcentre j)
  have hΦX : Set.MapsTo cX AU {x : Σ i, X i | x.2 ∈ A x.1} := by
    intro x hx
    refine ⟨(cX x).2.2, fun hc => ?_⟩
    rw [show q ((cX x).2 : E) = q x.1 from rfl] at hc
    exact hx ⟨(cX x).1, hc.symm⟩
  have hΦXi : Set.MapsTo cXi {x : Σ i, X i | x.2 ∈ A x.1} AU := by
    intro x hx hc
    obtain ⟨j, hj⟩ := hc
    rcases eq_or_ne j x.1 with h | h
    · exact hx.2 ((congrArg (fun w => q w) (hvalX x)).symm.trans ((h ▸ hj).symm))
    · exact (Set.disjoint_left.mp (hdisjO x.1 j (Ne.symm h)) hx.1) (hj ▸ hcentre j)
  have hqU : Set.MapsTo qU AU BU := by intro x hx; exact hx
  have hgS : Set.MapsTo (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ :
      C(Σ i, X i, Σ i, W i)) {x : Σ i, X i | x.2 ∈ A x.1}
      {x : Σ i, W i | x.2 ∈ Bm x.1} := by
    intro x hx
    exact hx
  -- ## The comparison maps and the middle map
  let PX := relChainsRPairMap AU {x : Σ i, X i | x.2 ∈ A x.1} cX hΦX
  let PXi := relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} AU cXi hΦXi
  let PY := relChainsRPairMap BU {x : Σ i, W i | x.2 ∈ Bm x.1} cW hΦW
  let PYi := relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} BU cWi hΦWi
  let M := midUMapOne Y ι f q
  let σMap := relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1}
    {x : Σ i, W i | x.2 ∈ Bm x.1}
    ⟨Sigma.map id (fun i => gs i), by fun_prop⟩ (by intro x hx; exact hx)
  -- ## The per-cell isomorphisms, transported to the disjoint union
  have hσ : ∀ m : ℕ, m < 1 + φ → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap σMap m) := by
    intro m hm
    exact (Work.Serre.CsrSharp.Sigma.sigmaSharp (X := X) (Y := W) A Bm gs
      (fun i => by intro x hx; exact hx) m).1
      (fun i => (hcell i).1 m hm)
  have hσsurj : Function.Surjective
      (HomologicalComplex.homologyMap σMap (1 + φ)).hom := by
    exact (Work.Serre.CsrSharp.Sigma.sigmaSharp (X := X) (Y := W) A Bm gs
      (fun i => by intro x hx; exact hx) (1 + φ)).2
      (fun i => (hcell i).2)
  -- ## The two transport maps are isomorphisms
  have hidX : Set.MapsTo (ContinuousMap.id ↥(q ⁻¹' U)) AU AU := fun x hx => hx
  have hidXi : Set.MapsTo (ContinuousMap.id (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1}
      {x : Σ i, X i | x.2 ∈ A x.1} := fun x hx => hx
  have hidW : Set.MapsTo (ContinuousMap.id ↥U) BU BU := fun x hx => hx
  have hidWi : Set.MapsTo (ContinuousMap.id (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1}
      {x : Σ i, W i | x.2 ∈ Bm x.1} := fun x hx => hx
  have hcompX : cXi.comp cX = ContinuousMap.id ↥(q ⁻¹' U) := by
    apply ContinuousMap.ext
    intro z
    show ΦX.symm (ΦX z) = z
    exact ΦX.symm_apply_apply z
  have hcompXi : cX.comp cXi = ContinuousMap.id (Σ i, X i) := by
    apply ContinuousMap.ext
    intro z
    show ΦX (ΦX.symm z) = z
    exact ΦX.apply_symm_apply z
  have hcompW : cWi.comp cW = ContinuousMap.id ↥U := by
    apply ContinuousMap.ext
    intro z
    show ΦW.symm (ΦW z) = z
    exact ΦW.symm_apply_apply z
  have hcompWi : cW.comp cWi = ContinuousMap.id (Σ i, W i) := by
    apply ContinuousMap.ext
    intro z
    show ΦW (ΦW.symm z) = z
    exact ΦW.apply_symm_apply z
  have hPX : PX ≫ PXi = 𝟙 _ := by
    have h1 : PX ≫ PXi
        = relChainsRPairMap AU AU (cXi.comp cX) (fun x hx => hΦXi (hΦX hx)) :=
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp cX cXi hΦX hΦXi
        (hg'' := fun x hx => hΦXi (hΦX hx))
    have h2 : relChainsRPairMap AU AU (cXi.comp cX) (fun x hx => hΦXi (hΦX hx)) = 𝟙 _ :=
      (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hcompX
        (fun x hx => hΦXi (hΦX hx)) hidX).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' AU hidX)
    exact h1.trans h2
  have hPXi : PXi ≫ PX = 𝟙 _ := by
    have h1 : PXi ≫ PX
        = relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, X i | x.2 ∈ A x.1}
            (cX.comp cXi) (fun x hx => hΦX (hΦXi hx)) :=
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp cXi cX hΦXi hΦX
        (hg'' := fun x hx => hΦX (hΦXi hx))
    have h2 : relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, X i | x.2 ∈ A x.1}
        (cX.comp cXi) (fun x hx => hΦX (hΦXi hx)) = 𝟙 _ :=
      (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hcompXi
        (fun x hx => hΦX (hΦXi hx)) hidXi).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' _ hidXi)
    exact h1.trans h2
  have hPY : PY ≫ PYi = 𝟙 _ := by
    have h1 : PY ≫ PYi
        = relChainsRPairMap BU BU (cWi.comp cW) (fun x hx => hΦWi (hΦW hx)) :=
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp cW cWi hΦW hΦWi
        (hg'' := fun x hx => hΦWi (hΦW hx))
    have h2 : relChainsRPairMap BU BU (cWi.comp cW) (fun x hx => hΦWi (hΦW hx)) = 𝟙 _ :=
      (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hcompW
        (fun x hx => hΦWi (hΦW hx)) hidW).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' BU hidW)
    exact h1.trans h2
  have hPYi : PYi ≫ PY = 𝟙 _ := by
    have h1 : PYi ≫ PY
        = relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
            (cW.comp cWi) (fun x hx => hΦW (hΦWi hx)) :=
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp cWi cW hΦWi hΦW
        (hg'' := fun x hx => hΦW (hΦWi hx))
    have h2 : relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
        (cW.comp cWi) (fun x hx => hΦW (hΦWi hx)) = 𝟙 _ :=
      (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hcompWi
        (fun x hx => hΦW (hΦWi hx)) hidWi).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' _ hidWi)
    exact h1.trans h2
  -- ## The square: the two ways round commute
  have hcommCM : (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ :
      C(Σ i, X i, Σ i, W i)).comp cX = cW.comp qU := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hcomm : PX ≫ σMap = M ≫ PY :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp_congr cX
      (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ : C(Σ i, X i, Σ i, W i))
      hΦX hgS qU cW hqU hΦW hcommCM
  -- ## Conclusion at the level of homology
  haveI hPXiso : CategoryTheory.IsIso PX := CategoryTheory.IsIso.mk ⟨PXi, hPX, hPXi⟩
  haveI hPYiso : CategoryTheory.IsIso PY := CategoryTheory.IsIso.mk ⟨PYi, hPY, hPYi⟩
  refine ⟨?_, ?_⟩
  · intro m hm
    have hsq := congrArg (fun f => HomologicalComplex.homologyMap f m) hcomm
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    haveI hPXm : CategoryTheory.IsIso (HomologicalComplex.homologyMap PX m) :=
      (HomologicalComplex.homologyMapIso (asIso PX) m).isIso_hom
    haveI hPYm : CategoryTheory.IsIso (HomologicalComplex.homologyMap PY m) :=
      (HomologicalComplex.homologyMapIso (asIso PY) m).isIso_hom
    haveI hσm : CategoryTheory.IsIso (HomologicalComplex.homologyMap σMap m) := hσ m hm
    haveI hMPY : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap M m ≫ HomologicalComplex.homologyMap PY m) := by
      rw [← hsq]
      infer_instance
    exact CategoryTheory.IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap M m)
      (HomologicalComplex.homologyMap PY m)
  · have hsq := congrArg (fun f => HomologicalComplex.homologyMap f (1 + φ)) hcomm
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    haveI hPXisoN : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap PX (1 + φ)) :=
      (HomologicalComplex.homologyMapIso (asIso PX) (1 + φ)).isIso_hom
    haveI hPYisoN : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap PY (1 + φ)) :=
      (HomologicalComplex.homologyMapIso (asIso PY) (1 + φ)).isIso_hom
    have hPYb : Function.Bijective
        (HomologicalComplex.homologyMap PY (1 + φ)).hom :=
      ConcreteCategory.bijective_of_isIso _
    have hPXb : Function.Bijective
        (HomologicalComplex.homologyMap PX (1 + φ)).hom :=
      ConcreteCategory.bijective_of_isIso _
    have hfact : (HomologicalComplex.homologyMap M (1 + φ) ≫
          HomologicalComplex.homologyMap PY (1 + φ)).hom
        = (HomologicalComplex.homologyMap PX (1 + φ) ≫
            HomologicalComplex.homologyMap σMap (1 + φ)).hom := by
      rw [hsq]
    have hsurj_comp : Function.Surjective
        ((HomologicalComplex.homologyMap M (1 + φ) ≫
          HomologicalComplex.homologyMap PY (1 + φ)).hom) := by
      rw [hfact]
      simp only [ModuleCat.hom_comp]
      exact hσsurj.comp hPXb.2
    intro y
    obtain ⟨x, hx⟩ := hsurj_comp
      ((HomologicalComplex.homologyMap PY (1 + φ)).hom y)
    exact ⟨x, hPYb.1 hx⟩

end

end Work.Serre.B1Rel
