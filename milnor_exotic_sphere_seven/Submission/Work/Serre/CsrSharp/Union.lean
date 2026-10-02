import Mathlib
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.csrGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cell-wise comparison over the union of the open half-balls, sharp form

Given the per-cell statement `Work.Serre.CsrSharp.PerCellIso` and the additivity statement
`Work.Serre.CsrSharp.SigmaIso`, the map of pairs `(q⁻¹U, q⁻¹V) → (U, V)` over the union
`U = ⋃ i, Work.Serre.csrOpenBall n Y ι f i` (with `V = Work.Serre.csrV n Y ι f` the complement of
the cell centres) is an isomorphism on rational homology in degrees `< (n+2) + φ` and surjective in
degree `(n+2) + φ`.

This is the sharp analogue of `Work.Serre.csrUnionIso` (`Submission/Work/Serre/csrUnionIso.lean`),
whose parameterisation (`hacyc` at a fixed `N`, conclusion for degrees `≤ N`) is too coarse for the
sharp cell step.
-/

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CsrSharp

noncomputable section

/-- **The middle comparison map over the union of the open half-balls**: the map of pairs
`(q⁻¹U, q⁻¹V) → (U, V)` induced by `q`, where `U = ⋃ i, csrOpenBall n Y ι f i` and
`V = csrV n Y ι f`. -/
def midUMap (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)))
      {x : ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)) |
        (x : E) ∈ q ⁻¹' (Work.Serre.csrV n Y ι f)} ⟶
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i))
      {x : ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i) |
        (x : Work.RatHurewicz.attachCells n Y ι f) ∈ Work.Serre.csrV n Y ι f} :=
  Work.Serre.relChainsRPairMap _ _
    (Work.Serre.csrRestrict q (⋃ i, Work.Serre.csrOpenBall n Y ι f i)) (fun _ hx => hx)

/-- **The cell-wise comparison over the union of the open half-balls, sharp form.** -/
theorem unionIso (hcell : PerCellIso) (hsigma : SigmaIso)
    (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.attachCells n Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.attachCells n Y ι f,
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q y))).homology 0 ≅ ModuleCat.of ℚ ℚ)) :
    (∀ m : ℕ, m < (n + 2) + φ → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (midUMap n Y ι f q) m)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (midUMap n Y ι f q)
      ((n + 2) + φ)).hom := by
  classical
  obtain ⟨hopen, -, -, -, hcentre, -, hdisjO, -, -, -, -, -⟩ := csrGeom n Y ι f
  -- the model spaces over the pieces
  let X : ι → Type := fun i => ↥(q ⁻¹' csrOpenBall n Y ι f i)
  let W : ι → Type := fun i => ↥(csrOpenBall n Y ι f i)
  let A : ∀ i, Set (X i) := fun i =>
    {u : X i | (u : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}
  let Bm : ∀ i, Set (W i) := fun i =>
    {v : W i | (v : Work.RatHurewicz.attachCells n Y ι f) ∈
      csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}}
  let AU : Set ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)) :=
    {x | (x : E) ∈ q ⁻¹' (csrV n Y ι f)}
  let BU : Set ↥(⋃ i, csrOpenBall n Y ι f i) :=
    {x | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrV n Y ι f}
  let gs : ∀ i, C(X i, W i) := fun i => csrRestrict q (csrOpenBall n Y ι f i)
  let qU : C(↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)), ↥(⋃ i, csrOpenBall n Y ι f i)) :=
    csrRestrict q (⋃ i, csrOpenBall n Y ι f i)
  let ΦW : ↥(⋃ i, csrOpenBall n Y ι f i) ≃ₜ (Σ i, W i) :=
    Tools.sigmaPiecesHomeo (fun i => csrOpenBall n Y ι f i) hopen hdisjO
      (fun i x hx => Set.mem_iUnion.mpr ⟨i, hx⟩) (fun z hz => Set.mem_iUnion.mp hz)
  let ΦX : ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)) ≃ₜ (Σ i, X i) :=
    Tools.sigmaPiecesHomeo (fun i => q ⁻¹' csrOpenBall n Y ι f i)
      (fun i => (hopen i).preimage q.continuous)
      (fun i j hij => (hdisjO i j hij).preimage (⇑q))
      (fun i x hx => Set.mem_iUnion.mpr ⟨i, hx⟩)
      (fun z hz => Set.mem_iUnion.mp (Set.preimage_iUnion ▸ hz))
  let cW : C(↥(⋃ i, csrOpenBall n Y ι f i), Σ i, W i) := ⟨fun x => ΦW x, ΦW.continuous_toFun⟩
  let cWi : C(Σ i, W i, ↥(⋃ i, csrOpenBall n Y ι f i)) :=
    ⟨fun x => ΦW.symm x, ΦW.continuous_invFun⟩
  let cX : C(↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)), Σ i, X i) :=
    ⟨fun x => ΦX x, ΦX.continuous_toFun⟩
  let cXi : C(Σ i, X i, ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i))) :=
    ⟨fun x => ΦX.symm x, ΦX.continuous_invFun⟩
  have hvalW : ∀ x : Σ i, W i, (cWi x).1 = x.2.1 := fun x => rfl
  have hvalX : ∀ x : Σ i, X i, (cXi x).1 = x.2.1 := fun x => rfl
  -- the comparisons of the pairs
  have hΦW : Set.MapsTo cW BU {x : Σ i, W i | x.2 ∈ Bm x.1} := by
    intro x hx
    refine ⟨(cW x).2.2, fun hc => ?_⟩
    rw [show ((cW x).2 : Work.RatHurewicz.attachCells n Y ι f) = x.1 from rfl] at hc
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
      C(Σ i, X i, Σ i, W i)) {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, W i | x.2 ∈ Bm x.1} := by
    intro x hx
    exact hx
  -- the comparison maps and the middle map
  let PX : Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i))) AU ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1} :=
    relChainsRPairMap AU {x : Σ i, X i | x.2 ∈ A x.1} cX hΦX
  let PXi : Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i))) AU :=
    relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} AU cXi hΦXi
  let PY : Work.StemsB.relChainsR ℚ (TopCat.of ↥(⋃ i, csrOpenBall n Y ι f i)) BU ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1} :=
    relChainsRPairMap BU {x : Σ i, W i | x.2 ∈ Bm x.1} cW hΦW
  let PYi : Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(⋃ i, csrOpenBall n Y ι f i)) BU :=
    relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} BU cWi hΦWi
  let M := midUMap n Y ι f q
  let σMap : Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1} :=
    relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
      ⟨Sigma.map id (fun i => gs i), by fun_prop⟩ (by intro x hx; exact hx)
  -- the per-cell isomorphisms, transported
  have hσ : ∀ m : ℕ, m < (n + 2) + φ →
      CategoryTheory.IsIso (HomologicalComplex.homologyMap σMap m) := by
    intro m hm
    exact (hsigma (X := X) (Y := W) A Bm gs
      (fun i => by intro x hx; exact hx) m).1
      (fun i => (hcell n Y ι f q hq φ hfib h0 i).1 m hm)
  have hσsurj : Function.Surjective
      (HomologicalComplex.homologyMap σMap ((n + 2) + φ)).hom := by
    exact (hsigma (X := X) (Y := W) A Bm gs
      (fun i => by intro x hx; exact hx) ((n + 2) + φ)).2
      (fun i => (hcell n Y ι f q hq φ hfib h0 i).2)
  -- the two transport maps are isomorphisms
  have hidX : Set.MapsTo (ContinuousMap.id ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i))) AU AU :=
    fun x hx => hx
  have hidXi : Set.MapsTo (ContinuousMap.id (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1}
      {x : Σ i, X i | x.2 ∈ A x.1} := fun x hx => hx
  have hidW : Set.MapsTo (ContinuousMap.id ↥(⋃ i, csrOpenBall n Y ι f i)) BU BU :=
    fun x hx => hx
  have hidWi : Set.MapsTo (ContinuousMap.id (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1}
      {x : Σ i, W i | x.2 ∈ Bm x.1} := fun x hx => hx
  have hcompX : cXi.comp cX
      = ContinuousMap.id ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)) := by
    apply ContinuousMap.ext
    intro z
    show ΦX.symm (ΦX z) = z
    exact ΦX.symm_apply_apply z
  have hcompXi : cX.comp cXi = ContinuousMap.id (Σ i, X i) := by
    apply ContinuousMap.ext
    intro z
    show ΦX (ΦX.symm z) = z
    exact ΦX.apply_symm_apply z
  have hcompW : cWi.comp cW = ContinuousMap.id ↥(⋃ i, csrOpenBall n Y ι f i) := by
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
      Tools.relChainsRPairMap_comp cX cXi hΦX hΦXi (hg'' := fun x hx => hΦXi (hΦX hx))
    have h2 : relChainsRPairMap AU AU (cXi.comp cX) (fun x hx => hΦXi (hΦX hx)) = 𝟙 _ :=
      (Tools.relChainsRPairMap_congr hcompX (fun x hx => hΦXi (hΦX hx)) hidX).trans
        (Tools.relChainsRPairMap_id' AU hidX)
    exact h1.trans h2
  have hPXi : PXi ≫ PX = 𝟙 _ := by
    have h1 : PXi ≫ PX
        = relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, X i | x.2 ∈ A x.1}
            (cX.comp cXi) (fun x hx => hΦX (hΦXi hx)) :=
      Tools.relChainsRPairMap_comp cXi cX hΦXi hΦX (hg'' := fun x hx => hΦX (hΦXi hx))
    have h2 : relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, X i | x.2 ∈ A x.1}
        (cX.comp cXi) (fun x hx => hΦX (hΦXi hx)) = 𝟙 _ :=
      (Tools.relChainsRPairMap_congr hcompXi (fun x hx => hΦX (hΦXi hx)) hidXi).trans
        (Tools.relChainsRPairMap_id' _ hidXi)
    exact h1.trans h2
  have hPY : PY ≫ PYi = 𝟙 _ := by
    have h1 : PY ≫ PYi
        = relChainsRPairMap BU BU (cWi.comp cW) (fun x hx => hΦWi (hΦW hx)) :=
      Tools.relChainsRPairMap_comp cW cWi hΦW hΦWi (hg'' := fun x hx => hΦWi (hΦW hx))
    have h2 : relChainsRPairMap BU BU (cWi.comp cW) (fun x hx => hΦWi (hΦW hx)) = 𝟙 _ :=
      (Tools.relChainsRPairMap_congr hcompW (fun x hx => hΦWi (hΦW hx)) hidW).trans
        (Tools.relChainsRPairMap_id' BU hidW)
    exact h1.trans h2
  have hPYi : PYi ≫ PY = 𝟙 _ := by
    have h1 : PYi ≫ PY
        = relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
            (cW.comp cWi) (fun x hx => hΦW (hΦWi hx)) :=
      Tools.relChainsRPairMap_comp cWi cW hΦWi hΦW (hg'' := fun x hx => hΦW (hΦWi hx))
    have h2 : relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
        (cW.comp cWi) (fun x hx => hΦW (hΦWi hx)) = 𝟙 _ :=
      (Tools.relChainsRPairMap_congr hcompWi (fun x hx => hΦW (hΦWi hx)) hidWi).trans
        (Tools.relChainsRPairMap_id' _ hidWi)
    exact h1.trans h2
  -- the square: the two ways round commute
  have hcommCM : (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ :
      C(Σ i, X i, Σ i, W i)).comp cX = cW.comp qU := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hcomm : PX ≫ σMap = M ≫ PY :=
    Tools.relChainsRPairMap_comp_congr cX
      (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ : C(Σ i, X i, Σ i, W i))
      hΦX hgS qU cW hqU hΦW hcommCM
  -- conclude at the level of homology
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
  · -- the boundary degree
    have hsq := congrArg (fun f => HomologicalComplex.homologyMap f ((n + 2) + φ)) hcomm
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    haveI hPXisoN : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap PX ((n + 2) + φ)) :=
      (HomologicalComplex.homologyMapIso (asIso PX) ((n + 2) + φ)).isIso_hom
    haveI hPYisoN : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap PY ((n + 2) + φ)) :=
      (HomologicalComplex.homologyMapIso (asIso PY) ((n + 2) + φ)).isIso_hom
    have hPYb : Function.Bijective
        (HomologicalComplex.homologyMap PY ((n + 2) + φ)).hom :=
      ConcreteCategory.bijective_of_isIso _
    have hPXb : Function.Bijective
        (HomologicalComplex.homologyMap PX ((n + 2) + φ)).hom :=
      ConcreteCategory.bijective_of_isIso _
    have hfact : (HomologicalComplex.homologyMap M ((n + 2) + φ) ≫
          HomologicalComplex.homologyMap PY ((n + 2) + φ)).hom
        = (HomologicalComplex.homologyMap PX ((n + 2) + φ) ≫
            HomologicalComplex.homologyMap σMap ((n + 2) + φ)).hom := by
      rw [hsq]
    have hsurj_comp : Function.Surjective
        ((HomologicalComplex.homologyMap M ((n + 2) + φ) ≫
          HomologicalComplex.homologyMap PY ((n + 2) + φ)).hom) := by
      rw [hfact]
      simp only [ModuleCat.hom_comp]
      exact hσsurj.comp hPXb.2
    intro y
    obtain ⟨x, hx⟩ := hsurj_comp
      ((HomologicalComplex.homologyMap PY ((n + 2) + φ)).hom y)
    exact ⟨x, hPYb.1 hx⟩

end

end Work.Serre.CsrSharp
