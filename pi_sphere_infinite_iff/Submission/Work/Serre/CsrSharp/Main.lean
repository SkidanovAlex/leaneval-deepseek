import Mathlib
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.CsrSharp.Union
import Submission.Work.Serre.csrGlue
import Submission.Work.Serre.csrRelIso
import Submission.Work.Serre.csrCompress
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Stems.Engine.CoeffTransfer

/-!
# Assembly of the sharp rational cell step

`Work.Serre.CsrSharp.cellStepSharpAux` deduces the sharp rational cell step from the two remaining
interfaces `Work.Serre.CsrSharp.PerCellIso` (the per-cell computation) and
`Work.Serre.CsrSharp.SigmaIso` (additivity of relative homology over a disjoint union): the cell
step map `Work.Serre.cellStepMap n ι f q` is the map of pairs `(E, q⁻¹Y') → (Z, Y')`, and the chain

* `(E, q⁻¹Y') → (E, q⁻¹V)` and `(Z, Y') → (Z, V)` are isomorphisms on homology in every degree
  (compression of the complement of the cell centres onto the old part, `Work.Serre.csrRelIso`
  with `Work.Serre.csrCompress`),
* the middle map `(E, q⁻¹V) → (Z, V)` is compared with the union `U = ⋃ i, csrOpenBall i` by the
  two excision isomorphisms `Work.Serre.csrExcisionRat`,
* over `U` the map is the coproduct of the per-cell maps (`Work.Serre.CsrSharp.unionIso`).

Everything is transported by `Work.Serre.CsrSharp.Tools.isIso_of_sq_left/right` and
`...surjective_of_sq_left/right`.
-/

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CsrSharp

noncomputable section

/-- `Work.Serre.cellStepMap n ι f q` is the map of relative chain complexes induced by the map of
pairs `(E, q⁻¹Y') → (Z, Y')`, in the form of `Work.Serre.relChainsRPairMap`. -/
theorem cellStepMap_eq_pairMap (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) :
    Work.Serre.cellStepMap n ι f q
      = Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl n Y ι f))
          (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) q (fun _ hx => hx) := by
  unfold Work.Serre.cellStepMap Work.Serre.relChainsRPairMap Work.Serre.csrRelMapOf
  apply Work.Serre.cokernel_map_congr <;> rfl

/-- **The sharp rational cell step**, deduced from the per-cell computation and additivity. -/
theorem cellStepSharpAux (hcell : PerCellIso) (hsigma : SigmaIso)
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
    (∀ i : ℕ, i < (n + 2) + φ →
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q)
      ((n + 2) + φ)).hom := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hVopen, hcover, -⟩ := csrGeom n Y ι f
  -- the relative part `Y'` of the old space, the union `U₀` of the open half-balls and the
  -- complement `V` of the cell centres, inside `Z = attachCells n Y ι f`
  let Y' : Set (Work.RatHurewicz.attachCells n Y ι f) :=
    Set.range (Work.RatHurewicz.attachIncl n Y ι f)
  let U₀ : Set (Work.RatHurewicz.attachCells n Y ι f) := ⋃ i, csrOpenBall n Y ι f i
  let V : Set (Work.RatHurewicz.attachCells n Y ι f) := csrV n Y ι f
  have hUopen : IsOpen U₀ := by
    rw [show U₀ = ⋃ i, csrOpenBall n Y ι f i from rfl]
    exact isOpen_iUnion fun i => (csrGeom n Y ι f).1 i
  have hY'V : Y' ⊆ V := by
    rintro z ⟨y, rfl⟩ ⟨i, hi⟩
    refine Work.RatHurewicz.cellOrigin_notMem_range_attachIncl (f := f) i ?_
    change csrCentre n Y ι f i ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)
    exact hi ▸ ⟨y, rfl⟩
  -- the compression of the complement of the centres onto the old part, over `ℚ`
  have hcomp := fun m => csrCompress n Y ι f q hq m
  have hVzero : ∀ m : ℕ, CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of ↥V) {x : ↥V | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ Y'}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m (hcomp m).1
  have hBzero : ∀ m : ℕ, CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of ↥(q ⁻¹' V)) {x : ↥(q ⁻¹' V) | (x : E) ∈ q ⁻¹' Y'}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m (hcomp m).2
  -- the two compression isomorphisms
  have hr1 : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E)
        (fun x hx => Set.preimage_mono hY'V hx)) m) :=
    fun m => csrRelIso (q ⁻¹' Y') (q ⁻¹' V) (Set.preimage_mono hY'V) hBzero m
  have hr3 : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap Y' V (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f))
        (fun x hx => hY'V hx)) m) :=
    fun m => csrRelIso Y' V hY'V hVzero m
  -- the square `cellStepMap ≫ r3 = r1 ≫ midV`
  have hsq1 : Work.Serre.cellStepMap n ι f q
        ≫ (Work.Serre.relChainsRPairMap Y' V
            (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun x hx => hY'V hx))
      = (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E)
          (fun x hx => Set.preimage_mono hY'V hx))
        ≫ (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx)) := by
    rw [cellStepMap_eq_pairMap n Y ι f q]
    exact Tools.relChainsRPairMap_comp_congr q
      (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun _ hx => hx)
      (fun x hx => hY'V hx) (ContinuousMap.id E) q
      (fun x hx => Set.preimage_mono hY'V hx) (fun _ hx => hx) (by ext x; rfl)
  -- the two excision isomorphisms comparing the middle map with the union `U₀`
  have hcovE : q ⁻¹' U₀ ∪ q ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, show U₀ ∪ V = Set.univ from hcover, Set.preimage_univ]
  have hexcE : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)) m) :=
    fun m => csrExcisionRat (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V) (hUopen.preimage q.continuous)
      (hVopen.preimage q.continuous) hcovE m
  have hexcZ : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
        U₀ V) m) :=
    fun m => csrExcisionRat (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V
      hUopen hVopen hcover m
  -- the square `excE ≫ midV = midU ≫ excZ`
  have hmapTot : Work.Cohomology.subtypeIncl (TopCat.of E) (q ⁻¹' U₀) ≫ TopCat.ofHom q
      = TopCat.ofHom (csrRestrict q U₀)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hsq2 :
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V))
        ≫ (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx))
      = (Work.Serre.relChainsRPairMap
          {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V} {x : ↥U₀ | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ V}
          (csrRestrict q U₀) (fun _ hx => hx))
        ≫ (Work.Serre.relChainsRInclPairMap
            (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) := by
    unfold Work.Serre.relChainsRInclPairMap Work.Serre.relChainsRPairMap
    rw [Work.Serre.csrRelMapOf_comp, Work.Serre.csrRelMapOf_comp]
    refine Tools.csrRelMapOf_congr ?_ ?_ ?_ ?_
    · exact hmapTot
    · apply TopCat.hom_ext
      ext x
      rfl
    · apply TopCat.hom_ext
      ext x
      rfl
    · apply TopCat.hom_ext
      ext x
      rfl
  -- the union statement
  have hmidU := unionIso hcell hsigma n Y ι f q hq φ hfib h0
  -- transfer to the middle map over `V`
  have hmidViso : ∀ m : ℕ, m < (n + 2) + φ → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx)) m) := by
    intro m hm
    refine Tools.isIso_of_sq_right
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V))
      (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx))
      (Work.Serre.relChainsRPairMap
        {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V}
        {x : ↥U₀ | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ V}
        (csrRestrict q U₀) (fun _ hx => hx))
      (Work.Serre.relChainsRInclPairMap
        (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) hsq2 m
      (hexcE m)
      (by
        have := hmidU.1 m hm
        exact this)
      (hexcZ m)
  have hmidVsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx)) ((n + 2) + φ)).hom :=
    Tools.surjective_of_sq_right
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V))
      (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx))
      (Work.Serre.relChainsRPairMap
        {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V}
        {x : ↥U₀ | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ V}
        (csrRestrict q U₀) (fun _ hx => hx))
      (Work.Serre.relChainsRInclPairMap
        (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) hsq2 ((n + 2) + φ)
      (by
        have := hmidU.2
        exact this)
      ((ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRInclPairMap
          (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) ((n + 2) + φ))).2)
  -- transfer to the cell step map
  refine ⟨?_, ?_⟩
  · intro i hi
    exact Tools.isIso_of_sq_left (Work.Serre.cellStepMap n ι f q)
      (Work.Serre.relChainsRPairMap Y' V
        (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun x hx => hY'V hx))
      (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E)
        (fun x hx => Set.preimage_mono hY'V hx))
      (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx)) hsq1 i
      (hr3 i) (hr1 i) (hmidViso i hi)
  · exact Tools.surjective_of_sq_left (Work.Serre.cellStepMap n ι f q)
      (Work.Serre.relChainsRPairMap Y' V
        (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun x hx => hY'V hx))
      (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E)
        (fun x hx => Set.preimage_mono hY'V hx))
      (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx)) hsq1 ((n + 2) + φ)
      ((ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap Y' V
          (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f))
          (fun x hx => hY'V hx)) ((n + 2) + φ))).1)
      ((ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E)
          (fun x hx => Set.preimage_mono hY'V hx)) ((n + 2) + φ))).2)
      hmidVsurj

end

end Work.Serre.CsrSharp
