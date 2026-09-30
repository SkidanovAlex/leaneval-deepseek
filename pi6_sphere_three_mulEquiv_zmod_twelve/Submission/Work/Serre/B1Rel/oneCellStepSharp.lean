import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.oneCellStepRelHomologyIso
import Submission.Work.Serre.B1Rel.Defs
import Submission.Work.Serre.B1Rel.perCellSharpOne
import Submission.Work.Serre.B1Rel.targetGroupsSelf
import Submission.Work.Serre.B1Rel.oneCellSourceIso
import Submission.Work.Serre.B1Rel.oneCellSection
import Submission.Work.Serre.B1Rel.oneCellUnionSharp
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.csrAssembly
import Submission.Work.Serre.csrMid
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.OneCell.compressRel_cellPunctured
import Submission.Work.Stems.Engine.CoeffTransfer

set_option synthInstance.maxHeartbeats 400000


/-!
# The sharp rational `1`-cell step

`Work.Serre.B1Rel.oneCellStepSharp`: for `Z = Work.Serre.attachOneCells Y ι f` (the space obtained
from `Y` by attaching `1`-cells) and a Serre fibration `q : E → Z` whose fibres are rationally
acyclic in degrees `0 < j < φ` and rationally connected, the map of relative rational chain
complexes `C_*(E, q⁻¹Y; ℚ) → C_*(Z, Y; ℚ)` induced by `q` is an isomorphism on homology in degrees
`< 1 + φ` and surjective in degree `1 + φ`.

The proof follows the general sharp rational cell step (`Work.Serre.cellStepSharp`, for cells of
dimension `≥ 2`): one compresses the complement of the cell centres onto the old part, excises the
open cover by the union of the open cells and the complement of the centres, decomposes the union of
the open cells into the coproduct of the single open cells (`oneCellUnionSharp`), and computes each
piece by Serre's `E2(d)` computation over the cube (`perCellSharpOne`, from `oneCellTargetGroups`,
`oneCellSourceIso` and `oneCellSection`).
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

open Work.Serre

theorem oneCellStepSharp (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (hfib : ∀ z : Work.Serre.attachOneCells Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology j))
    (h0 : ∀ z : Work.Serre.attachOneCells Y ι f,
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ)) :
    (∀ i : ℕ, i < 1 + φ → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.oneCellStepMap ι f q) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.oneCellStepMap ι f q) (1 + φ)).hom := by
  classical
  -- ## 0. The sets and the elementary geometry
  set UZ : Set (attachOneCells Y ι f) := OneCell.cellInnerUnionOne Y ι f with hUZ
  set PZ : Set (attachOneCells Y ι f) := OneCell.oneCellCentresOne Y ι f with hPZ
  set VZ : Set (attachOneCells Y ι f) := (OneCell.oneCellCentresOne Y ι f)ᶜ with hVZ
  obtain ⟨-, -, -, -, -, -, -, hClosedP⟩ := OneCell.oneCellGeometry Y ι f
  have hUZopen : IsOpen UZ := by
    rw [hUZ]
    exact OneCell.isOpen_cellUnionOne (Y := Y) (ι := ι) (f := f)
      (U := OneCell.cellInnerOne) (fun x hx => hx) OneCell.isOpen_cellInnerOne
  have hVZopen : IsOpen VZ := by
    rw [hVZ]
    exact hClosedP.isOpen_compl
  have hPZsubUZ : PZ ⊆ UZ := by
    intro z hz
    rw [hPZ] at hz
    obtain ⟨i, rfl⟩ := hz
    rw [hUZ]
    exact Set.mem_iUnion.mpr ⟨i, OneCell.oneCellCentreOne_mem_cellInteriorOne (Y := Y) (ι := ι) (f := f) i⟩
  have hcover : UZ ∪ VZ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    by_cases h : z ∈ PZ
    · exact Or.inl (hPZsubUZ h)
    · exact Or.inr h
  have hY'V : Set.range (oneIncl Y ι f) ⊆ VZ := by
    intro z hz
    rw [hVZ, Set.mem_compl_iff]
    simp only [OneCell.mem_oneCellCentresOne]
    rintro ⟨i, hi⟩
    exact OneCell.oneCellCentreOne_not_mem_oldPart (Y := Y) (ι := ι) f i (hi ▸ hz)
  -- ## 1. The compression of the complement of the centres onto the old part
  have hcompV : ∀ d, Work.RatHurewicz.CompressRel ↥VZ
      {x : ↥VZ | (x : attachOneCells Y ι f) ∈ Set.range (oneIncl Y ι f)} d :=
    fun d => OneCell.compressRel_cellPunctured Y ι f d
  have hVzero : ∀ m : ℕ, CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of ↥VZ) {x : ↥VZ | (x : attachOneCells Y ι f) ∈ Set.range (oneIncl Y ι f)}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m
      (isZero_relChains_of_compress hcompV m)
  have hBzero : ∀ m : ℕ, CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of ↥(q ⁻¹' VZ)) {x : ↥(q ⁻¹' VZ) | (x : E) ∈ q ⁻¹' Set.range (oneIncl Y ι f)}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m
      (isZero_relChains_preimage_of_compress q hq hY'V hcompV m)
  have hr1 : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) (q ⁻¹' VZ)
        (ContinuousMap.id E) (fun x hx => Set.preimage_mono hY'V hx)) m) :=
    fun m => csrRelIso (q ⁻¹' Set.range (oneIncl Y ι f)) (q ⁻¹' VZ)
      (Set.preimage_mono hY'V) hBzero m
  have hr3 : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
        (ContinuousMap.id (attachOneCells Y ι f)) hY'V) m) :=
    fun m => csrRelIso (Set.range (oneIncl Y ι f)) VZ hY'V hVzero m
  -- ## 2. `oneCellStepMap` is the relative pair map of `q`
  have honeCell : Work.Serre.oneCellStepMap ι f q
      = Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f))
          (Set.range (oneIncl Y ι f)) q (by intro x hx; exact hx) := by
    unfold Work.Serre.oneCellStepMap Work.Serre.oneCellStepRestrict
      Work.Serre.relChainsRPairMap Work.Serre.csrRelMapOf
    apply Work.Serre.csrAsm_cokernelMap_congr
    · refine congrArg (fun φ => Work.Cohomology.chainMap ℚ
        (TopCat.of {e : E | q e ∈ Set.range (oneIncl Y ι f)})
        (TopCat.of (Set.range (oneIncl Y ι f))) φ) ?_
      exact congrArg TopCat.ofHom (ContinuousMap.ext (fun x => Subtype.ext rfl))
    · rfl
  -- ## 3. The square relating the cell step map to the middle map
  have hsq1 : Work.Serre.oneCellStepMap ι f q
        ≫ Work.Serre.relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
            (ContinuousMap.id (attachOneCells Y ι f)) hY'V
      = Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) (q ⁻¹' VZ)
          (ContinuousMap.id E) (fun x hx => hY'V hx)
        ≫ Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (by intro x hx; exact hx) := by
    rw [honeCell]
    calc Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f))
            (Set.range (oneIncl Y ι f)) q (by intro x hx; exact hx)
          ≫ Work.Serre.relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
              (ContinuousMap.id (attachOneCells Y ι f)) hY'V
        = Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) VZ
            ((ContinuousMap.id (attachOneCells Y ι f)).comp q) (fun x hx => hY'V hx) :=
          Work.Serre.csrAsm_pair_comp q (ContinuousMap.id (attachOneCells Y ι f))
            (by intro x hx; exact hx) hY'V (hg'' := fun x hx => hY'V hx)
      _ = Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) VZ
            (q.comp (ContinuousMap.id E)) (fun x hx => hY'V hx) :=
          Work.Serre.csrAsm_pair_congr (ContinuousMap.ext (fun x => rfl)) _ _
      _ = Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) (q ⁻¹' VZ)
              (ContinuousMap.id E) (fun x hx => hY'V hx)
          ≫ Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (by intro x hx; exact hx) :=
          (Work.Serre.csrAsm_pair_comp (ContinuousMap.id E) q
            (fun x hx => hY'V hx) (by intro x hx; exact hx)
            (hg'' := fun x hx => hY'V hx)).symm
  -- ## 4. The cover by the open cells and the complement of the centres
  have hcovE : q ⁻¹' UZ ∪ q ⁻¹' VZ = Set.univ := by
    rw [← Set.preimage_union, show UZ ∪ VZ = Set.univ from hcover, Set.preimage_univ]
  have hexcE : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' UZ) (q ⁻¹' VZ)) m) :=
    fun m => csrExcisionRat (TopCat.of E) (q ⁻¹' UZ) (q ⁻¹' VZ) (hUZopen.preimage q.continuous)
      (hVZopen.preimage q.continuous) hcovE m
  have hexcZ : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of (attachOneCells Y ι f)) UZ VZ) m) :=
    fun m => csrExcisionRat (TopCat.of (attachOneCells Y ι f)) UZ VZ hUZopen hVZopen hcover m
  have hmapTot : Work.Cohomology.subtypeIncl (TopCat.of E) (q ⁻¹' UZ) ≫ TopCat.ofHom q
      = TopCat.ofHom (csrRestrict q UZ)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (attachOneCells Y ι f)) UZ := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hsq2 :
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' UZ) (q ⁻¹' VZ))
        ≫ (Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (fun _ hx => hx))
      = (midUMapOne Y ι f q)
        ≫ (Work.Serre.relChainsRInclPairMap
            (TopCat.of (attachOneCells Y ι f)) UZ VZ) := by
    unfold midUMapOne Work.Serre.relChainsRInclPairMap Work.Serre.relChainsRPairMap
    rw [Work.Serre.csrRelMapOf_comp, Work.Serre.csrRelMapOf_comp]
    refine Work.Serre.CsrSharp.Tools.csrRelMapOf_congr ?_ ?_ ?_ ?_
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
  -- ## 5. The sharpness of the middle map over the union, from the per-cell statements
  have hcell : ∀ i : ι, (∀ m : ℕ, m < 1 + φ → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) m)) ∧
      Function.Surjective (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i)
        (1 + φ)).hom :=
    fun i => perCellSharpOne Y ι f q hq φ hfib h0 i
  have hmidU := oneCellUnionSharp Y ι f q φ hcell
  have hmidViso : ∀ m : ℕ, m < 1 + φ → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (fun _ hx => hx)) m) := by
    intro m hm
    refine Work.Serre.CsrSharp.Tools.isIso_of_sq_right
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' UZ) (q ⁻¹' VZ))
      (Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (fun _ hx => hx))
      (midUMapOne Y ι f q)
      (Work.Serre.relChainsRInclPairMap (TopCat.of (attachOneCells Y ι f)) UZ VZ) hsq2 m
      (hexcE m) (hmidU.1 m hm) (hexcZ m)
  have hmidVsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (fun _ hx => hx)) (1 + φ)).hom :=
    Work.Serre.CsrSharp.Tools.surjective_of_sq_right
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' UZ) (q ⁻¹' VZ))
      (Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (fun _ hx => hx))
      (midUMapOne Y ι f q)
      (Work.Serre.relChainsRInclPairMap (TopCat.of (attachOneCells Y ι f)) UZ VZ) hsq2 (1 + φ)
      (hmidU.2)
      ((ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRInclPairMap
          (TopCat.of (attachOneCells Y ι f)) UZ VZ) (1 + φ))).2)
  -- ## 6. Conclusion
  refine ⟨?_, ?_⟩
  · intro i hi
    exact Work.Serre.CsrSharp.Tools.isIso_of_sq_left (Work.Serre.oneCellStepMap ι f q)
      (Work.Serre.relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
        (ContinuousMap.id (attachOneCells Y ι f)) hY'V)
      (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) (q ⁻¹' VZ)
        (ContinuousMap.id E) (fun x hx => hY'V hx))
      (Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (fun _ hx => hx)) hsq1 i
      (hr3 i) (hr1 i) (hmidViso i hi)
  · exact Work.Serre.CsrSharp.Tools.surjective_of_sq_left (Work.Serre.oneCellStepMap ι f q)
      (Work.Serre.relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
        (ContinuousMap.id (attachOneCells Y ι f)) hY'V)
      (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) (q ⁻¹' VZ)
        (ContinuousMap.id E) (fun x hx => hY'V hx))
      (Work.Serre.relChainsRPairMap (q ⁻¹' VZ) VZ q (fun _ hx => hx)) hsq1 (1 + φ)
      ((ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
          (ContinuousMap.id (attachOneCells Y ι f)) hY'V) (1 + φ))).1)
      ((ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) (q ⁻¹' VZ)
          (ContinuousMap.id E) (fun x hx => hY'V hx)) (1 + φ))).2)
      hmidVsurj


end

end Work.Serre.B1Rel
