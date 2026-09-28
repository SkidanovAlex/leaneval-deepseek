import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.cellStepRelHomologyIso
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.OneCell.Defs
import Submission.Work.Serre.OneCell.OneCellGeom
import Submission.Work.Serre.OneCell.RatMap
import Submission.Work.Serre.OneCell.Halves
import Submission.Work.Serre.OneCell.oneCellPerCell
import Submission.Work.Serre.OneCell.compressRel_cellPunctured
import Submission.Work.Serre.csrAssembly
import Submission.Work.Serre.csrMid

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

/-- The `1`-cell case of the cell step of the cellular proof of E3(a).

`Z := Work.Serre.attachOneCells Y ι f` is `Y` with `1`-cells (intervals) attached along the maps
`f : ι → C(S⁰, Y)` (the workspace's `Work.RatHurewicz.attachCells n` only attaches cells of
dimension `n+2 ≥ 2`, so the `1`-dimensional case is a separate construction, defined in
`Submission/Work/Serre/E3aDefs.lean`), and `q : E → Z` is a Serre fibration whose fibres are
rationally acyclic below `N` and rationally connected (`H_0 ≅ ℚ` for every fibre).

Then the map of relative chain complexes `Work.Serre.oneCellStepMap ι f q : C_*(E, q⁻¹Y;ℚ) →
C_*(Z, Y;ℚ)` induced by `q` (here `Y` is identified with `Set.range (oneIncl Y ι f) ⊆ Z` and
`q⁻¹Y` with its preimage in `E`) is an isomorphism on `i`-th homology for every `i ≤ N`.

Proof: the same scheme as `Work.Serre.cellStepRelHomologyIso` with cell dimension `1` — excision
plus the compression of the interval onto its boundary (lifted by the cube HLP) reduce both sides to
a direct sum over the cells: `H_i(E, q⁻¹Y;ℚ) ≅ ⊕_α H_{i-1}(F_α;ℚ)` (this is
`Work.Serre.SerreE2d`/`SerreE2c` at `n = 1`, already proved; the model disc `D¹ = [-1,1]` is
homeomorphic to the cube `I¹`) and `H_i(Z,Y;ℚ) ≅ ⊕_α H_{i-1}(pt;ℚ) = ⊕_α ℚ` in degree `1`, `0`
else (the standard computation of the interval pair).  In degree `0` both sides vanish (the fibres
are connected and the HLP gives path lifting); in degree `1` the termwise comparison is
`H_0(F_α;ℚ) ≅ ℚ`; in degrees `2 ≤ i ≤ N` both sides are `0`. -/
theorem oneCellStepRelHomologyIso (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : ∀ z : Work.Serre.attachOneCells Y ι f,
      (∀ k : ℕ, 0 < k → k ≤ N → CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology k)) ∧
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ))
    (i : ℕ) (hi : i ≤ N) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.oneCellStepMap ι f q) i) := by
  classical
  -- ## The sets
  -- `UZ` : the union of the open cells; `PZ` : the centres; `VZ` : the complement of the centres.
  set UZ : Set (attachOneCells Y ι f) := OneCell.cellInnerUnionOne Y ι f with hUZ
  set PZ : Set (attachOneCells Y ι f) := OneCell.oneCellCentresOne Y ι f with hPZ
  set VZ : Set (attachOneCells Y ι f) := (OneCell.oneCellCentresOne Y ι f)ᶜ with hVZ
  set UE : Set E := q ⁻¹' UZ with hUE
  set VE : Set E := q ⁻¹' VZ with hVE
  set AU : Set ↥UE := {x : ↥UE | (x : E) ∈ q ⁻¹' (UZ \ PZ)} with hAU
  set AE : Set ↥UE := {x : ↥UE | (x : E) ∈ VE} with hAE
  set BU : Set ↥UZ := {x : ↥UZ | (x : attachOneCells Y ι f) ∈ UZ \ PZ} with hBU
  set BZ : Set ↥UZ := {x : ↥UZ | (x : attachOneCells Y ι f) ∈ VZ} with hBZ
  -- ## Elementary facts
  have hClosedP : IsClosed PZ := by
    obtain ⟨-, -, -, -, -, -, -, h⟩ := OneCell.oneCellGeometry (Y := Y) (ι := ι) f
    exact h
  have hUZopen : IsOpen UZ :=
    OneCell.isOpen_cellUnionOne (Y := Y) (ι := ι) (f := f) (U := OneCell.cellInnerOne)
      (fun x hx => hx) OneCell.isOpen_cellInnerOne
  have hVZopen : IsOpen VZ := hClosedP.isOpen_compl
  have hPZsubUZ : PZ ⊆ UZ := by
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    exact Set.mem_iUnion.mpr ⟨i, OneCell.oneCellCentreOne_mem_cellInteriorOne (Y := Y) (ι := ι) f i⟩
  have hcovUV : UZ ∪ VZ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    by_cases h : z ∈ PZ
    · exact Or.inl (hPZsubUZ h)
    · exact Or.inr h
  have hUEopen : IsOpen UE := hUZopen.preimage q.continuous
  have hVEopen : IsOpen VE := hVZopen.preimage q.continuous
  have hcovUEVE : UE ∪ VE = Set.univ := by
    rw [hUE, hVE, ← Set.preimage_union, hcovUV, Set.preimage_univ]
  -- the old part sits inside the complement of the centres
  have hY'V : Set.range (oneIncl Y ι f) ⊆ VZ := by
    intro z hz
    rw [hVZ, Set.mem_compl_iff]
    simp only [OneCell.mem_oneCellCentresOne]
    rintro ⟨i, hi⟩
    exact OneCell.oneCellCentreOne_not_mem_oldPart (Y := Y) (ι := ι) f i (hi ▸ hz)
  -- ## The compression of `Z ∖ P` onto the old part, and its preimage
  have hcompV : ∀ d, Work.RatHurewicz.CompressRel ↥VZ
      {x : ↥VZ | (x : attachOneCells Y ι f) ∈ Set.range (oneIncl Y ι f)} d :=
    fun d => OneCell.compressRel_cellPunctured Y ι f d
  have hVzero : ∀ m : ℕ, IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of ↥VZ)
      {x : ↥VZ | (x : attachOneCells Y ι f) ∈ Set.range (oneIncl Y ι f)}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m
      (isZero_relChains_of_compress hcompV m)
  have hEzero : ∀ m : ℕ, IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of ↥VE)
      {x : ↥VE | (x : E) ∈ q ⁻¹' Set.range (oneIncl Y ι f)}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m
      (isZero_relChains_preimage_of_compress q hq
        (W₀ := Set.range (oneIncl Y ι f)) (W := VZ) hY'V hcompV m)
  -- ## The two compression isomorphisms
  haveI hisoα : IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) VE (ContinuousMap.id E)
        (by intro x hx; exact hY'V hx)) i) :=
    csrRelIso (q ⁻¹' Set.range (oneIncl Y ι f)) VE (fun x hx => hY'V hx) hEzero i
  haveI hisoγ : IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
        (ContinuousMap.id (attachOneCells Y ι f)) hY'V) i) :=
    csrRelIso (Set.range (oneIncl Y ι f)) VZ hY'V hVzero i
  -- ## The middle map is an isomorphism (excision + the per-cell model)
  have hAUE : AU ⊆ AE := fun x hx => hx.2
  have hAEAU : AE ⊆ AU := fun x hx => ⟨x.2, hx⟩
  have hBUZ : BU ⊆ BZ := fun x hx => hx.2
  have hBZBU : BZ ⊆ BU := fun x hx => ⟨x.2, hx⟩
  haveI hMid : IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap VE VZ q (by intro x hx; exact hx)) i) := by
    let cidUE : C(↥UE, ↥UE) := ContinuousMap.id ↥UE
    let cidUZ : C(↥UZ, ↥UZ) := ContinuousMap.id ↥UZ
    let gsubE : C(↥UE, E) := ⟨Subtype.val, continuous_subtype_val⟩
    let gsubZ : C(↥UZ, attachOneCells Y ι f) := ⟨Subtype.val, continuous_subtype_val⟩
    -- the excision maps, written as relative pair maps
    have hEqE : relChainsRInclPairMap (TopCat.of E) UE VE
        = relChainsRPairMap AE VE gsubE (by intro x hx; exact hx) :=
      csrAsm_inclPairMap_eq (TopCat.of E) UE VE
    have hEqZ : relChainsRInclPairMap (TopCat.of (attachOneCells Y ι f)) UZ VZ
        = relChainsRPairMap BZ VZ gsubZ (by intro x hx; exact hx) :=
      csrAsm_inclPairMap_eq (TopCat.of (attachOneCells Y ι f)) UZ VZ
    -- the excision isomorphisms
    have hexcE : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (relChainsRInclPairMap (TopCat.of E) UE VE) i) :=
      csrExcisionRat (TopCat.of E) UE VE hUEopen hVEopen hcovUEVE i
    have hexcZ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (relChainsRInclPairMap (TopCat.of (attachOneCells Y ι f)) UZ VZ) i) :=
      csrExcisionRat (TopCat.of (attachOneCells Y ι f)) UZ VZ hUZopen hVZopen hcovUV i
    -- the change-of-relative-part maps and their inverse laws
    have hthetaE : relChainsRPairMap AU AE cidUE hAUE
        ≫ relChainsRPairMap AE AU cidUE hAEAU = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥UE) AU))).1
      rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
        cokernel_π_relChainsRPairMap, Category.comp_id,
        ← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]
      rw [show TopCat.ofHom (cidUE.comp cidUE) = 𝟙 (TopCat.of ↥UE) from by
          rw [TopCat.ofHom_comp, TopCat.ofHom_id, Category.comp_id]]
      have h2 : Work.Cohomology.chainMap ℚ (TopCat.of ↥UE) (TopCat.of ↥UE)
          (𝟙 (TopCat.of ↥UE)) = 𝟙 _ :=
        CategoryTheory.Functor.map_id _ _
      rw [h2, Category.id_comp]
    have hthetaE' : relChainsRPairMap AE AU cidUE hAEAU
        ≫ relChainsRPairMap AU AE cidUE hAUE = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥UE) AE))).1
      rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
        cokernel_π_relChainsRPairMap, Category.comp_id,
        ← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]
      rw [show TopCat.ofHom (cidUE.comp cidUE) = 𝟙 (TopCat.of ↥UE) from by
          rw [TopCat.ofHom_comp, TopCat.ofHom_id, Category.comp_id]]
      have h2 : Work.Cohomology.chainMap ℚ (TopCat.of ↥UE) (TopCat.of ↥UE)
          (𝟙 (TopCat.of ↥UE)) = 𝟙 _ :=
        CategoryTheory.Functor.map_id _ _
      rw [h2, Category.id_comp]
    have hthetaU : relChainsRPairMap BU BZ cidUZ hBUZ
        ≫ relChainsRPairMap BZ BU cidUZ hBZBU = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥UZ) BU))).1
      rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
        cokernel_π_relChainsRPairMap, Category.comp_id,
        ← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]
      rw [show TopCat.ofHom (cidUZ.comp cidUZ) = 𝟙 (TopCat.of ↥UZ) from by
          rw [TopCat.ofHom_comp, TopCat.ofHom_id, Category.comp_id]]
      have h2 : Work.Cohomology.chainMap ℚ (TopCat.of ↥UZ) (TopCat.of ↥UZ)
          (𝟙 (TopCat.of ↥UZ)) = 𝟙 _ :=
        CategoryTheory.Functor.map_id _ _
      rw [h2, Category.id_comp]
    have hthetaU' : relChainsRPairMap BZ BU cidUZ hBZBU
        ≫ relChainsRPairMap BU BZ cidUZ hBUZ = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥UZ) BZ))).1
      rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
        cokernel_π_relChainsRPairMap, Category.comp_id,
        ← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]
      rw [show TopCat.ofHom (cidUZ.comp cidUZ) = 𝟙 (TopCat.of ↥UZ) from by
          rw [TopCat.ofHom_comp, TopCat.ofHom_id, Category.comp_id]]
      have h2 : Work.Cohomology.chainMap ℚ (TopCat.of ↥UZ) (TopCat.of ↥UZ)
          (𝟙 (TopCat.of ↥UZ)) = 𝟙 _ :=
        CategoryTheory.Functor.map_id _ _
      rw [h2, Category.id_comp]
    haveI hIE : IsIso (relChainsRPairMap AU AE cidUE hAUE) :=
      ⟨relChainsRPairMap AE AU cidUE hAEAU, hthetaE, hthetaE'⟩
    haveI hIU : IsIso (relChainsRPairMap BU BZ cidUZ hBUZ) :=
      ⟨relChainsRPairMap BZ BU cidUZ hBZBU, hthetaU, hthetaU'⟩
    -- the per-cell comparison
    haveI hIstep : IsIso (HomologicalComplex.homologyMap
        (relChainsRPairMap AU BU (csrRestrict q UZ) (by intro x hx; exact hx)) i) :=
      OneCell.oneCellPerCell Y ι f q hq N hacyc i hi
    -- the comparison square
    have hsq : relChainsRPairMap AU AE cidUE hAUE
          ≫ relChainsRInclPairMap (TopCat.of E) UE VE
          ≫ relChainsRPairMap VE VZ q (by intro x hx; exact hx)
        = relChainsRPairMap AU BU (csrRestrict q UZ) (by intro x hx; exact hx)
          ≫ relChainsRPairMap BU BZ cidUZ hBUZ
          ≫ relChainsRInclPairMap (TopCat.of (attachOneCells Y ι f)) UZ VZ := by
      rw [hEqE, hEqZ]
      rw [csrAsm_pair_comp (A := AE) (B := VE) (C := VZ) gsubE q
        (by intro x hx; exact hx) (by intro x hx; exact hx)
        (hg'' := fun x hx => hx)]
      rw [csrAsm_pair_comp (A := AU) (B := AE) (C := VZ) cidUE (q.comp gsubE) hAUE
        (by intro x hx; exact hx) (hg'' := fun x hx => hx.2)]
      rw [csrAsm_pair_comp (A := BU) (B := BZ) (C := VZ) cidUZ gsubZ hBUZ
        (by intro x hx; exact hx) (hg'' := fun x hx => hx.2)]
      rw [csrAsm_pair_comp (A := AU) (B := BU) (C := VZ) (csrRestrict q UZ) (gsubZ.comp cidUZ)
        (by intro x hx; exact hx) (fun x hx => hx.2) (hg'' := fun x hx => hx.2)]
      exact csrAsm_pair_congr (ContinuousMap.ext (fun x => rfl)) _ _
    -- conclude at the level of homology
    have hL : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (relChainsRPairMap AU AE cidUE hAUE
          ≫ (relChainsRInclPairMap (TopCat.of E) UE VE
              ≫ relChainsRPairMap VE VZ q (by intro x hx; exact hx))) i) := by
      have h := congrArg (fun φ => HomologicalComplex.homologyMap φ i) hsq
      rw [h, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
      infer_instance
    have hL1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
          (relChainsRPairMap AU AE cidUE hAUE) i
        ≫ HomologicalComplex.homologyMap
            (relChainsRInclPairMap (TopCat.of E) UE VE
              ≫ relChainsRPairMap VE VZ q (by intro x hx; exact hx)) i) := by
      rw [← HomologicalComplex.homologyMap_comp]; exact hL
    haveI := hL1
    have hStep : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (relChainsRInclPairMap (TopCat.of E) UE VE
          ≫ relChainsRPairMap VE VZ q (by intro x hx; exact hx)) i) :=
      CategoryTheory.IsIso.of_isIso_comp_left
        (HomologicalComplex.homologyMap (relChainsRPairMap AU AE cidUE hAUE) i) _
    have hS1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
          (relChainsRInclPairMap (TopCat.of E) UE VE) i
        ≫ HomologicalComplex.homologyMap (relChainsRPairMap VE VZ q (by intro x hx; exact hx)) i) := by
      rw [← HomologicalComplex.homologyMap_comp]; exact hStep
    haveI := hS1
    exact CategoryTheory.IsIso.of_isIso_comp_left
      (HomologicalComplex.homologyMap (relChainsRInclPairMap (TopCat.of E) UE VE) i) _
  -- ## `oneCellStepMap` is the relative pair map of `q`
  have honeCell : oneCellStepMap ι f q
      = relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) (Set.range (oneIncl Y ι f)) q
          (by intro x hx; exact hx) := by
    unfold oneCellStepMap oneCellStepRestrict relChainsRPairMap csrRelMapOf
    apply csrAsm_cokernelMap_congr
    · refine congrArg (fun φ => Work.Cohomology.chainMap ℚ
        (TopCat.of {e : E | q e ∈ Set.range (oneIncl Y ι f)})
        (TopCat.of (Set.range (oneIncl Y ι f))) φ) ?_
      exact congrArg TopCat.ofHom (ContinuousMap.ext (fun x => Subtype.ext rfl))
    · rfl
  -- ## The comparison square for the whole step
  have hsquare : oneCellStepMap ι f q
        ≫ relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
            (ContinuousMap.id (attachOneCells Y ι f)) hY'V
      = relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) VE (ContinuousMap.id E)
          (fun x hx => hY'V hx)
        ≫ relChainsRPairMap VE VZ q (by intro x hx; exact hx) := by
    rw [honeCell]
    calc relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) (Set.range (oneIncl Y ι f)) q
            (by intro x hx; exact hx)
          ≫ relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
              (ContinuousMap.id (attachOneCells Y ι f)) hY'V
        = relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) VZ
            ((ContinuousMap.id (attachOneCells Y ι f)).comp q)
            (fun x hx => hY'V hx) :=
          csrAsm_pair_comp q (ContinuousMap.id (attachOneCells Y ι f))
            (by intro x hx; exact hx) hY'V (hg'' := fun x hx => hY'V hx)
      _ = relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) VZ
            (q.comp (ContinuousMap.id E)) (fun x hx => hY'V hx) :=
          csrAsm_pair_congr (ContinuousMap.ext (fun x => rfl)) _ _
      _ = relChainsRPairMap (q ⁻¹' Set.range (oneIncl Y ι f)) VE (ContinuousMap.id E)
              (fun x hx => hY'V hx)
          ≫ relChainsRPairMap VE VZ q (by intro x hx; exact hx) :=
          (csrAsm_pair_comp (ContinuousMap.id E) q (fun x hx => hY'V hx)
            (by intro x hx; exact hx) (hg'' := fun x hx => hY'V hx)).symm
  -- ## Conclusion
  have hsq' := congrArg (fun φ => HomologicalComplex.homologyMap φ i) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq'
  have hfinal : CategoryTheory.IsIso (HomologicalComplex.homologyMap (oneCellStepMap ι f q) i
      ≫ HomologicalComplex.homologyMap
          (relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
            (ContinuousMap.id (attachOneCells Y ι f)) hY'V) i) := by
    rw [hsq']; infer_instance
  exact CategoryTheory.IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap (oneCellStepMap ι f q) i)
    (HomologicalComplex.homologyMap
      (relChainsRPairMap (Set.range (oneIncl Y ι f)) VZ
        (ContinuousMap.id (attachOneCells Y ι f)) hY'V) i)

end

end Work.Serre
