import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGeom
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Serre.csrAssembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The middle step of the rational cell step

`Work.Serre.csrAssembly` reduces the rational cell step to the comparison of the preimage pair over
`V = csrV` (the complement of the cell centres).  This file further reduces it to the comparison
over the open cover `{q⁻¹U, q⁻¹V}`, `U = ⋃ i, csrOpenBall i`: excision identifies the comparison
over `(E, q⁻¹V) → (Z, V)` with the comparison over the union, which is the cell-wise statement
`Work.Serre.csrUnionIso`.

The two relative parts of the excision statement are spelled with `q⁻¹V` and `V`, whereas the
cell-wise comparison uses the (equal) sets `q⁻¹(U ∩ V)` and `U ∩ V`; the two spellings are related
by the identity map of the underlying space, which is an isomorphism on relative chains because the
sets agree.  This is `Work.Serre.csrMidIso`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

/-- The inclusion of pairs `(U, U ∩ A) → (X, A)` is the relative pair map of the inclusion
`U ↪ X` (the two spellings of the comparison map agree). -/
theorem csrAsm_inclPairMap_eq (X : TopCat) (U A : Set X) :
    relChainsRInclPairMap X U A
      = relChainsRPairMap {x : ↥U | (x : X) ∈ A} A
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) (by intro x hx; exact hx) := by
  unfold relChainsRInclPairMap relChainsRPairMap csrRelMapOf
  apply csrAsm_cokernelMap_congr
  · refine congrArg (fun φ => Work.Cohomology.chainMap ℚ
      (TopCat.of {x : ↥U | (x : X) ∈ A}) (TopCat.of A) φ) ?_
    exact congrArg TopCat.ofHom (ContinuousMap.ext (fun x => Subtype.ext rfl))
  · rfl

/-- **The middle step of the rational cell step.**  If the cell-wise comparison over the union
`U = ⋃ i, csrOpenBall i` of the open half-balls is an isomorphism on rational homology in degrees
`≤ N`, then so is the comparison over the complement of the cell centres. -/
theorem csrMidIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (N : ℕ)
    (hUstep : ∀ m : ℕ, m ≤ N → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (X := ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)))
        (Y := ↥(⋃ i, csrOpenBall n Y ι f i))
        {x : ↥(q ⁻¹' (⋃ i, csrOpenBall n Y ι f i)) |
          (x : E) ∈ q ⁻¹' ((⋃ i, csrOpenBall n Y ι f i) ∩ csrV n Y ι f)}
        {x : ↥(⋃ i, csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            (⋃ i, csrOpenBall n Y ι f i) ∩ csrV n Y ι f}
        (csrRestrict q (⋃ i, csrOpenBall n Y ι f i)) (by intro x hx; exact hx)) m))
    (m : ℕ) (hm : m ≤ N) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (X := E)
        (Y := Work.RatHurewicz.attachCells n Y ι f)
        (q ⁻¹' csrV n Y ι f) (csrV n Y ι f) q (by intro x hx; exact hx)) m) := by
  classical
  obtain ⟨hopen, -, -, -, hcentre, -, hdisj, -, -, hVopen, hcover, hcap⟩ := csrGeom n Y ι f
  set U : Set (Work.RatHurewicz.attachCells n Y ι f) := ⋃ i, csrOpenBall n Y ι f i with hUdef
  set V : Set (Work.RatHurewicz.attachCells n Y ι f) := csrV n Y ι f with hVdef
  set W : Set E := q ⁻¹' U with hWdef
  set B : Set E := q ⁻¹' V with hBdef
  set AU : Set ↥W := {x : ↥W | (x : E) ∈ q ⁻¹' (U ∩ V)} with hAUdef
  set BU : Set ↥U := {x : ↥U | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ U ∩ V}
    with hBUdef
  let AE : Set ↥W := {x : ↥W | (x : E) ∈ B}
  let AZ : Set ↥U := {x : ↥U | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ V}
  let gsubE : C(↥W, E) := ⟨Subtype.val, continuous_subtype_val⟩
  let gsubZ : C(↥U, Work.RatHurewicz.attachCells n Y ι f) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let cidW : C(↥W, ↥W) := ContinuousMap.id ↥W
  let cidU : C(↥U, ↥U) := ContinuousMap.id ↥U
  have hUopen : IsOpen U := by rw [hUdef]; exact isOpen_iUnion fun i => hopen i
  have hWopen : IsOpen W := by rw [hWdef]; exact hUopen.preimage q.continuous
  have hBopen : IsOpen B := by rw [hBdef]; exact hVopen.preimage q.continuous
  have hcov : W ∪ B = Set.univ := by
    rw [hWdef, hBdef, ← Set.preimage_union, hcover, Set.preimage_univ]
  have hAUE : AU ⊆ AE := fun x hx => hx.2
  have hAEAU : AE ⊆ AU := fun x hx => ⟨x.2, hx⟩
  have hBUAZ : BU ⊆ AZ := fun x hx => hx.2
  have hAZBU : AZ ⊆ BU := fun x hx => ⟨x.2, hx⟩
  -- the two excision isomorphisms
  have hexcE : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRInclPairMap (TopCat.of E) W B) m) :=
    csrExcisionRat (TopCat.of E) W B hWopen hBopen hcov m
  have hexcZ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRInclPairMap (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U V) m) :=
    csrExcisionRat (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U V hUopen hVopen hcover m
  -- the identification of the excision maps with relative pair maps
  have hEqE : relChainsRInclPairMap (TopCat.of E) W B
      = relChainsRPairMap AE B gsubE (by intro x hx; exact hx) :=
    csrAsm_inclPairMap_eq (TopCat.of E) W B
  have hEqZ : relChainsRInclPairMap (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U V
      = relChainsRPairMap AZ V gsubZ (by intro x hx; exact hx) :=
    csrAsm_inclPairMap_eq (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U V
  -- the two "change of relative part" maps and their inverse laws
  have hthetaE : relChainsRPairMap AU AE cidW hAUE
      ≫ relChainsRPairMap AE AU cidW hAEAU = 𝟙 _ := by
    apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥W) AU))).1
    rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
      cokernel_π_relChainsRPairMap, Category.comp_id,
      ← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]
    rw [show TopCat.ofHom (cidW.comp cidW) = 𝟙 (TopCat.of ↥W) from by
        rw [TopCat.ofHom_comp, TopCat.ofHom_id, Category.comp_id]]
    have h2 : Work.Cohomology.chainMap ℚ (TopCat.of ↥W) (TopCat.of ↥W) (𝟙 (TopCat.of ↥W)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [h2, Category.id_comp]
  have hthetaE' : relChainsRPairMap AE AU cidW hAEAU
      ≫ relChainsRPairMap AU AE cidW hAUE = 𝟙 _ := by
    apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥W) AE))).1
    rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
      cokernel_π_relChainsRPairMap, Category.comp_id,
      ← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]
    rw [show TopCat.ofHom (cidW.comp cidW) = 𝟙 (TopCat.of ↥W) from by
        rw [TopCat.ofHom_comp, TopCat.ofHom_id, Category.comp_id]]
    have h2 : Work.Cohomology.chainMap ℚ (TopCat.of ↥W) (TopCat.of ↥W) (𝟙 (TopCat.of ↥W)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [h2, Category.id_comp]
  have hthetaU : relChainsRPairMap BU AZ cidU hBUAZ
      ≫ relChainsRPairMap AZ BU cidU hAZBU = 𝟙 _ := by
    apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥U) BU))).1
    rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
      cokernel_π_relChainsRPairMap, Category.comp_id,
      ← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]
    rw [show TopCat.ofHom (cidU.comp cidU) = 𝟙 (TopCat.of ↥U) from by
        rw [TopCat.ofHom_comp, TopCat.ofHom_id, Category.comp_id]]
    have h2 : Work.Cohomology.chainMap ℚ (TopCat.of ↥U) (TopCat.of ↥U) (𝟙 (TopCat.of ↥U)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [h2, Category.id_comp]
  have hthetaU' : relChainsRPairMap AZ BU cidU hAZBU
      ≫ relChainsRPairMap BU AZ cidU hBUAZ = 𝟙 _ := by
    apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥U) AZ))).1
    rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
      cokernel_π_relChainsRPairMap, Category.comp_id,
      ← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]
    rw [show TopCat.ofHom (cidU.comp cidU) = 𝟙 (TopCat.of ↥U) from by
        rw [TopCat.ofHom_comp, TopCat.ofHom_id, Category.comp_id]]
    have h2 : Work.Cohomology.chainMap ℚ (TopCat.of ↥U) (TopCat.of ↥U) (𝟙 (TopCat.of ↥U)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [h2, Category.id_comp]
  haveI hIE : CategoryTheory.IsIso (relChainsRPairMap AU AE cidW hAUE) :=
    ⟨relChainsRPairMap AE AU cidW hAEAU, hthetaE, hthetaE'⟩
  haveI hIU : CategoryTheory.IsIso (relChainsRPairMap BU AZ cidU hBUAZ) :=
    ⟨relChainsRPairMap AZ BU cidU hAZBU, hthetaU, hthetaU'⟩
  haveI hIstep : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap AU BU (csrRestrict q U) (by intro x hx; exact hx)) m) :=
    hUstep m hm
  -- the comparison square
  have hsq : relChainsRPairMap AU AE cidW hAUE
        ≫ relChainsRInclPairMap (TopCat.of E) W B
        ≫ relChainsRPairMap B V q (by intro x hx; exact hx)
      = relChainsRPairMap AU BU (csrRestrict q U) (by intro x hx; exact hx)
        ≫ relChainsRPairMap BU AZ cidU hBUAZ
        ≫ relChainsRInclPairMap (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U V := by
    rw [hEqE, hEqZ]
    rw [csrAsm_pair_comp (A := AE) (B := B) (C := V) gsubE q
      (by intro x hx; exact hx) (by intro x hx; exact hx)
      (hg'' := fun x hx => hx)]
    rw [csrAsm_pair_comp (A := AU) (B := AE) (C := V) cidW (q.comp gsubE) hAUE
      (by intro x hx; exact hx) (hg'' := fun x hx => hx.2)]
    rw [csrAsm_pair_comp (A := BU) (B := AZ) (C := V) cidU gsubZ hBUAZ
      (by intro x hx; exact hx) (hg'' := fun x hx => hx.2)]
    rw [csrAsm_pair_comp (A := AU) (B := BU) (C := V) (csrRestrict q U) (gsubZ.comp cidU)
      (by intro x hx; exact hx) (fun x hx => hx.2) (hg'' := fun x hx => hx.2)]
    exact csrAsm_pair_congr (ContinuousMap.ext (fun x => rfl)) _ _
  -- conclude at the level of homology
  have hL : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap AU AE cidW hAUE
        ≫ (relChainsRInclPairMap (TopCat.of E) W B
            ≫ relChainsRPairMap B V q (by intro x hx; exact hx))) m) := by
    have h := congrArg (fun φ => HomologicalComplex.homologyMap φ m) hsq
    rw [h, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    infer_instance
  have hL1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (relChainsRPairMap AU AE cidW hAUE) m
      ≫ HomologicalComplex.homologyMap
          (relChainsRInclPairMap (TopCat.of E) W B
            ≫ relChainsRPairMap B V q (by intro x hx; exact hx)) m) := by
    rw [← HomologicalComplex.homologyMap_comp]; exact hL
  haveI := hL1
  have hStep : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRInclPairMap (TopCat.of E) W B
        ≫ relChainsRPairMap B V q (by intro x hx; exact hx)) m) :=
    CategoryTheory.IsIso.of_isIso_comp_left
      (HomologicalComplex.homologyMap (relChainsRPairMap AU AE cidW hAUE) m) _
  have hS1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (relChainsRInclPairMap (TopCat.of E) W B) m
      ≫ HomologicalComplex.homologyMap (relChainsRPairMap B V q (by intro x hx; exact hx)) m) := by
    rw [← HomologicalComplex.homologyMap_comp]; exact hStep
  haveI := hS1
  exact CategoryTheory.IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (relChainsRInclPairMap (TopCat.of E) W B) m) _

end

end Work.Serre
