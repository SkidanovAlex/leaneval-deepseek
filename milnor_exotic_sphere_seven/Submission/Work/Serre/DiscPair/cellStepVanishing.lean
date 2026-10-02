import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.StemsB.RelChainsR
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.CsrSharp.cellStepSharpIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of the relative rational homology below the cell dimension

Let `Z = Work.RatHurewicz.attachCells n Y ι f` be obtained from `Y` by attaching `(n+2)`-cells
along the maps `f i : S^{n+1} → Y`, write `Y' = Set.range (attachIncl n Y ι f) ⊆ Z` for the old
part, and let `q : C(E, Z)` be a Serre fibration.

The main result of this file is that the *relative* rational homology of the total space of `q`
below the cell dimension vanishes:

`H_j(E, q⁻¹Y'; ℚ) = 0` for `j < n+2`,

and the same for the base (`E = Z`, `q = id`).  Both are specialisations of a single statement
(`isZero_relChainsR_homology_preimage_of_lt`).

The proof is the low-degree part of the chain that computes the sharp relative homology in
`Work.Serre.CsrSharp.cellStepSharpIso`, which is degree-agnostic as long as one does not use the
per-cell computation in the cell dimension:

`H_j(E, q⁻¹Y') ≅ H_j(E, q⁻¹V)` (compression of the complement of the cell centres onto `Y'`),
`≅ H_j(q⁻¹U₀, q⁻¹(V ∩ U₀))` (excision, `U₀ = ⋃ᵢ csrOpenBall i`),
`≅ H_j(Σᵢ q⁻¹oᵢ, Σᵢ q⁻¹(oᵢ ∖ {cᵢ}))` (`Σᵢ q⁻¹oᵢ = q⁻¹U₀` since the open half-balls are disjoint),
`≅ ∐ᵢ H_j(q⁻¹oᵢ, q⁻¹(oᵢ ∖ {cᵢ}))` (additivity over the disjoint union),

and each piece vanishes for `j < n+2` (`Work.Serre.CsrSharp.Cell.sourceIsZero`), so the coproduct
of the pieces vanishes.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

/-- A coproduct of zero `ℚ`-modules is a zero object. -/
theorem isZero_coprod_of_isZero {ι : Type} (M : ι → ModuleCat ℚ)
    (h : ∀ i, CategoryTheory.Limits.IsZero (M i)) :
    CategoryTheory.Limits.IsZero (∐ M) := by
  classical
  haveI : ∀ i, Subsingleton (↥(M i)) := fun i => ModuleCat.subsingleton_of_isZero (h i)
  rw [ModuleCat.isZero_iff_subsingleton]
  have e := ModuleCat.coprodIsoDirectSum M
  haveI : Subsingleton (DirectSum ι fun i => ↥(M i)) := inferInstance
  exact Equiv.subsingleton e.toLinearEquiv.toEquiv

set_option maxHeartbeats 1000000 in
/-- **Vanishing of the relative rational homology below the cell dimension.**  For a Serre
fibration `q : E → Z` over `Z = attachCells n Y ι f`, the pair `(E, q⁻¹Y')` has vanishing relative
rational homology in every degree `j < n+2`. -/
theorem isZero_relChainsR_homology_preimage_of_lt (n : ℕ) (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (j : ℕ) (hj : j < n + 2) :
    CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of E)
        (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl n Y ι f))).homology j) := by
  classical
  let Y' : Set (Work.RatHurewicz.attachCells n Y ι f) :=
    Set.range (Work.RatHurewicz.attachIncl n Y ι f)
  let U₀ : Set (Work.RatHurewicz.attachCells n Y ι f) := ⋃ i, Work.Serre.csrOpenBall n Y ι f i
  let V : Set (Work.RatHurewicz.attachCells n Y ι f) := Work.Serre.csrV n Y ι f
  let X : ι → Type := fun i => ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)
  let A' : ∀ i, Set (X i) := fun i =>
    {u : X i | (u : E) ∈ q ⁻¹'
      (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})}
  obtain ⟨hopen, -, -, -, -, -, hdisjO, -, hcentre_inter, hVopen, hcover, -⟩ :=
    Work.Serre.csrGeom n Y ι f
  -- (1) the compression of `V = csrV` onto the old part `Y'`
  have hY'V : Y' ⊆ V := by
    rintro z ⟨y, rfl⟩ ⟨i, hi⟩
    refine Work.RatHurewicz.cellOrigin_notMem_range_attachIncl (f := f) i ?_
    change Work.Serre.csrCentre n Y ι f i ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)
    exact hi ▸ ⟨y, rfl⟩
  have hBzero : ∀ mm : ℕ, CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of ↥(q ⁻¹' V)) {x : ↥(q ⁻¹' V) | (x : E) ∈ q ⁻¹' Y'}).homology mm) :=
    fun mm => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ mm
      ((Work.Serre.csrCompress n Y ι f q hq mm).2)
  have hr1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E)
        (fun x hx => Set.preimage_mono hY'V hx)) j) :=
    Work.Serre.csrRelIso (q ⁻¹' Y') (q ⁻¹' V) (Set.preimage_mono hY'V) hBzero j
  have h1 : ((Work.StemsB.relChainsR ℚ (TopCat.of E) (q ⁻¹' Y')).homology j) ≅
      ((Work.StemsB.relChainsR ℚ (TopCat.of E) (q ⁻¹' V)).homology j) :=
    @asIso _ _ _ _ _ hr1
  -- (2) excision of the cover `{q⁻¹U₀, q⁻¹V}`
  have hUopen : IsOpen U₀ := by
    rw [show U₀ = ⋃ i, Work.Serre.csrOpenBall n Y ι f i from rfl]
    exact isOpen_iUnion fun i => hopen i
  have hcovE : q ⁻¹' U₀ ∪ q ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, show U₀ ∪ V = Set.univ from hcover, Set.preimage_univ]
  have hexcE : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)) j) :=
    Work.Serre.csrExcisionRat (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)
      (hUopen.preimage q.continuous) (hVopen.preimage q.continuous) hcovE j
  have h2 : ((Work.StemsB.relChainsR ℚ (TopCat.of E) (q ⁻¹' V)).homology j) ≅
      ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' U₀))
        {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V}).homology j) :=
    (@asIso _ _ _ _ _ hexcE).symm
  -- (3) the union of the half-balls is the disjoint sum of the half-balls
  obtain ⟨Φ, hΦ⟩ := Work.Serre.CsrSharp.cssSigmaPiecesUnionHomeo n Y ι f q
  have he : ∀ x : ↥(q ⁻¹' U₀),
      ((x : E) ∈ q ⁻¹' V ↔ Φ x ∈ {y : Σ i, X i | y.2 ∈ A' y.1}) := by
    intro x
    exact hΦ x
  have h3 : ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' U₀))
        {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V}).homology j) ≅
      ((Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i))
        {y : Σ i, X i | y.2 ∈ A' y.1}).homology j) :=
    (Work.Serre.CsrSharp.cssRelChainsRHomeomorphCompat ↥(q ⁻¹' U₀) (Σ i, X i)
      {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V} {y : Σ i, X i | y.2 ∈ A' y.1}
      Φ he j).some
  -- (4) the relative chains of the disjoint sum are the coproduct of the pieces
  obtain ⟨eX, -, -⟩ := Work.Serre.relChainsCoproductSquareRat (X := X) (Y := X) A' A'
    (fun i => ContinuousMap.id (X i)) (fun i => fun x hx => hx)
  have h4 : ((Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i))
        {y : Σ i, X i | y.2 ∈ A' y.1}).homology j) ≅
      (∐ fun i => (Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A' i)).homology j) :=
    HomologicalComplex.homologyMapIso eX j ≪≫
      (@asIso _ _ _ _ _
        (Work.Serre.isIso_sigmaHomologyMap
          (fun i => Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A' i)) j)).symm
  -- (5) every piece vanishes below the cell dimension
  have hpiece : ∀ i : ι, CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A' i)).homology j) :=
    fun i => Work.Serre.CsrSharp.Cell.sourceIsZero n Y ι f q hq i j hj
  have hcop : CategoryTheory.Limits.IsZero
      (∐ fun i => (Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A' i)).homology j) :=
    isZero_coprod_of_isZero _ hpiece
  exact IsZero.of_iso hcop (h1 ≪≫ h2 ≪≫ h3 ≪≫ h4)

/-- The corresponding statement for the base itself (`E = Z`, `q = id`): a space obtained from `Y`
by attaching `(n+2)`-cells has no relative rational homology below the cell dimension. -/
theorem isZero_relChainsR_homology_self_of_lt (n : ℕ) (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (j : ℕ) (hj : j < n + 2) :
    CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
        (Set.range (Work.RatHurewicz.attachIncl n Y ι f))).homology j) := by
  have h := isZero_relChainsR_homology_preimage_of_lt n Y ι f
    (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f))
    Work.StemsB.isSerreFibration_id j hj
  have hEq : (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) ⁻¹'
      Set.range (Work.RatHurewicz.attachIncl n Y ι f)
      = Set.range (Work.RatHurewicz.attachIncl n Y ι f) := by
    ext z
    simp
  simpa only [hEq] using h

theorem cellStepVanishing (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < n + 2) :
    CategoryTheory.Limits.IsZero
        ((Work.StemsB.relChainsR ℚ (TopCat.of E)
          (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl n Y ι f))).homology k) ∧
      CategoryTheory.Limits.IsZero
        ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
          (Set.range (Work.RatHurewicz.attachIncl n Y ι f))).homology k) :=
  ⟨isZero_relChainsR_homology_preimage_of_lt n Y ι f q hq k hk2,
    isZero_relChainsR_homology_self_of_lt n Y ι f k hk2⟩

end

end Work.Serre.DiscPair
