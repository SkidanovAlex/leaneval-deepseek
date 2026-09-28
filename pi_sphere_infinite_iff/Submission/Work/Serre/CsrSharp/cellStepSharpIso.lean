import Mathlib
import Submission.Work.Serre.cellStepSharp
import Submission.Work.Serre.CsrSharp.Cell.sourceIso
import Submission.Work.Serre.CsrSharp.Cell.sourceIsZero
import Submission.Work.Serre.sigmaRelHomologyIso
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The sharp relative homology of the total space of the cell step

`Work.Serre.CsrSharp.cellStepSharpIso` computes, in *every* degree, the relative rational homology
of the total space of a Serre fibration `q : E → Z` over `Z = attachCells n Y ι f` relative to the
preimage of the old part `Y' = range (attachIncl n Y ι f)`:

`H_{m+(n+2)}(E, q⁻¹Y'; ℚ) ≅ ⨁ᵢ H_m(F_{cᵢ}; ℚ)`,

the direct sum of the homology of the fibres over the centres `cᵢ = csrCentre n Y ι f i` of the
attached cells, in degree `m`.

The proof is a chain of six isomorphisms:

* `H(E, q⁻¹Y') ≅ H(E, q⁻¹V)` — compression of the complement `V = csrV` of the cell centres onto
  the old part (`Work.Serre.csrCompress` + `Work.Serre.csrRelIso`), unconditional;
* `H(E, q⁻¹V) ≅ H(q⁻¹U₀, q⁻¹(U₀ ∩ V))` — excision, `U₀ = ⋃ᵢ csrOpenBall i`
  (`Work.Serre.csrExcisionRat`), unconditional;
* `(q⁻¹U₀, q⁻¹(U₀ ∩ V)) ≅ (Σᵢ q⁻¹oᵢ, Σᵢ q⁻¹(oᵢ ∖ {cᵢ}))` — the union of the pairwise disjoint
  open half-balls is their disjoint sum (`Work.Serre.CsrSharp.Tools.sigmaPiecesHomeo`), and a
  homeomorphism of pairs induces an isomorphism of relative rational homology
  (`Work.Serre.CsrSharp.cssRelChainsRHomeomorphCompat`);
* `H(Σᵢ q⁻¹oᵢ, Σᵢ q⁻¹(oᵢ∖{cᵢ})) ≅ ∐ᵢ H(q⁻¹oᵢ, q⁻¹(oᵢ∖{cᵢ}))` — the relative chains of a disjoint
  union are the coproduct of the relative chains of the pieces
  (`Work.Serre.relChainsCoproductSquareRat`) and homology commutes with coproducts over `ℚ`
  (`Work.Serre.sigmaHomologyMap`);
* `∐ᵢ H(q⁻¹oᵢ, q⁻¹(oᵢ∖{cᵢ})) ≅ ∐ᵢ H_m(F_{cᵢ})` — the unconditional per-cell computation
  `Work.Serre.CsrSharp.Cell.sourceIso`;
* `∐ᵢ H_m(F_{cᵢ}) ≅ ⨁ᵢ H_m(F_{cᵢ})` — `ModuleCat.coprodIsoDirectSum`.

No fibre hypothesis is used: `Cell.sourceIso` is unconditional.
-/

namespace Work.Serre.CsrSharp

open scoped Topology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

/-! ## Two elementary ingredients -/

/-- **Relative rational homology is invariant under a homeomorphism of pairs**: if `e : X ≃ₜ Y`
carries the subset `A ⊆ X` onto `B ⊆ Y`, then `H_k(X, A; ℚ) ≅ H_k(Y, B; ℚ)`.  The rational
analogue of `Work.Cohomology.relChainsHomeomorphCompat`. -/
theorem cssRelChainsRHomeomorphCompat (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology k ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of Y) B).homology k) := by
  set E := TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e with hE
  have hEf : ∀ x : X, (E.hom : X → Y) x = e x := by
    intro x
    rw [hE, TopCat.isoOfHomeo_hom, TopCat.ofHom_apply]
    rfl
  have he' : ∀ x, x ∈ A ↔ (E.hom : X → Y) x ∈ B := by
    intro x; rw [hEf x]; exact he x
  have hev : ∀ a : ↥A, (E.hom : X → Y) a.1 ∈ B := fun a => (he' a.1).mp a.2
  have hev' : ∀ b : ↥B, (E.inv : Y → X) b.1 ∈ A := by
    intro b
    refine (he' ((E.inv : Y → X) b.1)).mpr ?_
    have h : (TopCat.Hom.hom E.hom) ((TopCat.Hom.hom E.inv) b.1) = b.1 := by
      have h2 : TopCat.Hom.hom (E.inv ≫ E.hom) = TopCat.Hom.hom (𝟙 (TopCat.of Y)) := by
        rw [E.inv_hom_id]
      exact DFunLike.congr_fun h2 b.1
    rw [h]; exact b.2
  let hA : ↥A ≃ₜ ↥B :=
    { toFun := fun a => ⟨(E.hom : X → Y) a.1, hev a⟩
      invFun := fun b => ⟨(E.inv : Y → X) b.1, hev' b⟩
      left_inv := by
        intro a
        apply Subtype.ext
        have h2 : TopCat.Hom.hom (E.hom ≫ E.inv) = TopCat.Hom.hom (𝟙 (TopCat.of X)) := by
          rw [E.hom_inv_id]
        exact DFunLike.congr_fun h2 a.1
      right_inv := by
        intro b
        apply Subtype.ext
        have h2 : TopCat.Hom.hom (E.inv ≫ E.hom) = TopCat.Hom.hom (𝟙 (TopCat.of Y)) := by
          rw [E.inv_hom_id]
        exact DFunLike.congr_fun h2 b.1
      continuous_toFun := ((TopCat.Hom.hom E.hom).continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((TopCat.Hom.hom E.inv).continuous.comp continuous_subtype_val).subtype_mk _ }
  have hsq : Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A
        ≫ Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) E.hom =
      Work.Cohomology.chainMap ℚ (TopCat.of ↥A) (TopCat.of ↥B) (TopCat.isoOfHomeo hA).hom
        ≫ Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B := by
    have h2 : (Work.Cohomology.subtypeIncl (TopCat.of X) A ≫ E.hom) =
        ((TopCat.isoOfHomeo hA).hom ≫ Work.Cohomology.subtypeIncl (TopCat.of Y) B) := by
      apply TopCat.hom_ext
      ext a
      rfl
    show Work.Cohomology.chainMap ℚ (TopCat.of ↥A) (TopCat.of X)
          (Work.Cohomology.subtypeIncl (TopCat.of X) A)
        ≫ Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) E.hom = _
    rw [← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp]
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) k).mapIso
    (cokernel.mapIso (f := Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)
      (f' := Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B)
      (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).mapIso
        (TopCat.isoOfHomeo hA))
      (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).mapIso E) hsq)⟩

/-- **The union of the open half-balls is the disjoint sum of the half-balls, compatibly with the
punctured half-balls.**  The canonical homeomorphism
`q⁻¹(⋃ᵢ oᵢ) ≃ₜ Σᵢ q⁻¹oᵢ` (where `oᵢ = csrOpenBall n Y ι f i` are pairwise disjoint open sets)
matches `q⁻¹(csrV)` with `Σᵢ q⁻¹(oᵢ ∖ {cᵢ})`. -/
theorem cssSigmaPiecesUnionHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) :
    ∃ Φ : ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)) ≃ₜ
        (Σ i, ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)),
      ∀ x : ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)),
        ((x : E) ∈ q ⁻¹' Work.Serre.csrV n Y ι f ↔
          (Φ x).2 ∈ {u : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f (Φ x).1) |
            (u : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f (Φ x).1 \
              {Work.Serre.csrCentre n Y ι f (Φ x).1})}) := by
  classical
  obtain ⟨hopen, -, -, -, -, -, hdisjO, -, hcentre_inter, -, -, -⟩ :=
    Work.Serre.csrGeom n Y ι f
  have hmemb : ∀ (z : Work.RatHurewicz.attachCells n Y ι f) (i : ι),
      z ∈ Work.Serre.csrOpenBall n Y ι f i →
      (z ∉ Work.Serre.csrCentres n Y ι f ↔
        z ∈ Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}) := by
    intro z i hz
    constructor
    · intro hzC
      refine ⟨hz, ?_⟩
      intro hzs
      exact hzC (by rw [Work.Serre.csrCentres]; exact ⟨i, (Set.mem_singleton_iff.mp hzs).symm⟩)
    · rintro ⟨-, hne⟩ hzC
      simp only [Work.Serre.csrCentres, Set.mem_range] at hzC
      obtain ⟨j, hj⟩ := hzC
      have hmem : z ∈ Work.Serre.csrOpenBall n Y ι f i ∩ Work.Serre.csrCentres n Y ι f :=
        ⟨hz, by rw [Work.Serre.csrCentres]; exact ⟨j, hj⟩⟩
      rw [hcentre_inter i] at hmem
      exact hne hmem
  let Φ : ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)) ≃ₜ
      (Σ i, ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)) :=
    Tools.sigmaPiecesHomeo (fun i => q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)
      (fun i => (hopen i).preimage q.continuous)
      (fun i j hij => (hdisjO i j hij).preimage (⇑q))
      (fun i x hx => Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨i, Set.mem_preimage.mp hx⟩))
      (fun z hz => Set.mem_iUnion.mp (Set.preimage_iUnion ▸ hz))
  refine ⟨Φ, ?_⟩
  intro x
  have hspec : q ((Φ x).2 : E) ∈ Work.Serre.csrOpenBall n Y ι f (Φ x).1 := (Φ x).2.2
  have hcoe : ((Φ x).2 : E) = x.1 := rfl
  rw [hcoe] at hspec
  show q x.1 ∈ Work.Serre.csrV n Y ι f ↔
    q x.1 ∈ (Work.Serre.csrOpenBall n Y ι f (Φ x).1 \ {Work.Serre.csrCentre n Y ι f (Φ x).1})
  exact hmemb (q x.1) (Φ x).1 hspec

/-! ## The main computation -/

theorem cellStepSharpIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (m : ℕ) :
    Nonempty (((Work.StemsB.relChainsR ℚ (TopCat.of E)
        (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl n Y ι f))).homology (m + (n+2))) ≅
      ModuleCat.of ℚ (DirectSum ι (fun i => ↥((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))).homology m)))) := by
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
        (fun x hx => Set.preimage_mono hY'V hx)) (m + (n+2))) :=
    Work.Serre.csrRelIso (q ⁻¹' Y') (q ⁻¹' V) (Set.preimage_mono hY'V) hBzero (m + (n+2))
  have h1 : ((Work.StemsB.relChainsR ℚ (TopCat.of E) (q ⁻¹' Y')).homology (m + (n+2))) ≅
      ((Work.StemsB.relChainsR ℚ (TopCat.of E) (q ⁻¹' V)).homology (m + (n+2))) :=
    @asIso _ _ _ _ _ hr1
  -- (2) excision of the cover `{q⁻¹U₀, q⁻¹V}`
  have hUopen : IsOpen U₀ := by
    rw [show U₀ = ⋃ i, Work.Serre.csrOpenBall n Y ι f i from rfl]
    exact isOpen_iUnion fun i => hopen i
  have hcovE : q ⁻¹' U₀ ∪ q ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, show U₀ ∪ V = Set.univ from hcover, Set.preimage_univ]
  have hexcE : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)) (m + (n+2))) :=
    Work.Serre.csrExcisionRat (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)
      (hUopen.preimage q.continuous) (hVopen.preimage q.continuous) hcovE (m + (n+2))
  have h2 : ((Work.StemsB.relChainsR ℚ (TopCat.of E) (q ⁻¹' V)).homology (m + (n+2))) ≅
      ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' U₀))
        {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V}).homology (m + (n+2))) :=
    (@asIso _ _ _ _ _ hexcE).symm
  -- (3) the union of the half-balls is the disjoint sum of the half-balls
  obtain ⟨Φ, hΦ⟩ := cssSigmaPiecesUnionHomeo n Y ι f q
  have he : ∀ x : ↥(q ⁻¹' U₀),
      ((x : E) ∈ q ⁻¹' V ↔ Φ x ∈ {y : Σ i, X i | y.2 ∈ A' y.1}) := by
    intro x
    exact hΦ x
  have h3 : ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' U₀))
        {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V}).homology (m + (n+2))) ≅
      ((Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i))
        {y : Σ i, X i | y.2 ∈ A' y.1}).homology (m + (n+2))) :=
    (cssRelChainsRHomeomorphCompat ↥(q ⁻¹' U₀) (Σ i, X i)
      {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V} {y : Σ i, X i | y.2 ∈ A' y.1}
      Φ he (m + (n+2))).some
  -- (4) the relative chains of the disjoint sum are the coproduct of the pieces
  obtain ⟨eX, -, -⟩ := Work.Serre.relChainsCoproductSquareRat (X := X) (Y := X) A' A'
    (fun i => ContinuousMap.id (X i)) (fun i => fun x hx => hx)
  have h4 : ((Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i))
        {y : Σ i, X i | y.2 ∈ A' y.1}).homology (m + (n+2))) ≅
      (∐ fun i => (Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A' i)).homology (m + (n+2))) :=
    HomologicalComplex.homologyMapIso eX (m + (n+2)) ≪≫
      (@asIso _ _ _ _ _
        (Work.Serre.isIso_sigmaHomologyMap
          (fun i => Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A' i)) (m + (n+2)))).symm
  -- (5) the unconditional per-cell computation
  have h5 : (∐ fun i => (Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A' i)).homology (m + (n+2))) ≅
      (∐ fun i => (Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))).homology m) :=
    Sigma.mapIso fun i => (Work.Serre.CsrSharp.Cell.sourceIso n Y ι f q hq i m).some
  -- (6) the coproduct in `ModuleCat ℚ` is the direct sum
  have h6 : (∐ fun i => (Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))).homology m) ≅
      ModuleCat.of ℚ (DirectSum ι (fun i => ↥((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))).homology m))) :=
    ModuleCat.coprodIsoDirectSum _
  exact ⟨h1 ≪≫ h2 ≪≫ h3 ≪≫ h4 ≪≫ h5 ≪≫ h6⟩

end

end Work.Serre.CsrSharp
