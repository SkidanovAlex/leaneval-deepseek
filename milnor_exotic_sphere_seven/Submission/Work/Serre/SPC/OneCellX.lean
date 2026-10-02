import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Cohomology.localHomology
import Submission.Work.StemsB.SerreExact
import Submission.Work.RatHurewicz.AttachCells

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `1`-cell attachment, integral coefficients (vocabulary for the `b = 1` case)

The workspace's `Work.RatHurewicz.attachCells n` attaches cells of dimension `n + 2 ≥ 2` only, so
it cannot create elements of `π₁`.  This file provides the missing **`1`-cell** case, in a
self-contained way (the copy in `Submission/Work/Serre/E3aDefs.lean` cannot be imported together
with `Work.Serre.cellStepDefs`, which our file needs for `Work.Serre.SPC.CellStepHyp`: both declare
`Work.Serre.cellStepAttachMap`), together with the **integral** comparison map of the pair
`(X, q⁻¹Y) → (Z, Y)` of the attached space, and the `Prop`-valued statement
`Work.Serre.SPC.CellStepHypOne` of the `D = 1` cell step.

`attachOneCells Y ι f` is the quotient of the coproduct `Y ⊕ (Σ _ : ι, D¹)` that glues the two
endpoints of the `i`-th interval to `f i (±1) ∈ Y`.  For a Serre fibration `q : X → Z` with
`Z = attachOneCells Y ι f` the comparison map is the map of relative chain complexes induced by the
map of pairs `(X, q⁻¹Y) → (Z, Y)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC

noncomputable section

/-! ## The `1`-cell attachment -/

/-- The model `0`-sphere `S⁰ = {±1} ⊆ ℝ`. -/
abbrev cellS0 : Type := Metric.sphere (0 : ℝ) 1

/-- The model `1`-disc `D¹ = [-1,1] ⊆ ℝ`. -/
abbrev cellD1 : Type := ↥(Metric.closedBall (0 : ℝ) 1)

/-- The inclusion of the `0`-sphere as the boundary of the interval. -/
def cellS0ToD1 : C(cellS0, cellD1) where
  toFun z := ⟨(z : ℝ), Metric.mem_closedBall.mpr (by
    have h : dist (z : ℝ) 0 = 1 := Metric.mem_sphere.mp z.2
    simpa using le_of_eq h)⟩
  continuous_toFun :=
    Continuous.subtype_mk continuous_subtype_val (fun z =>
      Metric.mem_closedBall.mpr (by
        have h : dist (z : ℝ) 0 = 1 := Metric.mem_sphere.mp z.2
        simpa using le_of_eq h))

/-- The gluing relation: the endpoint `z ∈ S⁰` of the `i`-th interval is identified with `f i z`. -/
def oneCellRel (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) :
    (Y ⊕ (Σ _ : ι, cellD1)) → (Y ⊕ (Σ _ : ι, cellD1)) → Prop :=
  fun a b => ∃ (i : ι) (z : cellS0),
    a = Sum.inl (f i z) ∧ b = Sum.inr ⟨i, cellS0ToD1 z⟩

/-- **The space obtained from `Y` by attaching `1`-cells** along the attaching maps
`f : ι → C(S⁰, Y)`. -/
abbrev attachOneCells (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) : Type :=
  Quotient (Relation.EqvGen.setoid (oneCellRel Y ι f))

/-- The inclusion of `Y` into the space obtained by attaching `1`-cells. -/
def oneIncl (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) :
    C(Y, attachOneCells Y ι f) where
  toFun y := Quotient.mk'' (Sum.inl y)
  continuous_toFun := continuous_quotient_mk'.comp continuous_inl

/-- The characteristic map of the `i`-th `1`-cell. -/
def oneCellMap (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (i : ι) : C(cellD1, attachOneCells Y ι f) where
  toFun x := Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellD1))
  continuous_toFun :=
    continuous_quotient_mk'.comp (continuous_inr.comp continuous_sigmaMk)

/-- **The gluing relation**: the endpoints of the `i`-th interval are glued to `Y` along `f i`. -/
theorem oneIncl_oneCellRel (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) (i : ι) (z : cellS0) :
    oneIncl Y ι f (f i z) = oneCellMap Y ι f i (cellS0ToD1 z) :=
  Quotient.sound (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
    (Relation.EqvGen.rel (r := oneCellRel Y ι f) _ _ ⟨i, z, rfl, rfl⟩)

/-- The function on the disjoint union `Y ⊕ (Σ i, D¹)` given by `g` on `Y` and by the `G i` on
the cells. -/
def oneCellGlue (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    {B : Type} [TopologicalSpace B] (g : C(Y, B)) (G : ι → C(cellD1, B)) :
    Y ⊕ (Σ _ : ι, cellD1) → B :=
  Sum.elim g fun p : Σ _ : ι, cellD1 => G p.1 p.2

/-- The gluing function is continuous. -/
theorem continuous_oneCellGlue (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    {B : Type} [TopologicalSpace B] (g : C(Y, B)) (G : ι → C(cellD1, B)) :
    Continuous (oneCellGlue Y ι f g G) :=
  g.continuous.sumElim (continuous_sigma fun i => (G i).continuous)

/-- Two related points have the same image under the gluing function. -/
theorem oneCellGlue_rel (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    {B : Type} [TopologicalSpace B] (g : C(Y, B)) (G : ι → C(cellD1, B))
    (hG : ∀ (i : ι) (z : cellS0), G i (cellS0ToD1 z) = g (f i z)) :
    ∀ a b : Y ⊕ (Σ _ : ι, cellD1),
      Relation.EqvGen (oneCellRel Y ι f) a b →
        oneCellGlue Y ι f g G a = oneCellGlue Y ι f g G b := by
  have hgen : ∀ a b : Y ⊕ (Σ _ : ι, cellD1), oneCellRel Y ι f a b →
      oneCellGlue Y ι f g G a = oneCellGlue Y ι f g G b := by
    rintro a b ⟨i, z, rfl, rfl⟩
    simpa [oneCellGlue] using (hG i z).symm
  intro a b hab
  induction hab with
  | rel x y h => exact hgen x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Extending a map over the attached `1`-cells**, given the values on the cells and the
compatibility on their boundaries. -/
def oneAttachG {B : Type} [TopologicalSpace B] (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) (g : C(Y, B)) (G : ι → C(cellD1, B))
    (hG : ∀ (i : ι) (z : cellS0), G i (cellS0ToD1 z) = g (f i z)) :
    C(attachOneCells Y ι f, B) :=
  ⟨Quotient.lift (oneCellGlue Y ι f g G) (oneCellGlue_rel Y ι f g G hG),
    (continuous_oneCellGlue Y ι f g G).quotient_lift (oneCellGlue_rel Y ι f g G hG)⟩

@[simp] theorem oneAttachG_incl {B : Type} [TopologicalSpace B] (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(cellS0, Y)) (g : C(Y, B)) (G : ι → C(cellD1, B))
    (hG : ∀ (i : ι) (z : cellS0), G i (cellS0ToD1 z) = g (f i z)) (y : Y) :
    oneAttachG Y ι f g G hG (oneIncl Y ι f y) = g y := rfl

@[simp] theorem oneAttachG_cell {B : Type} [TopologicalSpace B] (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(cellS0, Y)) (g : C(Y, B)) (G : ι → C(cellD1, B))
    (hG : ∀ (i : ι) (z : cellS0), G i (cellS0ToD1 z) = g (f i z)) (i : ι) (x : cellD1) :
    oneAttachG Y ι f g G hG (oneCellMap Y ι f i x) = G i x := rfl

/-! ## The comparison map of the pair `(X, q⁻¹Y) → (Z, Y)` -/

/-- The restriction of `q` to the preimage of the old part, as a map to the old part. -/
def oneCellStepRestrict {Y : Type} [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachOneCells Y ι f)) :
    C({x : X | q x ∈ Set.range (oneIncl Y ι f)}, Set.range (oneIncl Y ι f)) :=
  ⟨fun x => ⟨q x.1, x.2⟩, Continuous.subtype_mk (q.continuous.comp continuous_subtype_val)
    (fun x => x.2)⟩

/-- **The map of relative chain complexes** `C_*(X, q⁻¹Y) → C_*(Z, Y)` (integral coefficients)
induced by a map `q : X → Z`, where `Z = attachOneCells Y ι f`. -/
def oneCellStepMap {Y : Type} [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    Work.Cohomology.relChains (TopCat.of X)
        {x : X | q x ∈ Set.range (oneIncl Y ι f)} ⟶
      Work.Cohomology.relChains (TopCat.of (attachOneCells Y ι f))
        (Set.range (oneIncl Y ι f)) :=
  Work.Cohomology.relChainsMapOf (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
    {x : X | q x ∈ Set.range (oneIncl Y ι f)} (Set.range (oneIncl Y ι f))
    (TopCat.ofHom q) (TopCat.ofHom (oneCellStepRestrict ι f q)) (by ext x; rfl)

/-- **The `D = 1` cell step.**  For a Serre fibration `q : X → Z` over the space
`Z = attachOneCells Y ι f` obtained by attaching `1`-cells to `Y`, with fibres that are homologically
`φ`-connected (`H_j = 0` for `0 < j < φ`, `H_0 ≅ ℤ`), the map of pairs `(X, q⁻¹Y) → (Z, Y)` is an
isomorphism on integral homology in degrees `< 1 + φ` and surjective in degree `1 + φ`.

This is the exact analogue of `Work.Serre.SPC.CellStepHyp` for cells of dimension `D = 1`
(there `D + φ` with `D ≥ 2`), and the only missing ingredient of the cellular induction for
`b = 1`.

## Plan of the proof

Write `Z := attachOneCells Y ι f`, `Y' := Set.range (oneIncl Y ι f)` (so `Z ∖ Y'` is the union of
the open cells), `B := ⋃ i, (oneCellMap Y ι f i) '' (the open cell)` (the union of the open cells)
and `P := ⋃ i, {oneCellMap Y ι f i c}` where `c ∈ cellD1` is the centre.  Note `Z ∖ B = Y'` (the
boundary points of the cells are the images of the attaching maps).  All the compressions below are
provided by `Work.Serre.isZero_relChains_of_deformation` (base side) and
`Work.Serre.isZero_relChains_preimage_of_compress` (E-side, using
`Work.Serre.SPC.compressRel_of_deformation` to produce the `CompressRel` input), while the
identifications of pairs are `Work.Serre.isIso_relCokerMap_of_acyclic` /
`Work.Serre.isIso_tripleIncl_of_acyclic` (the long exact sequence of a triple) and the **integral
excision** `Work.Cohomology.excision_relChainsMap_isIso`.

1. **Base side.**  `H_*(Z, Y') ≅ H_*(Z, Z∖P)` because `Z∖P` deformation retracts onto `Y'`
   (contract each half of an interval onto its endpoint), and `H_*(Z, Z∖P) ≅ H_*(B, B∖P)` by
   excision for the open cover `(B, Z∖P)`.  Since `B` is the disjoint union of the open cells,
   `C_*(B, B∖P) = ⊕_i C_*(cell_i, cell_i ∖ centre_i)` (the chains of a coproduct; see
   `Submission/Work/Serre/coprodChainAux.lean`, `sigmaRelChainsIso`, `homology_coproduct_iso`),
   and `(cell, cell∖centre) ≅ (D¹, ∂D¹)` up to the deformation of each half-interval onto its
   endpoint, so `H_1(Z,Y') ≅ ⊕_i ℤ` and `H_m(Z,Y') = 0` for `m ≥ 2`
   (`Work.Cohomology.relH1OfPair_aux` computes `H_1` of a pair `(X,A)` with `X` contractible and
   the reduced `H_0(A) = ℤ`).
2. **E-side.**  The same three steps with `q ⁻¹'` in place of the sets, giving
   `H_*(X, q⁻¹Y') ≅ ⊕_i H_*(q⁻¹cell_i, q⁻¹(cell_i ∖ centre_i))`; the *lifted* compressions are
   `Work.Serre.isZero_relChains_preimage_of_compress`.
3. **Local model.**  `Work.Serre.SerreE2d` at `n = 1` gives
   `H_{m}(q⁻¹cell, q⁻¹∂cell) ≅ H_{m-1}(F)` (the fibre over a point of the cell), and the
   deformation `cell ∖ centre ≃ ∂cell` identifies the relative parts, so the per-cell comparison is
   `H_{m-1}(F) → H_m(cell, cell∖centre)`.
4. **Per-cell comparison.**  For `m = 1` it is `ℤ ≅ ℤ` and is an isomorphism because it is
   *surjective*: a relative `1`-cycle of `(cell, ∂cell)` (a path in the cell between its two
   endpoints) lifts through `q` — using the homotopy lifting property of the Serre fibration — to a
   relative `1`-cycle of `(q⁻¹cell, q⁻¹∂cell)` with the same image.  (An epimorphism `ℤ → ℤ` whose
   source and target are both `≅ ℤ` is an isomorphism.)  For `m ≥ 2` the target vanishes and the
   source is `H_{m-1}(F)`, which vanishes for `m ≤ φ` by the hypothesis and is mapped onto `0` for
   `m = φ + 1`.  In degree `0` both sides vanish.
5. **Assembly.**  The direct sum of the per-cell comparisons is the comparison of the two
   decompositions (functoriality of the coproduct identification), so it is an isomorphism in
   degrees `≤ φ` and surjective in degree `φ + 1`; transporting back along the identifications of
   step 1 (which are isomorphisms in every degree) gives the claim. -/
def CellStepHypOne : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (X : Type) [TopologicalSpace X] (q : C(X, attachOneCells Y ι f))
    (_hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (_hfib : ∀ y : attachOneCells Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (_h0 : ∀ y : attachOneCells Y ι f,
      IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y)) (ModuleCat.of ℤ ℤ))),
    (∀ i : ℕ, i < 1 + φ →
      IsIso (HomologicalComplex.homologyMap (oneCellStepMap ι f q) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (oneCellStepMap ι f q) (1 + φ)).hom


/-! ## Compressions from deformations -/

/-- A deformation of `Y` into `A` (fixing `A` pointwise) gives the compression property of the pair
`(Y,A)` in every dimension. -/
theorem compressRel_of_deformation {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (c : C(Y × unitInterval, Y)) (hc0 : ∀ y, c (y, 0) = y) (hc1 : ∀ y, c (y, 1) ∈ A)
    (hcA : ∀ y ∈ A, ∀ t : unitInterval, c (y, t) = y) (d : ℕ) :
    Work.RatHurewicz.CompressRel Y A d := by
  intro f hf
  refine ⟨⟨fun q => c (f q.1, q.2), by fun_prop⟩, ?_, ?_, ?_⟩
  · intro x; exact hc0 (f x)
  · intro x hx t; exact hcA (f x) (hf x hx) t
  · intro x; exact hc1 (f x)

end

end Work.Serre.SPC
