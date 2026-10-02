import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `E3(a)`: shared vocabulary for the cellular proof

This file contains the vocabulary used by the cellular (cell-by-cell) proof of
`Work.Serre.SerreE3a`:

* `Work.Serre.SerreE3aFibreAcyclic` — the honest-fibre form of E3(a);
* `Work.Serre.cellStepMap` — the map of relative chain complexes of a pair
  `(E, E|Y) → (Z, Y)` for a cell attachment `Z = attachCells n Y ι f`, induced by a map `q : E → Z`.

It is `sorry`-free (it only contains definitions) so that the lemmas proved against it do not
inherit any `sorryAx`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-- **E3(a) in the "honest fibre" form.**  For a Serre fibration `q : X → B` over a path-connected
base whose fibre over a point `b₀` is rationally acyclic below `N` (the strong form: `H_t = 0` for
`0 < t ≤ N` and `H_0 ≅ ℚ`), `q` induces a rational homology isomorphism in degrees `< N`.

This is the form in which the cell step produces the statement, and `Work.Serre.SerreE3a` (whose
hypothesis is about the *homotopy* fibre) reduces to it by the mapping-path-space replacement
(`Work.Serre.serreE3aStepA`). -/
def SerreE3aFibreAcyclic : Prop :=
  ∀ (X B : Type) [TopologicalSpace X] [TopologicalSpace B] (q : C(X, B)) (b₀ : B) (N : ℕ),
    Work.StemsB.IsSerreFibration q → PathConnectedSpace B →
      (∀ t : ℕ, 0 < t → t ≤ N →
        IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) t)) →
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) 0 ≅ ModuleCat.of ℚ ℚ) →
      ∀ i : ℕ, i < N → IsIso (Work.Serre.ratHomologyMap q i)

/-- The restriction of `q` to the preimage of `Y ⊆ Z`, as a map of pairs. -/
def cellStepRestrict {Y : Type} [TopologicalSpace Y] (n : ℕ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) :
    TopCat.of {e : E | q e ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)} ⟶
      TopCat.of (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) :=
  TopCat.ofHom ⟨fun e => ⟨q e.1, e.2⟩,
    Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun e => e.2)⟩

/-- The map of relative chain complexes (with rational coefficients)
`C_*(E, E|Y; ℚ) → C_*(Z, Y; ℚ)` induced by `q`, for `Z = attachCells n Y ι f`. -/
def cellStepMap {Y : Type} [TopologicalSpace Y] (n : ℕ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of E)
        {e : E | q e ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
        (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) :=
  cokernel.map
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of E)
      {e : E | q e ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)})
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
      (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
    (Work.Cohomology.chainMap ℚ
      (TopCat.of {e : E | q e ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)})
      (TopCat.of (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
      (cellStepRestrict n ι f q))
    (Work.Cohomology.chainMap ℚ (TopCat.of E) (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
      (TopCat.ofHom q))
    (by
      simp only [Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

end

end Work.Serre

/-! ## The 1-cell attachment

The cellular proof of `Work.Serre.SerreE3a` needs cells in dimension `1` as well (this is the only
way to *create* elements of `π₁`); the workspace's `Work.RatHurewicz.attachCells n` only attaches
cells of dimension `n + 2 ≥ 2`.  Here is the missing case, mirroring that construction verbatim with
`S⁰ = {±1}` as the attaching sphere and the interval `D¹ = [-1,1]` as the cell.
-/

namespace Work.Serre

/-- The model `0`-sphere `S⁰ = {±1} ⊆ ℝ`. -/
abbrev cellSphereZero : Type := Metric.sphere (0 : ℝ) 1

/-- The model `1`-disc `D¹ = [-1,1] ⊆ ℝ`. -/
abbrev cellDiskOne : Type := ↥(Metric.closedBall (0 : ℝ) 1)

/-- The inclusion of the `0`-sphere as the boundary of the interval. -/
def cellSphereZeroToDiskOne : C(cellSphereZero, cellDiskOne) where
  toFun z := ⟨(z : ℝ), Metric.mem_closedBall.mpr (by
    have h : dist (z : ℝ) 0 = 1 := Metric.mem_sphere.mp z.2
    simpa using le_of_eq h)⟩
  continuous_toFun :=
    Continuous.subtype_mk continuous_subtype_val (fun z =>
      Metric.mem_closedBall.mpr (by
        have h : dist (z : ℝ) 0 = 1 := Metric.mem_sphere.mp z.2
        simpa using le_of_eq h))

/-- The relation on `Y ⊕ (ι × D¹)` whose equivalence closure is the gluing of the `1`-cells: the
endpoint `z ∈ S⁰` of the `i`-th interval is identified with `f i z ∈ Y`. -/
def oneCellRel (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) :
    (Y ⊕ (Σ _ : ι, cellDiskOne)) → (Y ⊕ (Σ _ : ι, cellDiskOne)) → Prop :=
  fun a b => ∃ (i : ι) (z : cellSphereZero),
    a = Sum.inl (f i z) ∧ b = Sum.inr ⟨i, cellSphereZeroToDiskOne z⟩

/-- **The space obtained from `Y` by attaching `1`-cells** along the attaching maps
`f : ι → C(S⁰, Y)`. -/
abbrev attachOneCells (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) : Type :=
  Quotient (Relation.EqvGen.setoid (oneCellRel Y ι f))

/-- The inclusion of `Y` into the space obtained by attaching `1`-cells. -/
def oneIncl (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphereZero, Y)) :
    C(Y, attachOneCells Y ι f) where
  toFun y := Quotient.mk'' (Sum.inl y)
  continuous_toFun := continuous_quotient_mk'.comp continuous_inl

/-- The characteristic map of the `i`-th `1`-cell. -/
def oneCellMap (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphereZero, Y))
    (i : ι) : C(cellDiskOne, attachOneCells Y ι f) where
  toFun x := Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDiskOne))
  continuous_toFun :=
    continuous_quotient_mk'.comp (continuous_inr.comp continuous_sigmaMk)

/-- **The gluing relation**: the endpoints of the `i`-th interval are glued to `Y` along the
attaching map `f i`. -/
theorem oneIncl_oneCellRel (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) (z : cellSphereZero) :
    oneIncl Y ι f (f i z) = oneCellMap Y ι f i (cellSphereZeroToDiskOne z) :=
  Quotient.sound (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
    (Relation.EqvGen.rel (r := oneCellRel Y ι f) _ _ ⟨i, z, rfl, rfl⟩)


/-- The restriction of `q` to the preimage of the old part, as a map of pairs (the `1`-cell case). -/
def oneCellStepRestrict {Y : Type} [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, attachOneCells Y ι f)) :
    TopCat.of {e : E | q e ∈ Set.range (oneIncl Y ι f)} ⟶
      TopCat.of (Set.range (oneIncl Y ι f)) :=
  TopCat.ofHom ⟨fun e => ⟨q e.1, e.2⟩,
    Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun e => e.2)⟩

/-- The map of relative chain complexes (with rational coefficients)
`C_*(E, E|Y; ℚ) → C_*(Z, Y; ℚ)` induced by `q`, for `Z = attachOneCells Y ι f`. -/
noncomputable def oneCellStepMap {Y : Type} [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, attachOneCells Y ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of E)
        {e : E | q e ∈ Set.range (oneIncl Y ι f)} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (attachOneCells Y ι f))
        (Set.range (oneIncl Y ι f)) :=
  cokernel.map
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of E) {e : E | q e ∈ Set.range (oneIncl Y ι f)})
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of (attachOneCells Y ι f)) (Set.range (oneIncl Y ι f)))
    (Work.Cohomology.chainMap ℚ
      (TopCat.of {e : E | q e ∈ Set.range (oneIncl Y ι f)})
      (TopCat.of (Set.range (oneIncl Y ι f))) (oneCellStepRestrict ι f q))
    (Work.Cohomology.chainMap ℚ (TopCat.of E) (TopCat.of (attachOneCells Y ι f)) (TopCat.ofHom q))
    (by
      simp only [Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

/-- The restriction of `q : E → Z` to the preimage of `A ⊆ Z`, as a map to `A`. -/
def restrictMap {E Z : Type} [TopologicalSpace E] [TopologicalSpace Z] (q : C(E, Z)) (A : Set Z) :
    C({e : E | q e ∈ A}, A) :=
  ⟨fun e => ⟨q e.1, e.2⟩,
    Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun e => e.2)⟩

/-- The map of relative chain complexes (with rational coefficients) induced by a map of pairs
`(f, g) : (X,A) → (Y,B)`. -/
noncomputable def relChainsRMapOf {R : Type} [CommRing R] (X Y : TopCat) (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.StemsB.relChainsR R X A ⟶ Work.StemsB.relChainsR R Y B :=
  cokernel.map (Work.StemsB.relChainsRIncl R X A) (Work.StemsB.relChainsRIncl R Y B)
    (Work.Cohomology.chainMap R (TopCat.of A) (TopCat.of B) g) (Work.Cohomology.chainMap R X Y f)
    (by
      simp only [Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ w)

end Work.Serre
