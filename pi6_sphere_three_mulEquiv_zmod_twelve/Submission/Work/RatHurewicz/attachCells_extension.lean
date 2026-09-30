import Mathlib
import Submission.Work.RatHurewicz.AttachCells

/-!
# The universal property of a cell attachment

`Work.RatHurewicz.attachCells n Y ι f` is the space obtained from `Y` by gluing `(n+2)`-cells along
the attaching maps `f i : S^{n+1} → Y`.  This module proves the (existence half of the) universal
property: a continuous map `g : Y → Z` together with continuous maps `G i : D^{n+2} → Z` agreeing
with `g ∘ f i` on the boundary sphere produces a continuous map out of `attachCells` restricting to
`g` and to the `G i`.  This is the tool with which the maps between the Postnikov models of the
Serre blueprint (`Submission/Work/Drive/SERRE_BLUEPRINT.md`, C0/K1) are constructed.
-/

set_option linter.unusedVariables false

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The function on the disjoint union `Y ⊕ (Σ i, D^{n+2})` given by `g` on `Y` and by the `G i` on
the cells. -/
def attachCellsGlue (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {Z : Type} [TopologicalSpace Z] (g : C(Y, Z))
    (G : ∀ i : ι, C(cellDisk n, Z)) : Y ⊕ (Σ _ : ι, cellDisk n) → Z :=
  Sum.elim g fun p : Σ _ : ι, cellDisk n => G p.1 p.2

/-- The gluing function is continuous. -/
theorem continuous_attachCellsGlue (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {Z : Type} [TopologicalSpace Z] (g : C(Y, Z))
    (G : ∀ i : ι, C(cellDisk n, Z)) :
    Continuous (attachCellsGlue n Y ι f g G) := by
  exact g.continuous.sumElim (continuous_sigma fun i => (G i).continuous)

/-- Two points of `Y ⊕ (Σ i, D^{n+2})` related by the gluing relation have the same image under the
gluing function, as soon as the boundary restrictions agree. -/
theorem attachCellsGlue_rel (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {Z : Type} [TopologicalSpace Z] (g : C(Y, Z))
    (G : ∀ i : ι, C(cellDisk n, Z))
    (hG : ∀ (i : ι) (z : cellSphere n), G i (cellSphereToDisk n z) = g (f i z)) :
    ∀ a b : Y ⊕ (Σ _ : ι, cellDisk n),
      Relation.EqvGen (attachRel n Y ι f) a b →
        attachCellsGlue n Y ι f g G a = attachCellsGlue n Y ι f g G b := by
  have hgen : ∀ a b : Y ⊕ (Σ _ : ι, cellDisk n), attachRel n Y ι f a b →
      attachCellsGlue n Y ι f g G a = attachCellsGlue n Y ι f g G b := by
    rintro a b ⟨i, z, rfl, rfl⟩
    simpa [attachCellsGlue] using (hG i z).symm
  intro a b hab
  induction hab with
  | rel x y h => exact hgen x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The universal property of a cell attachment.**  A continuous map out of `attachCells n Y ι f`
into a space `Z` is determined by a continuous map `g : Y → Z` together with, for every cell
`i : ι`, a continuous map `G i : D^{n+2} → Z` whose restriction to the boundary sphere agrees with
`g` composed with the attaching map `f i`.  Concretely, such data `(g, G, hG)` produce a continuous
map `g' : attachCells n Y ι f → Z` which restricts to `g` on `Y` and to `G i` on the `i`-th cell. -/
theorem attachCells_extension (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {Z : Type} [TopologicalSpace Z] (g : C(Y, Z))
    (G : ∀ i : ι, C(cellDisk n, Z))
    (hG : ∀ (i : ι) (z : cellSphere n), G i (cellSphereToDisk n z) = g (f i z)) :
    ∃ g' : C(attachCells n Y ι f, Z),
      g'.comp (attachIncl n Y ι f) = g ∧
        ∀ i : ι, g'.comp (cellMap n Y ι f i) = G i := by
  have hc := continuous_attachCellsGlue n Y ι f g G
  have hrel := attachCellsGlue_rel n Y ι f g G hG
  refine ⟨⟨Quotient.lift (attachCellsGlue n Y ι f g G) hrel, hc.quotient_lift hrel⟩, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro y
    rfl
  · intro i
    apply ContinuousMap.ext
    intro x
    rfl

end

end Work.RatHurewicz
