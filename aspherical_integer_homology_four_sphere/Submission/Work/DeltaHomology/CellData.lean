import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.SkelProps
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cells of a realized `Δ`-complex

For a `Δ`-complex `K` realized in a space `X` by characteristic maps `χ`, this file
introduces the *cells* of the realization:

* `χ.cell k σ` — the closed `k`-cell carried by the simplex `σ`, the image of `χ σ`;
* `χ.cellBarycenter k σ` — the barycentre of that cell;
* `χ.punctCell k σ` — the closed cell with its barycentre removed;
* `χ.intCell k σ` — the open cell, i.e. the points of the closed cell which are not in
  any lower skeleton.

These are the pieces appearing in the skeleta induction of Hatcher's theorem
(`H_n(X^k, X^{k-1})` is the direct sum of the relative homologies of the pairs
`(cell, punctCell)` over the `k`-simplices): see `NOTES.md` §4.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology
open scoped Simplicial

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

namespace DeltaSimplexMap

variable (χ : DeltaSimplexMap K X)

/-- The closed `k`-cell of the simplex `σ`: the image of the characteristic map `χ σ`. -/
def cell (k : ℕ) (σ : Fin (K.card k)) : Set X := Set.range (χ.cls k σ)

/-- The barycentre of the `k`-cell `σ`. -/
def cellBarycenter (k : ℕ) (σ : Fin (K.card k)) : X := χ.cls k σ (simplexBarycenter k)

/-- The open `k`-cell: the points of the closed cell lying in no lower skeleton. -/
def intCell (k : ℕ) (σ : Fin (K.card k)) : Set X :=
  {x | x ∈ cell χ k σ ∧ ∀ j, j < k → x ∉ χ.skelSet j}

theorem cell_subset_skelSet {k : ℕ} (σ : Fin (K.card k)) : cell χ k σ ⊆ χ.skelSet k := by
  rintro x ⟨y, rfl⟩
  exact χ.cls_mem_skelSet le_rfl σ y

theorem cellBarycenter_mem_cell (k : ℕ) (σ : Fin (K.card k)) :
    cellBarycenter χ k σ ∈ cell χ k σ := Set.mem_range_self _

theorem cellBarycenter_mem_barycenterSet (k : ℕ) (σ : Fin (K.card k)) :
    cellBarycenter χ k σ ∈ χ.barycenterSet k := Set.mem_range_self _

/-- The barycentre of a `k`-cell is not in the `(k-1)`-skeleton. -/
theorem cellBarycenter_not_mem_skelSet_of_lt (R : DeltaRealization K X) {j k : ℕ} (hjk : j < k)
    (σ : Fin (K.card k)) :
    cellBarycenter R.toDeltaSimplexMap k σ ∉ R.toDeltaSimplexMap.skelSet j :=
  barycenter_not_mem_skelSet_of_lt R hjk σ

/-- The barycentre of a `k`-cell lies in the open `k`-cell. -/
theorem cellBarycenter_mem_intCell (R : DeltaRealization K X) (k : ℕ) (σ : Fin (K.card k)) :
    cellBarycenter R.toDeltaSimplexMap k σ ∈ R.toDeltaSimplexMap.intCell k σ :=
  ⟨R.toDeltaSimplexMap.cellBarycenter_mem_cell k σ,
   fun _ hj => cellBarycenter_not_mem_skelSet_of_lt R hj σ⟩

theorem intCell_subset_cell (k : ℕ) (σ : Fin (K.card k)) : intCell χ k σ ⊆ cell χ k σ :=
  fun _ hx => hx.1

theorem mem_intCell_iff {k : ℕ} (σ : Fin (K.card k)) {x : X} :
    x ∈ intCell χ k σ ↔ x ∈ cell χ k σ ∧ ∀ j, j < k → x ∉ χ.skelSet j := Iff.rfl

theorem intCell_subset_skelSet (k : ℕ) (σ : Fin (K.card k)) :
    intCell χ k σ ⊆ χ.skelSet k :=
  fun _ hx => χ.cell_subset_skelSet σ hx.1

/-- The open cell of a `k`-simplex is the closed cell with the skeletons below removed. -/
theorem intCell_eq_sdiff (k : ℕ) (σ : Fin (K.card k)) :
    intCell χ k σ = cell χ k σ \ (⋃ j : {j : ℕ // j < k}, χ.skelSet j) := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun hy => by
      obtain ⟨⟨j, hj⟩, hyj⟩ := Set.mem_iUnion.mp hy
      exact h j hj hyj⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j hj hxj => h (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩)⟩

theorem cls_mem_cell (k : ℕ) (σ : Fin (K.card k)) (y : StdSimplex ℝ (Fin (k + 1))) :
    (χ.cls k σ y : X) ∈ cell χ k σ := Set.mem_range_self y

/-- The open `k`-cell is disjoint from the `(k-1)`-skeleton, hence contained in the
complement of the closed cells of dimension `< k`. -/
theorem intCell_subset_compl_skelSet {k j : ℕ} (hj : j < k) (σ : Fin (K.card k)) :
    intCell χ k σ ⊆ (χ.skelSet j)ᶜ :=
  fun x hx hxs => hx.2 j hj hxs

end DeltaSimplexMap

end

end Work.DeltaHomology
