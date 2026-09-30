import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.RealizationDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The skeleta of a realized `Δ`-complex

For a `Δ`-complex `K` with characteristic maps `χ : DeltaSimplexMap K X` (as in
`Submission/Work/DeltaHomology/RealizationDefs.lean`), the **`k`-skeleton** of
`X` is the union of the images of the closed simplices of dimension `≤ k`:

`χ.skelSet k = ⋃_{j ≤ k} ⋃_{σ : Fin (K.card j)} (χ.cls j σ) '' univ`.

This file contains the definition together with the elementary API
(`cls_mem_skelSet`, `skelSet_mono`, `real_mem_skelSet`, and the corestriction
`clsInSkelSet`).  The facts that need the realization (the characterization
`x ∈ X^k ↔ dim of the open simplex of x is ≤ k`, closedness, and `X^dim = X`) are
in the files `mem_skelSet_iff.lean`, `isClosed_skelSet.lean` and
`skelSet_univ.lean`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Convexity

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

open scoped Simplicial

variable {K : DeltaCx} {X : TopCat}

/-- The `k`-skeleton of a realized `Δ`-complex: the union of the images of the
closed simplices of dimension `≤ k`. -/
def DeltaSimplexMap.skelSet (χ : DeltaSimplexMap K X) (k : ℕ) : Set X :=
  ⋃ (j : {j : ℕ // j ≤ k}) (σ : Fin (K.card j.1)), Set.range (χ.cls j.1 σ)

/-- Each point of a closed simplex of dimension `≤ k` lies in the `k`-skeleton. -/
theorem DeltaSimplexMap.cls_mem_skelSet (χ : DeltaSimplexMap K X) {j k : ℕ} (h : j ≤ k)
    (σ : Fin (K.card j)) (y : StdSimplex ℝ (Fin (j + 1))) :
    (χ.cls j σ y : X) ∈ χ.skelSet k :=
  Set.mem_iUnion₂.mpr ⟨⟨j, h⟩, σ, Set.mem_range_self y⟩

/-- The skeleta are nested. -/
theorem DeltaSimplexMap.skelSet_mono (χ : DeltaSimplexMap K X) {k l : ℕ} (h : k ≤ l) :
    χ.skelSet k ⊆ χ.skelSet l := by
  intro x hx
  simp only [DeltaSimplexMap.skelSet, Set.mem_iUnion, Set.mem_range] at hx ⊢
  obtain ⟨j, σ, y, rfl⟩ := hx
  exact ⟨⟨j.1, le_trans j.2 h⟩, σ, y, rfl⟩

/-- The image of an open simplex of dimension `j` lies in the `j`-skeleton. -/
theorem DeltaSimplexMap.real_mem_skelSet (χ : DeltaSimplexMap K X) (p : OpenSimplex K) :
    (χ.real p : X) ∈ χ.skelSet p.dim :=
  χ.cls_mem_skelSet le_rfl p.idx p.pt

/-- The characteristic map of a `j`-simplex (`j ≤ k`), corestricted to the
`k`-skeleton. -/
def DeltaSimplexMap.clsInSkelSet (χ : DeltaSimplexMap K X) (k : ℕ) {j : ℕ} (h : j ≤ k)
    (σ : Fin (K.card j)) : C(StdSimplex ℝ (Fin (j + 1)), ↥(χ.skelSet k)) :=
  ⟨fun y => ⟨χ.cls j σ y, χ.cls_mem_skelSet h σ y⟩,
    (χ.cls j σ).continuous.subtype_mk _⟩

@[simp]
theorem DeltaSimplexMap.clsInSkelSet_coe (χ : DeltaSimplexMap K X) (k : ℕ) {j : ℕ}
    (h : j ≤ k) (σ : Fin (K.card j)) (y : StdSimplex ℝ (Fin (j + 1))) :
    ((χ.clsInSkelSet k h σ y : ↥(χ.skelSet k)) : X) = χ.cls j σ y := rfl

/-- The barycentre of the standard `k`-simplex (all barycentric weights `1/(k+1)`),
the interior point used to puncture the `k`-simplices in the collar argument. -/
def simplexBarycenter (k : ℕ) : StdSimplex ℝ (Fin (k + 1)) :=
  StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1))

theorem simplexBarycenter_weights (k : ℕ) (i : Fin (k + 1)) :
    (simplexBarycenter k).weights i = ((k + 1 : ℕ) : ℝ)⁻¹ := by
  rw [simplexBarycenter, StdSimplex.weights_barycenter_apply, Fintype.card_fin]

theorem simplexBarycenter_weights_pos (k : ℕ) (i : Fin (k + 1)) :
    0 < (simplexBarycenter k).weights i := by
  rw [simplexBarycenter_weights]
  positivity

/-- The barycentre of a simplex is an interior point of the standard simplex. -/
theorem isOpenSimplexPoint_simplexBarycenter (k : ℕ) :
    IsOpenSimplexPoint k (simplexBarycenter k) :=
  simplexBarycenter_weights_pos k

/-- The barycentres of the `k`-simplices of `K`, as points of `X`. -/
def DeltaSimplexMap.barycenterSet (χ : DeltaSimplexMap K X) (k : ℕ) : Set X :=
  Set.range (fun σ : Fin (K.card k) => (χ.cls k σ (simplexBarycenter k) : X))

/-- The `k`-skeleton with the barycentres of its `k`-simplices removed: an open
neighbourhood of the `(k-1)`-skeleton inside the `k`-skeleton, which deformation
retracts onto it (the collar used in the skeleta induction). -/
def DeltaSimplexMap.punctSkel (χ : DeltaSimplexMap K X) (k : ℕ) : Set X :=
  χ.skelSet k \ χ.barycenterSet k

theorem DeltaSimplexMap.punctSkel_subset_skelSet (χ : DeltaSimplexMap K X) (k : ℕ) :
    χ.punctSkel k ⊆ χ.skelSet k :=
  Set.sdiff_subset

theorem DeltaSimplexMap.barycenterSet_finite (χ : DeltaSimplexMap K X) (k : ℕ) :
    (χ.barycenterSet k).Finite :=
  Set.finite_range _

end

end Work.DeltaHomology
