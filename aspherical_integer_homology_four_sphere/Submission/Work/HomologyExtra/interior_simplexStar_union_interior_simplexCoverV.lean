import Mathlib
import Submission.Work.HomologyExtra.SimplexStar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The interiors of the closed star and of the open neighbourhood of the opposite face cover `∂Δⁿ⁺¹`

This file proves

`interior (simplexStar n) ∪ interior (simplexCoverV n) = univ`,

the statement that the two open sets of the Mayer–Vietoris cover of `∂Δⁿ⁺¹` used elsewhere in the
development — the interior of the closed star `B = simplexStar n` of the last vertex and the open
neighbourhood `simplexCoverV n = {x | x_last < 1/4}` of the face opposite the last vertex — cover
the whole boundary.

The point is that `simplexCoverV n` is open (so it is its own interior), while any point of
`∂Δⁿ⁺¹` outside it has last barycentric coordinate at least `1/4`; since some coordinate of such a
point vanishes and the last one does not, some *other* coordinate vanishes, and in fact the open
condition `x_last > 1/8` already forces membership in the closed star (again the vanishing
coordinate cannot be the last one).  Thus `{x | x_last > 1/8}` is an open neighbourhood of the
complement of `simplexCoverV n` contained in `simplexStar n`, so that complement lies in the
interior of `simplexStar n`.

## Main results

* `Work.HomologyExtra.simplexMidV` — the open set `{x ∈ ∂Δⁿ⁺¹ | 1/8 < x_last}`;
* `Work.HomologyExtra.simplexMidV_subset_interior_simplexStar`;
* `Work.HomologyExtra.interior_simplexStar_union_interior_simplexCoverV`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-- The points of `∂Δⁿ⁺¹` whose last barycentric coordinate exceeds `1/8`: an open neighbourhood
of the complement of `simplexCoverV n` which is contained in the closed star `simplexStar n`. -/
def simplexMidV (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {y | (1:ℝ)/8 < (y : simplex (n + 1)).weights (Fin.last (n + 1))}

theorem mem_simplexMidV {n : ℕ} {y : boundarySpace (n + 1)} :
    y ∈ simplexMidV n ↔ (1:ℝ)/8 < (y : simplex (n + 1)).weights (Fin.last (n + 1)) := Iff.rfl

/-- `simplexMidV n` is open in `∂Δⁿ⁺¹`, being an open sublevel set of a barycentric coordinate. -/
theorem isOpen_simplexMidV (n : ℕ) : IsOpen (simplexMidV n) :=
  isOpen_lt continuous_const
    ((Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp
      continuous_subtype_val)

/-- `simplexMidV n` is contained in the closed star `simplexStar n`: at a point of `∂Δⁿ⁺¹` some
coordinate vanishes, and if the last coordinate exceeds `1/8` that coordinate is not the last. -/
theorem simplexMidV_subset_simplexStar (n : ℕ) : simplexMidV n ⊆ simplexStar n := by
  intro y hy
  rw [mem_simplexMidV] at hy
  rw [mem_simplexStar]
  obtain ⟨j, hj⟩ := y.2
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · exact ⟨i, hj⟩
  · rw [hj] at hy
    norm_num at hy

/-- `simplexMidV n` is contained in the *interior* of the closed star. -/
theorem simplexMidV_subset_interior_simplexStar (n : ℕ) :
    simplexMidV n ⊆ interior (simplexStar n) :=
  interior_maximal (simplexMidV_subset_simplexStar n) (isOpen_simplexMidV n)

/-- The closed star of the last vertex and the open neighbourhood of the opposite face together
cover `∂Δⁿ⁺¹`. -/
theorem simplexStar_union_simplexCoverV (n : ℕ) :
    simplexStar n ∪ simplexCoverV n = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have h : x ∈ simplexStar n ∪ simplexLastFace n := by
    rw [simplexStar_union_lastFace]; exact Set.mem_univ x
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (simplexLastFace_subset_coverV n h)

/-- **The interiors of the closed star of the last vertex and of the open neighbourhood of the
opposite face cover `∂Δⁿ⁺¹`.** -/
theorem interior_simplexStar_union_interior_simplexCoverV (n : ℕ) :
    interior (Work.HomologyExtra.simplexStar n) ∪
      interior (Work.HomologyExtra.simplexCoverV n) = Set.univ := by
  have hV : interior (simplexCoverV n) = simplexCoverV n :=
    (isOpen_simplexCoverV n).interior_eq
  rw [hV]
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ simplexCoverV n
  · exact Or.inr hx
  · left
    have hx' : (1:ℝ)/4 ≤ (x : simplex (n + 1)).weights (Fin.last (n + 1)) := by
      rw [mem_simplexCoverV] at hx
      exact not_lt.mp hx
    exact simplexMidV_subset_interior_simplexStar n (by
      rw [mem_simplexMidV]
      exact lt_of_lt_of_le (by norm_num) hx')

end

end Work.HomologyExtra
