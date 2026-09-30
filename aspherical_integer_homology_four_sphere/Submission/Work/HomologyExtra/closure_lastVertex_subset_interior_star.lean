import Mathlib
import Submission.Work.HomologyExtra.SimplexFaceSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The last vertex lies in the interior of the closed star

The closed star `simplexStar n` of the last vertex `v = simplexLastVertex n` of the boundary
`∂Δⁿ⁺¹` contains the open **north cap** `simplexNorthCap n = {x | 0 < x_last}`: a boundary point
with `x_last > 0` must have one of its other (necessarily `castSucc`) barycentric coordinates
equal to `0`, i.e. lie in the star.  Since `v` has last coordinate `1 > 0`, it lies in the north
cap, and as the north cap is open this exhibits `interior (simplexStar n)` as a neighbourhood of
`v`.

Consequently the closure of the singleton `{v}` (which is `{v}` in this `T₁` space) is contained
in `interior (simplexStar n)`.

This is the elementary topological fact behind the observation that `B = simplexStar n` is a
*closed* neighbourhood of `v` in `∂Δⁿ⁺¹`: the excision of the interior of `B` from the pair
`(∂Δⁿ⁺¹, B)` is legitimate.
-/

set_option linter.style.haveILetI false

namespace Work.HomologyExtra

noncomputable section

/-- The open north cap of `∂Δⁿ⁺¹` is contained in the closed star of the last vertex: if the last
barycentric coordinate is positive, the (guaranteed) vanishing coordinate of a boundary point is
one of the `castSucc` coordinates. -/
theorem simplexNorthCap_subset_simplexStar (n : ℕ) :
    simplexNorthCap n ⊆ simplexStar n := by
  intro x hx
  obtain ⟨i, hi⟩ := x.2
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact ⟨j, hi⟩
  · exfalso
    change 0 < (x : simplex (n + 1)).weights (Fin.last (n + 1)) at hx
    rw [hi] at hx
    exact lt_irrefl 0 hx

theorem closure_lastVertex_subset_interior_star (n : ℕ) :
    closure ({Work.HomologyExtra.simplexLastVertex n} :
        Set (Work.HomologyExtra.boundarySpace (n + 1)))
      ⊆ interior (Work.HomologyExtra.simplexStar n) := by
  -- The standard simplex is a `T₁` space (it embeds into a function space), hence so is the
  -- boundary, and the closure of a singleton is the singleton.
  haveI : T1Space ↥(simplex (n + 1)) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).t1Space
  -- The north cap is an open neighbourhood of `v` contained in the closed star.
  have hopen : IsOpen (simplexNorthCap n) := by
    have h : Continuous (fun x : boundarySpace (n + 1) =>
        (x : simplex (n + 1)).weights (Fin.last (n + 1))) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp
        continuous_subtype_val
    exact isOpen_lt continuous_const h
  have hsub : simplexNorthCap n ⊆ interior (simplexStar n) := by
    rw [← hopen.interior_eq]
    exact interior_mono (simplexNorthCap_subset_simplexStar n)
  rw [closure_singleton]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hsub (simplexLastVertex_mem_northCap n)

end

end Work.HomologyExtra
