import Mathlib
import Submission.Work.Projective.Atlas
import Submission.Work.Model.prod_transfer
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.sphereCohomologyTop

/-!
# The affine charts of `ℂPⁿ` as topological spaces, and the standard cover of `ℂP²`

This module provides the topological input for the computation of `H^*(ℂP²;ℤ)` by
Mayer–Vietoris in the workspace's own cochain model (`Submission/Work/Cohomology/`):

* `Work.Projective.CPSpace n` — `ℂPⁿ` as a `TopCat`;
* **`Work.Projective.chartHomeomorph i : (Fin n → ℂ) ≃ₜ ↥(chartSet i)`** — each affine chart is
  homeomorphic to `ℂⁿ` (via `chartInv`/`chartFun`), hence contractible
  (`Work.Projective.contractibleSpace_chartSet`);
* the standard cover of `ℂP²` by the chart `U = chartSet 0` and the complement `V` of the point
  `[1:0:0]`, i.e. the union of the other two charts (`cp2U`, `cp2V`), with
  `Work.Projective.isOpen_cp2U`, `isOpen_cp2V`, `cp2U_union_cp2V`;
* `Work.Projective.cp2U_homeo : (Fin 2 → ℂ) ≃ₜ ↥cp2U` (so `U` is contractible) and
  `Work.Projective.cp2UV_homeo : ↥(cp2U ∩ cp2V) ≃ₜ {z : Fin 2 → ℂ // z ≠ 0}` (so `U ∩ V` is
  homotopy equivalent to `S³`).

The cohomology computations of the pieces and the Mayer–Vietoris assembly are in
`Submission/Work/Projective/CP2Cohomology.lean`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-- `ℂPⁿ` as a topological space. -/
abbrev CPSpace (n : ℕ) : TopCat := TopCat.of (CP n)

/-- **Each affine chart of `ℂPⁿ` is homeomorphic to `ℂⁿ`**: the inverse chart map `chartInv i`
followed by the chart map `chartFun i`. -/
def chartHomeomorph (n : ℕ) (i : Fin (n + 1)) : (Fin n → ℂ) ≃ₜ ↥(chartSet i) where
  toFun w := ⟨chartInv i w, chartInv_mem_chartSet i w⟩
  invFun p := chartFun i p.1
  left_inv w := chartFun_chartInv i w
  right_inv p := Subtype.ext (chartInv_chartFun i p.1 p.2)
  continuous_toFun := Continuous.subtype_mk (continuous_chartInv i) _
  continuous_invFun := by
    have h : ContinuousOn (chartFun i) (chartSet i) := continuousOn_chartFun i
    exact continuousOn_iff_continuous_domRestrict.mp h

/-- **The affine charts of `ℂPⁿ` are contractible** (they are homeomorphic to `ℂⁿ`). -/
instance contractibleSpace_chartSet (n : ℕ) (i : Fin (n + 1)) :
    ContractibleSpace ↥(chartSet i) :=
  (chartHomeomorph n i).symm.contractibleSpace

/-! ## The standard cover of `ℂP²` -/

/-- The chart of `ℂP²` at the index `0`: the open set where the `0`-th homogeneous coordinate does
not vanish.  It is contractible. -/
abbrev cp2U : Set (CPSpace 2) := chartSet 0

/-- The complement of the point `[1 : 0 : 0]` in `ℂP²`, i.e. the union of the other two charts.
It is homotopy equivalent to `ℂP¹`. -/
abbrev cp2V : Set (CPSpace 2) := chartSet 1 ∪ chartSet 2

theorem isOpen_cp2U : IsOpen cp2U := isOpen_chartSet 0

theorem isOpen_cp2V : IsOpen cp2V := (isOpen_chartSet 1).union (isOpen_chartSet 2)

/-- The two open sets `cp2U`, `cp2V` cover `ℂP²`. -/
theorem cp2U_union_cp2V : cp2U ∪ cp2V = (Set.univ : Set (CPSpace 2)) := by
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨i, hi⟩ := exists_mem_chartSet p
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h; exact Or.inl hi
  · rcases Fin.eq_zero_or_eq_succ j with h | ⟨k, rfl⟩
    · subst h; exact Or.inr (Or.inl hi)
    · have : k = 0 := by
        have := k.isLt
        omega
      subst this
      exact Or.inr (Or.inr hi)

/-- `U = chartSet 0` of `ℂP²` is homeomorphic to `ℂ²`. -/
def cp2U_homeo : (Fin 2 → ℂ) ≃ₜ ↥cp2U := chartHomeomorph 2 0

/-- The point `[1 : 0 : 0]` of `ℂP²`, the origin of the chart `cp2U`. -/
def cp2Origin : CPSpace 2 := chartInv 0 0

/-- `[1 : 0 : 0]` is not in `cp2V = chartSet 1 ∪ chartSet 2`. -/
theorem cp2Origin_notMem_cp2V : cp2Origin ∉ cp2V := by
  have h0 : (chartInv (n := 2) 0 0) =
      cpMk 2 ⟨Fin.insertNth (α := fun _ => ℂ) 0 (1 : ℂ) 0, insertNth_one_ne_zero 0 0⟩ := rfl
  rw [cp2V, Set.mem_union, not_or]
  constructor
  · intro h
    change chartInv 0 0 ∈ chartSet 1 at h
    rw [h0] at h
    have h1 := (mem_chartSet_iff 1 _).mp h
    simp at h1
  · intro h
    change chartInv 0 0 ∈ chartSet 2 at h
    rw [h0] at h
    have h1 := (mem_chartSet_iff 2 _).mp h
    simp at h1

/-- A point of `ℂP²` in `cp2U` whose affine coordinates in the chart at `0` vanish is the origin
`[1 : 0 : 0]`. -/
theorem eq_origin_of_chartFun_eq_zero {p : CPSpace 2} (hp : p ∈ cp2U)
    (h : chartFun 0 p = 0) : p = cp2Origin := by
  have h1 : chartInv 0 (chartFun 0 p) = p := chartInv_chartFun 0 p hp
  rw [h] at h1
  rw [← h1]
  rfl

end

end Work.Projective
