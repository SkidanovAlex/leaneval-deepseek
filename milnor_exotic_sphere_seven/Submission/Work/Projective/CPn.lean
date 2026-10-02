import Mathlib
import Submission.Work.Projective.Cover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The standard two-piece cover of `ℂPⁿ` by a chart and the complement of a point

For every `n`, the projective space `ℂPⁿ` is covered by

* `cpU n = chartSet 0` — the affine chart at `0`, homeomorphic to `ℂⁿ`, hence contractible;
* `cpV n = ⋃_{i ≠ 0} chartSet i` — the complement of the point `[1 : 0 : … : 0]`, which
  deformation retracts onto the hyperplane `{z₀ = 0} ≅ ℂP^{n-1}`,

and the intersection `cpU n ∩ cpV n` is the chart `cpU n` with the origin removed, i.e. `ℂⁿ ∖ {0}`,
which is homotopy equivalent to `S^{2n-1}`.

This is the cover on which the Mayer–Vietoris computation of `H^*(ℂPⁿ;ℤ)` is based; for `n = 2` the
pieces and their cohomology are computed in `Submission/Work/Projective/cp2V_cohomology.lean`,
`cp2UV_cohomology.lean` and assembled in `CP2Cohomology.lean`.  The general `n` is treated in
`CPnCohomology.lean`.

## Conventions

`cpV` is written as the union of the *charts* `i ≠ 0` rather than as a set difference, so that
openness is immediate; `cpOrigin n = chartInv 0 0` is the point `[1 : 0 : … : 0]`, the origin of the
chart `cpU n`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-- The chart of `ℂPⁿ` at the index `0`: the open set where the `0`-th homogeneous coordinate does
not vanish.  It is homeomorphic to `ℂⁿ`, hence contractible. -/
abbrev cpU (n : ℕ) : Set (CPSpace n) := chartSet 0

/-- The complement of the point `[1 : 0 : … : 0]` in `ℂPⁿ`, written as the union of the charts
`i ≠ 0`.  It deformation retracts onto the hyperplane `{z₀ = 0} ≅ ℂP^{n-1}`. -/
def cpV (n : ℕ) : Set (CPSpace n) :=
  ⋃ i ∈ {i : Fin (n + 1) | i ≠ 0}, chartSet i

theorem mem_cpV_iff {n : ℕ} {p : CPSpace n} :
    p ∈ cpV n ↔ ∃ i : Fin (n + 1), i ≠ 0 ∧ p ∈ chartSet i := by
  constructor
  · intro h
    obtain ⟨i, h'⟩ := Set.mem_iUnion.mp (by simpa only [cpV] using h)
    obtain ⟨hi, hmem⟩ := Set.mem_iUnion.mp h'
    exact ⟨i, hi, hmem⟩
  · rintro ⟨i, hi, hmem⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hmem⟩⟩

theorem isOpen_cpU (n : ℕ) : IsOpen (cpU n) := isOpen_chartSet 0

theorem isOpen_cpV (n : ℕ) : IsOpen (cpV n) :=
  isOpen_biUnion fun i _ => isOpen_chartSet i

/-- The two open sets `cpU n` and `cpV n` cover `ℂPⁿ`. -/
theorem cpU_union_cpV (n : ℕ) : cpU n ∪ cpV n = (Set.univ : Set (CPSpace n)) := by
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨i, hi⟩ := exists_mem_chartSet p
  by_cases h : i = 0
  · exact Or.inl (by simpa [h] using hi)
  · exact Or.inr (mem_cpV_iff.mpr ⟨i, h, hi⟩)

/-- The point `[1 : 0 : … : 0]` of `ℂPⁿ`, the origin of the chart `cpU n`. -/
def cpOrigin (n : ℕ) : CPSpace n := chartInv 0 0

theorem cpOrigin_apply (n : ℕ) :
    cpOrigin n = cpMk n ⟨Fin.insertNth (α := fun _ => ℂ) 0 (1 : ℂ) 0,
      insertNth_one_ne_zero 0 0⟩ := rfl

/-- `[1 : 0 : … : 0]` is not in `cpV n`. -/
theorem cpOrigin_notMem_cpV (n : ℕ) : cpOrigin n ∉ cpV n := by
  intro h
  obtain ⟨i, hi, hmem⟩ := mem_cpV_iff.mp h
  rw [cpOrigin_apply] at hmem
  have h1 := (mem_chartSet_iff i _).mp hmem
  have h2 : (Fin.insertNth (α := fun _ => ℂ) 0 (1 : ℂ) 0 : Fin (n + 1) → ℂ) i = 0 := by
    rw [insertNth_apply_of_ne (i := (0 : Fin (n + 1))) (j := i) hi, Pi.zero_apply]
  exact h1 h2

/-- A point of `cpU n` whose chart coordinates vanish is the origin `[1 : 0 : … : 0]`. -/
theorem eq_cpOrigin_of_chartFun_eq_zero {n : ℕ} {p : CPSpace n} (hp : p ∈ cpU n)
    (h : chartFun 0 p = 0) : p = cpOrigin n := by
  have h1 : chartInv 0 (chartFun 0 p) = p := chartInv_chartFun 0 p hp
  rw [h] at h1
  rw [← h1]
  rfl

end

end Work.Projective
