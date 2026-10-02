import Mathlib
import Submission.Work.Projective.CPn
import Submission.Work.Projective.nonempty_continuousLinearEquiv
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `U ∩ V` in `ℂPⁿ` is homotopy equivalent to `S^{2n-1}`

Here `U = cpU n = chartSet 0` and `V = cpV n = ⋃_{i ≠ 0} chartSet i`.  The chart at `0`
identifies `U` with `ℂⁿ` and, under this identification, the points of `V` correspond exactly
to the *nonzero* vectors of `ℂⁿ`:

`U ∩ V ≅ ℂⁿ ∖ {0} ≃ₕ S^{2n-1}`.

The last equivalence is `Work.Cohomology.punctured_homotopyEquiv_sphere` (radial normalization),
and `ℂⁿ` is identified with the Euclidean space `ℝ^{2n}` by a real continuous linear equivalence.

This is the general-`n` version of `Work.Projective.cp2UV_homotopyEquiv_sphere`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-! ## The chart at `0` identifies `U ∩ V` with the punctured model space -/

/-- A vector `w : ℂⁿ` has `chartInv 0 w ∈ cpV n` precisely when `w ≠ 0`: the only chart through
the origin of the chart at `0` is the chart at `0` itself, and all other charts say that some
coordinate of `w` is nonzero. -/
theorem cpnUV_chartInv_mem_iff (n : ℕ) (w : Fin n → ℂ) :
    chartInv 0 w ∈ cpV n ↔ w ≠ 0 := by
  rw [mem_cpV_iff]
  constructor
  · rintro ⟨i, hi, hmem⟩
    rw [chartInv_apply, mem_chartSet_iff i ⟨_, insertNth_one_ne_zero 0 w⟩] at hmem
    change (Fin.insertNth (α := fun _ => ℂ) 0 (1 : ℂ) w) i ≠ 0 at hmem
    rw [insertNth_apply_of_ne 0 i hi 1 w] at hmem
    intro hw
    exact hmem (by simp [hw])
  · intro hw
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    refine ⟨Fin.succAbove (0 : Fin (n + 1)) k, Fin.succAbove_ne 0 k, ?_⟩
    rw [chartInv_apply, mem_chartSet_iff _ ⟨_, insertNth_one_ne_zero 0 w⟩]
    change (Fin.insertNth (α := fun _ => ℂ) 0 (1 : ℂ) w) (Fin.succAbove 0 k) ≠ 0
    rw [Fin.insertNth_apply_succAbove (α := fun _ => ℂ)]
    simpa using hk

/-- A point of `U ∩ V` has non-vanishing chart coordinates in the chart at `0`: if `chartFun 0`
vanished at `p`, then `p` would be the origin `[1 : 0 : … : 0]`, which is not in `V`. -/
theorem chartFun_ne_zero_of_mem_cpnUV (n : ℕ) (p : ↥(cpU n ∩ cpV n)) :
    chartFun 0 p.1 ≠ 0 := by
  intro h
  have h1 : p.1 = cpOrigin n := eq_cpOrigin_of_chartFun_eq_zero p.2.1 h
  exact cpOrigin_notMem_cpV n (h1 ▸ p.2.2)

/-- **The chart at `0` identifies `U ∩ V` with the punctured model space `ℂⁿ ∖ {0}`.** -/
noncomputable def cpnUV_homeo (n : ℕ) :
    ↥(cpU n ∩ cpV n) ≃ₜ {z : Fin n → ℂ // z ≠ 0} where
  toFun p := ⟨chartFun 0 p.1, chartFun_ne_zero_of_mem_cpnUV n p⟩
  invFun z := ⟨chartInv 0 z.1,
    ⟨chartInv_mem_chartSet 0 z.1, (cpnUV_chartInv_mem_iff n z.1).mpr z.2⟩⟩
  left_inv p := Subtype.ext (chartInv_chartFun 0 p.1 p.2.1)
  right_inv z := Subtype.ext (chartFun_chartInv 0 z.1)
  continuous_toFun := Continuous.subtype_mk
    ((chartHomeomorph n 0).continuous_invFun.comp
      (Continuous.subtype_mk continuous_subtype_val fun p => p.2.1))
    (chartFun_ne_zero_of_mem_cpnUV n)
  continuous_invFun := Continuous.subtype_mk
    ((continuous_chartInv 0).comp continuous_subtype_val)
    (fun z => ⟨chartInv_mem_chartSet 0 z.1, (cpnUV_chartInv_mem_iff n z.1).mpr z.2⟩)

/-! ## Passing to the Euclidean model `ℝ^{2n}` -/

/-- The punctured model space `ℂⁿ ∖ {0}` is homeomorphic to the punctured Euclidean space
`ℝ^{2n} ∖ {0}` (both are real normed spaces of dimension `2n`). -/
theorem cpnUV_punctured_homeo (n : ℕ) :
    Nonempty ({z : Fin n → ℂ // z ≠ 0} ≃ₜ
      {v : EuclideanSpace ℝ (Fin (2 * n)) // v ≠ 0}) := by
  obtain ⟨L⟩ := nonempty_continuousLinearEquiv n
  exact ⟨{ toFun := fun z => ⟨L z.1, fun h => z.2 (L.map_eq_zero_iff.mp h)⟩
           invFun := fun v => ⟨L.symm v.1, fun h => v.2 (by
             rw [← L.apply_symm_apply v.1, h, map_zero])⟩
           left_inv := fun z => Subtype.ext (L.symm_apply_apply z.1)
           right_inv := fun v => Subtype.ext (L.apply_symm_apply v.1)
           continuous_toFun := Continuous.subtype_mk
             (L.continuous.comp continuous_subtype_val) _
           continuous_invFun := Continuous.subtype_mk
             (L.symm.continuous.comp continuous_subtype_val) _ }⟩

/-! ## The homotopy equivalence with the sphere -/

/-- **`U ∩ V = chartSet 0 ∩ ⋃_{i ≠ 0} chartSet i` in `ℂPⁿ` is homotopy equivalent to
`S^{2n-1} ⊆ ℝ^{2n}`.** -/
theorem cpnUV_homotopyEquiv_sphere (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(Work.Projective.cpU n ∩ Work.Projective.cpV n)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n))) 1)) := by
  obtain ⟨hP⟩ := cpnUV_punctured_homeo n
  obtain ⟨hsph⟩ :=
    Work.Cohomology.punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin (2 * n)))
  exact ⟨(cpnUV_homeo n).toHomotopyEquiv.trans (hP.toHomotopyEquiv.trans hsph)⟩

end

end Work.Projective
