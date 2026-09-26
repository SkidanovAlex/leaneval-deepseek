import Mathlib
import Submission.Work.CountedPinch.Defs
import Submission.Work.BoxShrink.PinchOff.TangentConfig
import Submission.Work.CountedPinch.transverseSlice_std_four
import Submission.Work.PinchCounted.exists_traceCircleFamily_z

/-!
# The tameness of the equator slice `{z = 1/2}` of the standard torus

This module proves `Work.CountedPinch.tameSlice_standard_equator`, the `TameSlice` component of the
plane datum at the standard configuration `(ψ = idDiffeo, s = 4, c = 0, σ = refl, u = 1/2)`.

The trace of the plane `{z = 1/2}` with the standard torus of revolution is the union of the two
longitude circles `{φ = π/6}` and `{φ = 5π/6}` (whose planar radii are `2 ± √3/2`); both lie in the
flat disc `cutDisc 4 0 refl (1/2)` because the whole torus lies in Pardon's box `PBox 4 0 refl`,
and `sin ψ = 1/2` forces `ψ ≡ π/6` or `ψ ≡ 5π/6` modulo `2π`, so the two circles cover the slice.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CountedPinch

noncomputable section

/-! ## Elementary bounds for the standard parametrisation -/

/-- Every coordinate of a point of the standard torus of revolution is at most `3` in absolute
value: the horizontal coordinates are `(2 + cos φ) cos θ`, `(2 + cos φ) sin θ` with
`|2 + cos φ| ≤ 3`, and the vertical coordinate is `sin φ`. -/
theorem abs_torusMap_apply_le_three (θ φ : ℝ) (i : Fin 3) :
    |(Work.Core.torusMap θ φ) i| ≤ 3 := by
  fin_cases i <;> simp only [Fin.reduceFinMk]
  · rw [Work.Core.torusMap_apply_zero, abs_mul,
      abs_of_nonneg (by linarith [Real.neg_one_le_cos φ])]
    have h1 : 2 + Real.cos φ ≤ 3 := by linarith [Real.cos_le_one φ]
    have h3 : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    calc (2 + Real.cos φ) * |Real.cos θ| ≤ 3 * 1 :=
          mul_le_mul h1 h3 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3)
      _ = 3 := by ring
  · rw [Work.Core.torusMap_apply_one, abs_mul,
      abs_of_nonneg (by linarith [Real.neg_one_le_cos φ])]
    have h1 : 2 + Real.cos φ ≤ 3 := by linarith [Real.cos_le_one φ]
    have h3 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    calc (2 + Real.cos φ) * |Real.sin θ| ≤ 3 * 1 :=
          mul_le_mul h1 h3 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3)
      _ = 3 := by ring
  · rw [Work.Core.torusMap_apply_two]
    have h3 : |Real.sin φ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin φ, Real.sin_le_one φ⟩
    linarith

/-- **The whole standard torus lies in Pardon's box `PBox 4 0 refl`**: every coordinate is at most
`3` in absolute value and each half-side length `boxSide i * 4` is at least `4`. -/
theorem torusMap_mem_PBox_four (θ φ : ℝ) :
    Work.Core.torusMap θ φ ∈ Submission.PBox 4 (0 : R3) (Equiv.refl (Fin 3)) := by
  rw [Submission.mem_PBox]
  intro i
  have hle := abs_torusMap_apply_le_three θ φ i
  have hside := Submission.one_le_boxSide i
  have h4 : (3:ℝ) < Submission.boxSide i * 4 := by nlinarith
  calc |(Work.Core.torusMap θ φ) (Equiv.refl (Fin 3) i) - (0 : R3) (Equiv.refl (Fin 3) i)|
      = |(Work.Core.torusMap θ φ) i| := by simp
    _ ≤ 3 := hle
    _ < Submission.boxSide i * 4 := h4

/-! ## The two longitude circles of the equator slice -/

/-- The meridian parameters of the two longitude circles in the plane `{z = 1/2}`: `π/6` and
`5π/6`, the two solutions of `sin φ = 1/2` modulo `2π`. -/
def equatorParam (i : Fin 2) : ℝ := if (i : ℕ) = 0 then Real.pi / 6 else 5 * Real.pi / 6

/-- **The solutions of `sin ψ = 1/2`** are congruent modulo `2π` to `π/6` or to `5π/6`. -/
theorem sin_eq_half_cong (ψ : ℝ) (hψ : Real.sin ψ = 1 / 2) :
    (∃ k : ℤ, ψ = Real.pi / 6 + (k : ℝ) * (2 * Real.pi)) ∨
    (∃ k : ℤ, ψ = 5 * Real.pi / 6 + (k : ℝ) * (2 * Real.pi)) := by
  have hsin : Real.sin (Real.pi / 6) = Real.sin ψ := by rw [Real.sin_pi_div_six]; exact hψ.symm
  obtain ⟨k, hk | hk⟩ := (Real.sin_eq_sin_iff (x := Real.pi/6) (y := ψ)).mp hsin
  · left; exact ⟨k, by rw [hk]; ring⟩
  · right; exact ⟨k, by rw [hk]; ring⟩

/-- `sin (5π/6) = 1/2`. -/
theorem sin_five_pi_div_six : Real.sin (5 * Real.pi / 6) = 1 / 2 := by
  have h : 5 * Real.pi / 6 = Real.pi - Real.pi / 6 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_six]

/-- **The longitude circle at a solution `φ` of `sin φ = 1/2` lies in the flat disc**
`cutDisc 4 0 refl (1/2)`: its points are `torusMap θ φ ∈ PBox 4 0 refl` (the whole torus is inside
the box) and have vertical coordinate `sin φ = 1/2`. -/
theorem longitudeCurve_mem_cutDisc (φ θ : ℝ) (hφ : Real.sin φ = 1 / 2) :
    (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard φ).γ θ ∈
      Work.BoxShrink.Core.cutDisc 4 (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) := by
  rw [Work.BoxShrink.Core.mem_cutDisc]
  refine ⟨?_, ?_⟩
  · change Work.Core.torusMap θ φ ∈ Submission.PBox 4 (0 : R3) (Equiv.refl (Fin 3))
    exact torusMap_mem_PBox_four θ φ
  · change (Work.Core.torusMap θ φ).ofLp 2 = (0 : R3).ofLp 2 + 1 / 2
    rw [Work.Core.torusMap_apply_two, hφ]
    simp

/-! ## The two circles are disjoint -/

/-- `5π/6` is not congruent to `π/6` modulo `2π`. -/
theorem not_cong_five_pi_six (k : ℤ) :
    5 * Real.pi / 6 ≠ Real.pi / 6 + (k : ℝ) * (2 * Real.pi) := by
  intro h
  have hk : (k : ℝ) = 1 / 3 := by nlinarith [Real.pi_pos, h]
  have h0 : (0 : ℤ) < k := by
    have : (0:ℝ) < (k:ℝ) := by rw [hk]; norm_num
    exact_mod_cast this
  have h1 : k < 1 := by
    have : (k:ℝ) < 1 := by rw [hk]; norm_num
    exact_mod_cast this
  omega

/-- `π/6` is not congruent to `5π/6` modulo `2π`. -/
theorem not_cong_pi_six (k : ℤ) :
    Real.pi / 6 ≠ 5 * Real.pi / 6 + (k : ℝ) * (2 * Real.pi) := by
  intro h
  refine not_cong_five_pi_six (-k) ?_
  push_cast
  linarith

/-! ## The instance -/

/-- **A non-degenerate instance of the tameness of the plane route**: the standard torus, the box
`PBox 4 0 (refl (Fin 3))` (which contains the whole torus) and the cutting plane `{z = 1/2}`
(`σ = refl`, `u = 1/2`).

The trace of the plane with the torus is the union of the two circles `longitudeCurve standard φ`
for `φ = π/6` and `φ = 5π/6` (radii `2 ± √3/2`): they are simple, pairwise disjoint, lie in the flat
disc `cutDisc 4 0 (refl (Fin 3)) (1/2)`, and cover the slice pointwise (`sin v = 1/2` forces
`v ≡ π/6` or `v ≡ 5π/6`).  Hence the tameness `TameSlice` of the workspace holds there, i.e.
`Work.Smooth.Plane.TransversePlane standard (cutDisc 4 0 (refl (Fin 3)) (1/2))`.

The workspace already has the circle-family machinery for exactly this configuration in
`Submission/Work/PinchCounted/exists_traceCircleFamily_z.lean`: `mem_slice_z_iff`,
`slice_subset_two_longitudeCurves` and `disjoint_range_longitudeCurve`.

With `transverseSlice_std_four` (the plane is transverse at the same configuration) this is the
second component of the body of `CountedSlicePlane` at a configuration whose slice is *non-empty*
and compact — the trace of the plane does not leave the box. -/
theorem tameSlice_standard_equator :
    Work.BoxShrink.Pinch.TameSlice Work.BoxShrink.PinchOff.idDiffeo 4
      (0 : LeanEval.KnotTheory.PardonDistortion.R3) (Equiv.refl (Fin 3)) (1 / 2) := by
  change Work.Smooth.Plane.TransversePlane Work.CoreTopology.standard
    (Work.BoxShrink.Core.cutDisc 4 (0 : R3) (Equiv.refl (Fin 3)) (1 / 2))
  refine ⟨Fin 2, inferInstance,
    fun i => Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (equatorParam i),
    Fin 0, inferInstance, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the closed components are simple
    intro i
    exact Work.CoreTopology.longitudeCurve_simple _ _
  · -- distinct closed components are disjoint
    intro i j hij
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    obtain rfl | rfl := hi
    · obtain rfl | rfl := hj
      · exact absurd rfl hij
      · exact Work.PinchCounted.disjoint_range_longitudeCurve not_cong_five_pi_six
    · obtain rfl | rfl := hj
      · exact Work.PinchCounted.disjoint_range_longitudeCurve not_cong_pi_six
      · exact absurd rfl hij
  · -- the closed components lie in the flat disc
    intro i t
    fin_cases i
    · exact longitudeCurve_mem_cutDisc (Real.pi / 6) t Real.sin_pi_div_six
    · exact longitudeCurve_mem_cutDisc (5 * Real.pi / 6) t sin_five_pi_div_six
  · intro j; exact j.elim0
  · intro j; exact j.elim0
  · intro j; exact j.elim0
  · intro j; exact j.elim0
  · intro j; exact j.elim0
  · -- the two circles cover the slice pointwise
    intro x hxD hxc
    left
    have hxs : x ∈ {y : R3 | y 2 = 1 / 2} ∩ Work.CoreTopology.standard.carrier := by
      refine ⟨?_, hxc⟩
      rw [Work.BoxShrink.Core.mem_cutDisc] at hxD
      simpa using hxD.2
    have hcov := Work.PinchCounted.slice_subset_two_longitudeCurves (v := 1 / 2)
      (a := Real.pi / 6) (b := 5 * Real.pi / 6) sin_eq_half_cong
    rcases hcov hxs with hh | hh
    · exact ⟨0, hh⟩
    · exact ⟨1, hh⟩

end

end Work.CountedPinch
