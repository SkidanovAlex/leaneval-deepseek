import Mathlib
import Submission.Work.L2F.Torus.Defs

open scoped MatrixGroups

namespace Work.L2F.Torus

/-- A central element of `SL(2,F)` is `±1`, in every characteristic.

Mathlib's `Matrix.SpecialLinearGroup.mem_center_iff` writes a central `z` as the scalar matrix
`r • 1` with `r ^ (Fintype.card (Fin 2)) = r ^ 2 = 1`; over a field `(r - 1) * (r + 1) = r ^ 2 - 1
= 0` forces `r = 1` or `r = -1`.  The converse is immediate since `1` and `-1` are central.

(This is `Work.L2F.Mat2.mem_center_sl_two` with its unused odd-characteristic hypothesis
`(2 : F) ≠ 0` dropped: in characteristic `2` the two alternatives coincide.) -/
theorem mem_center_iff_eq_one_or_negOne (F : Type*) [Field F]
    (z : Matrix.SpecialLinearGroup (Fin 2) F) :
    z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ↔
      z = 1 ∨ z = Work.L2F.negOne F := by
  constructor
  · intro hz
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
    obtain ⟨r, hr, hrx⟩ := hz
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hfac : (r - 1) * (r + 1) = 0 := by
      have : (r - 1) * (r + 1) = r ^ 2 - 1 := by ring
      rw [this, hr2]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · left
      have hr1 : r = 1 := sub_eq_zero.mp h
      apply Subtype.ext
      rw [← hrx, hr1, map_one]
      rfl
    · right
      have hr1 : r = -1 := add_eq_zero_iff_eq_neg.mp h
      apply Subtype.ext
      rw [← hrx, hr1, map_neg, map_one]
      rfl
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [Matrix.SpecialLinearGroup.mem_center_iff]
      exact ⟨-1, by norm_num, by rw [map_neg, map_one]; rfl⟩

/-- The centre of `SL(2,F)` is `{±1}`, and `-1 ∈ ⟨x, -1⟩`, hence the centre is contained in
`⟨x, -1⟩`. -/
theorem center_le_genZ (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≤ genZ F x := by
  intro z hz
  rw [genZ_apply]
  rcases (mem_center_iff_eq_one_or_negOne F z).mp hz with hz1 | hzn
  · rw [hz1]
    exact Subgroup.one_mem _
  · rw [hzn]
    exact Subgroup.subset_closure (by simp)

end Work.L2F.Torus
