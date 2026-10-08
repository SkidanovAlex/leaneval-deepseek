import Mathlib

namespace Work.A7REC.Char

/-- In the dihedral group of order `8 = 2 * 4`, the two reflections `sr 0`, `sr 1` are
involutions whose product is the rotation `r 1` of order `4`. Consequently at least one of the
two reflections lies outside any subgroup all of whose elements square to `1`. Transporting back
along `e` gives an involution outside `W`. -/
theorem involutionNotMemFour {H : Type*} [Group H] (e : H ≃* DihedralGroup 4)
    (W : Subgroup H) (hW : ∀ w ∈ W, w * w = 1) : ∃ t : H, t * t = 1 ∧ t ∉ W := by
  -- `r 1` is a rotation of order `4`, so it is not an involution.
  have hr : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.r 1 ≠ 1 := by
    simp [DihedralGroup.r_mul_r]
    decide
  -- The two reflections `sr 0` and `sr 1` are involutions.
  have haa : e.symm (DihedralGroup.sr 0) * e.symm (DihedralGroup.sr 0) = 1 := by
    rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
  have hbb : e.symm (DihedralGroup.sr 1) * e.symm (DihedralGroup.sr 1) = 1 := by
    rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
  -- Their product is the rotation `r 1`.
  have hab : e.symm (DihedralGroup.sr 0) * e.symm (DihedralGroup.sr 1)
      = e.symm (DihedralGroup.r 1) := by
    rw [← map_mul, DihedralGroup.sr_mul_sr, sub_zero]
  by_cases ha : e.symm (DihedralGroup.sr 0) ∈ W
  · -- If `sr 0` lies in `W`, then `sr 1` cannot: otherwise their product `r 1` would lie in `W`,
    -- contradicting `hW` since `r 1` is not an involution.
    refine ⟨e.symm (DihedralGroup.sr 1), hbb, fun hb => ?_⟩
    have hm : e.symm (DihedralGroup.r 1) * e.symm (DihedralGroup.r 1) = 1 := by
      have h := hW _ (W.mul_mem ha hb)
      rwa [hab] at h
    have key : e.symm (DihedralGroup.r 1 * DihedralGroup.r 1) = 1 := by
      rw [map_mul]; exact hm
    exact hr (by simpa using congrArg e key)
  · exact ⟨e.symm (DihedralGroup.sr 0), haa, ha⟩

end Work.A7REC.Char
