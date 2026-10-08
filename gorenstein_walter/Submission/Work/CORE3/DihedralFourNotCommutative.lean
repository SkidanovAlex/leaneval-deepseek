import Mathlib

namespace Work.CORE3

open DihedralGroup

/-- `DihedralGroup 4` (the dihedral group of order `8`) is not commutative: the rotation `r 1` and
the reflection `sr 0` do not commute.  Indeed `r 1 * sr 0 = sr (0 - 1) = sr 3` while
`sr 0 * r 1 = sr (0 + 1) = sr 1`, by `DihedralGroup.r_mul_sr` and `DihedralGroup.sr_mul_r`, and
`sr 3 ≠ sr 1` in `ZMod 4`. -/
lemma dihedralFour_not_comm : ∃ x y : DihedralGroup 4, x * y ≠ y * x := by
  refine ⟨DihedralGroup.r 1, DihedralGroup.sr 0, ?_⟩
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  intro h
  exact absurd (DihedralGroup.sr.inj h) (by decide)

-- (put this in `namespace Work.CORE3`, so the full name is `Work.CORE3.DihedralFourNotCommutative`)
/-- `DihedralGroup 4` (order `8`) is not commutative.  Proof: `DihedralGroup.r 1 * DihedralGroup.sr 0 =
DihedralGroup.sr (0 - 1)` and `DihedralGroup.sr 0 * DihedralGroup.r 1 = DihedralGroup.sr 1` by
`DihedralGroup.r_mul_sr` and `DihedralGroup.sr_mul_r`, and `sr` is injective with `-1 ≠ 1` in
`ZMod 4`; transport along the given isomorphism. -/
theorem DihedralFourNotCommutative {S : Type} [Group S]
    (h : Nonempty (S ≃* DihedralGroup 4)) : ∃ x y : S, x * y ≠ y * x := by
  obtain ⟨e⟩ := h
  obtain ⟨x, y, hxy⟩ := dihedralFour_not_comm
  refine ⟨e.symm x, e.symm y, fun hc => hxy ?_⟩
  have h1 : e (e.symm x * e.symm y) = e (e.symm y * e.symm x) := by rw [hc]
  simpa using h1

end Work.CORE3
