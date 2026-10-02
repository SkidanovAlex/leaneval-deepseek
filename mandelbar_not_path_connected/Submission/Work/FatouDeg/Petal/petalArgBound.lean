import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- A point of the sector `c |Im z| < Re z` (with `c > 0`) has argument strictly inside
`(-arctan(1/c), arctan(1/c))`. -/
theorem petalArgBound (c : ℝ) (hc : 0 < c) {z : ℂ} (hre : 0 < z.re)
    (hs : c * |z.im| < z.re) : |z.arg| < Real.arctan (1 / c) := by
  have hz : z ≠ 0 := by rintro rfl; simp at hre
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have harglt : |z.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hcos : Real.cos |z.arg| = z.re / ‖z‖ := by
    rw [Real.cos_abs]; exact Complex.cos_arg hz
  have hsin : Real.sin |z.arg| = |z.im| / ‖z‖ := by
    rw [← Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [harglt, Real.pi_pos])]
    rw [Complex.sin_arg]
    rw [abs_div, abs_of_nonneg (norm_nonneg z)]
  have htan : Real.tan |z.arg| = |z.im| / z.re := by
    rw [Real.tan_eq_sin_div_cos, hsin, hcos]
    field_simp
  have hratio : |z.im| / z.re < 1 / c := by
    rw [div_lt_div_iff₀ hre hc]
    nlinarith [hs]
  have hIoo : |z.arg| ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [abs_nonneg z.arg, Real.pi_pos], harglt⟩
  have harctan : Real.arctan (|z.im| / z.re) = |z.arg| :=
    Real.arctan_eq_of_tan_eq htan hIoo
  rw [← harctan]
  exact Real.arctan_lt_arctan_iff.mpr hratio

end Work.FatouDeg.Petal
