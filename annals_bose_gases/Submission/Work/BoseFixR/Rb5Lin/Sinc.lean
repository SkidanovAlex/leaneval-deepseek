import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.sincR` — the (normalised) cardinal sine

The auxiliary vocabulary shared by the proof of
`Work.BoseFixR.lattice_W1sq_over_tau_le` and by its delegated pieces
(`lattice_sinc_kernel_le`, `radial_fourier_sinc`, `coulomb_radial_shell`).

`sincR x = sin x / x` for `x ≠ 0` and `sincR 0 = 1` (the continuous extension).  It is the
spherical average of the plane wave: `⨍_{|x| = r} e^{i⟪q,x⟫} dx = sincR (‖q‖ * r)`, which is
why the radial Fourier transform of a radial function is the one-dimensional integral of
`r² · ψ r · sincR (‖q‖ * r)`.
-/

noncomputable section

namespace Work.BoseFixR

/-- The cardinal sine, with its removable singularity filled in by `1`. -/
noncomputable def sincR (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

@[simp] theorem sincR_zero : sincR 0 = 1 := by simp [sincR]

theorem sincR_of_ne {x : ℝ} (hx : x ≠ 0) : sincR x = Real.sin x / x := by
  simp [sincR, hx]

theorem abs_sincR_le_one (x : ℝ) : |sincR x| ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxpos : 0 < |x| := abs_pos.mpr hx
    rw [sincR_of_ne hx, abs_div]
    rw [div_le_one hxpos]
    simpa using Real.abs_sin_le_abs (x := x)

end Work.BoseFixR
