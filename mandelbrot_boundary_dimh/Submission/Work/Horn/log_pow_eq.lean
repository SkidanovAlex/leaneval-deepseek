import Mathlib

/-!
# The principal logarithm commutes with powers, on a sector

If `u` has argument `θ` with `|θ| * q < π` (so the whole `q`-fold power stays
inside the open sector of width `2π`, i.e. `q * θ` is still the principal
argument of `u ^ q`), then `log (u ^ q) = q * log u` for the principal branch
`Complex.log`.
-/

namespace Work.Horn

theorem log_pow_eq {u : ℂ} {q : ℕ} (hq : 1 ≤ q) (hu : u ≠ 0)
    (h : |u.arg| * (q : ℝ) < Real.pi) :
    Complex.log (u ^ q) = (q : ℂ) * Complex.log u := by
  have _ : u ^ q ≠ 0 := pow_ne_zero q hu
  -- `q` is a positive real (written as a real, since all estimates are real)
  have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  -- the exponentiated argument `q * θ` is strictly inside `(-π, π)`
  have habs : |(q : ℝ) * u.arg| < Real.pi := by
    rw [abs_mul, abs_of_nonneg hqnonneg, mul_comm]
    exact h
  have hmem : (q : ℝ) * u.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    obtain ⟨h1, h2⟩ := abs_lt.mp habs
    exact ⟨h1, le_of_lt h2⟩
  have htoReal : ((q : ℝ) * u.arg : Real.Angle).toReal = (q : ℝ) * u.arg :=
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hmem
  -- the argument of the power is `q * θ` as an angle
  have hangle : ((u ^ q).arg : Real.Angle) = ((q : ℝ) * u.arg : Real.Angle) := by
    rw [Complex.arg_pow_coe_angle, ← Real.Angle.coe_nsmul, nsmul_eq_mul]
  -- hence, since `q * θ` is the principal value, the principal arguments agree
  have harg : (u ^ q).arg = (q : ℝ) * u.arg := by
    have := congrArg Real.Angle.toReal hangle
    rwa [Complex.arg_coe_angle_toReal_eq_arg, htoReal] at this
  -- and the moduli multiply as usual
  have hlog : Real.log ‖u ^ q‖ = (q : ℝ) * Real.log ‖u‖ := by
    rw [Complex.norm_pow, Real.log_pow]
  show Real.log ‖u ^ q‖ + (u ^ q).arg * Complex.I =
    (q : ℂ) * (Real.log ‖u‖ + u.arg * Complex.I)
  rw [hlog, harg]
  push_cast
  ring

end Work.Horn
