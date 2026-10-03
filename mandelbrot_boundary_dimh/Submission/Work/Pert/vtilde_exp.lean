import Mathlib

namespace Work.Pert

theorem vtilde_exp {α z F s : ℂ} (hα : α ≠ 0)
    (hF : F = z + (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (1 - s))
    (hs : 1 - s ≠ 0) :
    (1 - s) / Complex.exp (2 * Real.pi * Complex.I * α)
      = Complex.exp (2 * Real.pi * Complex.I * α * (F - z - 1)) := by
  -- Rewrite the exponent using the defining relation for `F`, then undo the
  -- logarithm via `exp_log` and recombine the exponentials.
  have harg : 2 * Real.pi * Complex.I * α * (F - z - 1)
      = Complex.log (1 - s) - 2 * Real.pi * Complex.I * α := by
    rw [hF]
    field_simp
    ring
  rw [harg, Complex.exp_sub, Complex.exp_log hs]

end Work.Pert
