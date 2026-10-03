import Mathlib

/-!
# `Work.Pert.stripChart`: the conformal chart from a vertical strip to the closed unit disc

For `h > 0` the map

    stripChart h ζ = (exp (i π ζ / (2h)) - 1) / (exp (i π ζ / (2h)) + 1) = tanh (i π ζ / (4h))

maps the vertical strip `{ζ | |ζ.re| ≤ h}` into the closed unit disc, and is a conformal map of
the open strip onto the open disc.  It is the chart used to transfer the Schwarz–Pick estimate
for the unit disc to functions mapping a disc into such a strip: on the strip the exact identity

    1 - ‖stripChart h ζ‖ ^ 2 = (4 h / π) * cos (π * ζ.re / (2h)) * ‖deriv (stripChart h) ζ‖

holds, so that `(1 - ‖stripChart h ζ‖ ^ 2) / ‖deriv (stripChart h) ζ‖ ≤ 4h/π`.
-/

namespace Work.Pert

noncomputable section

/-- The conformal chart `ζ ↦ (exp (iπζ/(2h)) - 1)/(exp (iπζ/(2h)) + 1)` from the vertical strip
`|Re ζ| ≤ h` to the closed unit disc. -/
def stripChart (h : ℝ) (ζ : ℂ) : ℂ :=
  (Complex.exp (Complex.I * (Real.pi / (2 * h)) * ζ) - 1) /
    (Complex.exp (Complex.I * (Real.pi / (2 * h)) * ζ) + 1)

end

end Work.Pert
