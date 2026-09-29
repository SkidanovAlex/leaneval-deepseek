import Mathlib

/-!
# The crude second-derivative bound template

The second-derivative bound of the slit map is obtained by the triangle inequality applied to the
closed form `slit'' = (N''w² - 2N'w + 2N)/(8rw³)`, giving an expression of the shape below in
terms of ten real quantities (the bounds `A ≥ (1+r)²`, `E ≥ 2(r-1)²`, `C1 ≥ 1+r`, the disc data
`w ≥ |w|`, `wm1 ≥ |w-1|`, `wlo ≤ |w|`, and the radicand data `Qp ≥ |Q'|`, `Qhi ≥ |Q|`,
`Slo ≤ |S|`, `Shi ≥ |S|`).  `crude` packages that shape, so that the whole numerical work is a
single monotonicity statement (`Work.ANum3.crude_mono`).
-/

namespace Work.ANum3

noncomputable section

/-- The crude second-derivative bound expression: with `A ≥ (1+r)²`, `E ≥ 2(r-1)²`, `C1 ≥ 1+r`,
`w ≥ |z|`, `wm1 ≥ |z-1|`, `wlo ≤ |z|`, `Qp ≥ |Q'|`, `Qhi ≥ |Q|`, `Slo ≤ |√Q| ≤ Shi`, the quantity
`crude r A E C1 w wm1 wlo Qp Qhi Slo Shi` is an upper bound for `‖slit r '' z‖` for
`|z - c| ≤ ρ` whenever the corresponding lower-case quantities of `c, ρ` are bounded by them. -/
def crude (r A E C1 w wm1 wlo Qp Qhi Slo Shi : ℝ) : ℝ :=
  ((2 * A + C1 * Qp / Slo + C1 * wm1 * (4 * A * Qhi + Qp ^ 2) / (4 * Slo ^ 3)) * w ^ 2
    + 2 * (E + 2 * A * w + C1 * Shi + C1 * wm1 * Qp / (2 * Slo)) * w
    + 2 * (A + E * w + A * w ^ 2 + C1 * wm1 * Shi)) / (8 * r * wlo ^ 3)

end

end Work.ANum3
