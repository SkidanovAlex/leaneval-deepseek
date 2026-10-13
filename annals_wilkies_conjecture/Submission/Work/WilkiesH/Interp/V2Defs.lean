import Mathlib
import Submission.Work.WilkiesH.Defs

/-!
# Area I (`v2` route) — the numerical vocabulary of the interpolation step

The Siegel–Wilkie interpolation step of BNZ Prop. 6.1 produces, for each small box `V` of the
chart domain, an integral polynomial `P_V` of degree `≤ d` and coefficients `≤ Q` whose jet of
order `≤ b` at the box centre is bounded by `ρ`-powers (see
`Work.WilkiesH.Interp.siegel_poly_exists`).  The Taylor bound (`Interp.poly_comp_taylor_bound`)
then gives an upper bound on `|P_V|` on the box, and Liouville
(`Interp.vanishes_of_bounds`) forces `P_V = 0` at the points of bounded degree and height.

This file fixes the *numerical* quantities that the estimate compares:

* `above μ b d Q ρ ε` — the upper bound for `|P_V (x∘e)|` at a point of degree `≤ g`,
  height `≤ H` within `ε` of the chart: the Taylor part at the box centre plus the Lipschitz
  part (`ε` times the gradient bound);
* `liou μ d Q g H` — the Liouville lower bound
  `1 / (monoCount (μ+1) d · Q · H^{((μ+1)+1)·d·g})^g`;
* `exists_params_v2` supplies `b, d, ρ, Q, ε` making the Siegel cardinality condition hold and
  `above < liou`, with `b`, the box count `⌈1/ρ⌉^μ`, the product degree `⌈1/ρ⌉^μ·d`, `b+1`
  (the smoothness order `r`) and `log (1/ε)` all bounded by one polynomial `q` in
  `(D, g, log H)`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Interp

open WilkiesConjecture

/-- The upper bound for `|P_V (y)|` at a point `y` of degree `≤ g`, height `≤ H` within `ε` of
the chart, for a box of radius `ρ`, a polynomial of degree `≤ d` and coefficient bound `Q`:

* the Taylor part at the box centre, `√(monoCount(μ+1,d)) · ρ^b · Σ_{j≤b} ((√μ)^{3j} d^j)/j!`
  (from the jet bound `|D^j F(t₀)(v^j)| ≤ ρ^{b-j}√monoCount·d^j·μ^j·‖v‖^j` of
  `Interp.siegel_poly_exists` and `‖v‖ ≤ √μ·ρ`);
* the Taylor remainder `monoCount·Q·(d+1)^{b+1}·(√μ ρ)^{b+1}/(b+1)!`;
* the Lipschitz term `monoCount·Q·d·(μ+1)·ε`. -/
noncomputable def above (μ b d Q : ℕ) (ρ ε : ℝ) : ℝ :=
  Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * ρ ^ b
      * (∑ j ∈ Finset.range (b + 1),
          ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / (((j.factorial : ℕ) : ℝ)))
    + (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * ((d : ℝ) + 1) ^ (b + 1)
      * ((Real.sqrt (μ : ℝ) * ρ) ^ (b + 1)) / ((((b + 1).factorial : ℕ) : ℝ))
    + (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * (d : ℝ) * ((μ : ℝ) + 1) * ε

/-- The Liouville lower bound for a nonzero evaluation at a point of degree `≤ g` and
height `≤ H`. -/
noncomputable def liou (μ d Q g H : ℕ) : ℝ :=
  1 / ((Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ)
        * (H : ℝ) ^ (((μ + 1) + 1) * d * g)) ^ g

end Work.WilkiesH.Interp
