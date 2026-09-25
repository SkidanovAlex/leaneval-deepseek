import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# Region III (`ξ = caXi ε ≥ 10^8`): the scale and the constants

`RegionIII.caU ξ = 1/(√ξ · log ξ)` is the natural scale of the margin inequality of
`Work.RHContract.A.regionIII_margin_positive`; the left-hand side of that theorem is
`RegionIII.caCJ ξ * RegionIII.caU ξ`, and the four quantities of the margin satisfy
(in the region `ξ ≥ 10^8`, under `|ψ t − t| ≤ 0.45 t^{3/4} + 2` for `t ≥ √ξ`)

* `caC1 ε ≥ (44/100) * caU ξ`,
* `caNet2 ε ≥ −(1/200) * caU ξ`,
* `caK3 ε ≤ (1/100) * caU ξ`,
* `caW ε ≤ (11/100) * caU ξ`,

while `caCJ ξ ≤ 1/4`; the sum of the four bounds is `0.315 * caU ξ` (see
`regionIII_margin_positive`).
-/

namespace Work.RHContract.A.RegionIII

noncomputable section

/-- `u(ξ) = 1/(√ξ log ξ)`, the scale of the margin. -/
def caU (ξ : ℝ) : ℝ := 1 / (Real.sqrt ξ * Real.log ξ)

/-- `caCJ ξ = β(5 + 7/L + 4/L²) + log(2π)/√ξ + 1/ξ` with `β = 2 + γ − log 4π`, `L = log ξ`;
the numerator of the left-hand side of the margin inequality. -/
def caCJ (ξ : ℝ) : ℝ :=
  (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
      * (5 + 7 / Real.log ξ + 4 / (Real.log ξ) ^ 2)
    + Real.log (2 * Real.pi) / Real.sqrt ξ + 1 / ξ

/-- The upper bound `W ≤ caWbd ξ` for `Margin.caW ε`, proved from
`|ψ ξ − ξ| ≤ 0.45 ξ^{3/4} + 2`: with `v = (0.45 ξ^{3/4} + 2)/ξ`,
`caWbd ξ = v²(1 + 1/log ξ)/(2 log ξ (1−v)²)`. -/
def caWbd (ξ : ℝ) : ℝ :=
  let v := (0.45 * ξ ^ (3 / 4 : ℝ) + 2) / ξ
  v ^ 2 * (1 + 1 / Real.log ξ) / (2 * Real.log ξ * (1 - v) ^ 2)

end

end Work.RHContract.A.RegionIII
