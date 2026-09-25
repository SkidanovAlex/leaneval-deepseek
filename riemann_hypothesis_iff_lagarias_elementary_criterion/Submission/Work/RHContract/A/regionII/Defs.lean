import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.ca_exp_eq_one_of_gt_xi2
import Submission.Work.RHContract.A.ca_exp_eq_two_of_between

/-!
# Region II: definitions and numeric interfaces

Route (see `ROUTE_LEAD.md` §2.3/2.5 and `Work/RHContract/NOTES.md`):

For a colossally abundant number `N = N_ε` with largest prime factor `ξ = ξ(ε)` and
`ξ₂ = max{p : a_p ≥ 2}` one has, under `RH`,

`Δ := γ + logloglog N − log(σ(N)/N) ≥ −J(ξ) + caC·Δ_N ...`

in the form of `key_identity`: `Δ = J + (logloglog N − loglog ψ) − W + Σ_p b_p − primeTail ξ`.
The two *positive* contributions to the right are

* `caC ε · Δ_N` (via `loglog_step`), where `Δ_N = log N − ψ(ξ)`;
* `Σ_{p ∈ supp} b_p − primeTail ξ`.

Per prime `p ≤ ξ` with `e_p = ⌊log ξ / log p⌋` the contribution
`caC·(a_p − e_p)·log p + b_p − t_p` is bounded below by

* `c1 p = 1/(2p²) − 1/(3p³)` when `p > ξ₂` (there `a_p = e_p = 1`, `p > √ξ`);
* `c2 p = caC·log p − 1/(2p(p−1))` when `√ξ < p ≤ ξ₂` (there `a_p = 2`, `e_p = 1`);
* `−max(0, 1/(ξ·(e_p+1)·(1−1/p)) − caC·log p)` when `p ≤ √ξ` (deep levels).

Using `ξ₂⁻ := √(2ξ)(1 − log 2/(2 log ξ)) ≤ ξ₂ ≤ ⌈√(2.5ξ)⌉ =: ξU` and the fact that
`q ↦ Σ_{q<p≤ξ} c1 p + Σ_{√ξ<p≤q} (caC log p − 1/(2p(p−1)))` is *increasing* in `q`, the whole
arithmetic gain is at least `caT ξ − caK3 ξ` where

`caT ξ = Σ_{ξ₂⁻<p≤ξ} c1 p + caC·(θ(ξ₂⁻) − θ(√ξ)) − Σ_{√ξ<p≤ξ₂⁻} 1/(2p(p−1))`

and `caK3 ξ` collects the deep-level losses.  Both `caT` and `caK3` are bounded below/above by
explicit expressions using the certified Chebyshev bounds of
`Commons.NumberTheory.Chebyshev.theta_bracket_finite_range` (tables `CL`/`CU`, valid on
`[59,10^5]`), `theta_lower_96_1e7` (on `[10^5,10^7]`) and `theta_lower_ninetenths`.

The final step is the explicit inequality
`caT_lb ξ − caK3_ub ξ ≥ (caCJ ξ + caWub ξ) * caU ξ`.
-/

open scoped ArithmeticFunction.sigma
open scoped BigOperators

namespace Work.RHContract.A.RegionII

noncomputable section

/-- `u ξ = 1/(√ξ log ξ)`: the natural scale of the margin. -/
def caU (ξ : ℝ) : ℝ := 1 / (Real.sqrt ξ * Real.log ξ)

/-- The constant of the `J`-lower bound `psiTail_ge_of_RH`. -/
def caCJ (ξ : ℝ) : ℝ :=
  (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) *
      (5 + 7 / Real.log ξ + 4 / (Real.log ξ) ^ 2)
    + Real.log (2 * Real.pi) / Real.sqrt ξ + 1 / ξ

/-- The constant of the `W`-upper bound: `W ≤ caWub ξ * u ξ`. -/
def caWub (ξ : ℝ) : ℝ :=
  let v := (0.45 * ξ ^ (3 / 4 : ℝ) + 2) / ξ
  v ^ 2 * (1 + 1 / Real.log ξ) / (2 * Real.log ξ * (1 - v) ^ 2)

/-- `ξ₂⁻ = √(2ξ)(1 − log 2/(2 log ξ))`: the proved lower bound for `ξ₂(ε)`. -/
def caXi2lo (ξ : ℝ) : ℝ := Real.sqrt (2 * ξ) * (1 - Real.log 2 / (2 * Real.log ξ))

/-- `ξU = ⌈√(2.5ξ)⌉`: the proved upper bound for `ξ₂(ε)`. -/
def caXiU (ξ : ℝ) : ℕ := Nat.ceil (Real.sqrt (2.5 * ξ))

/-- `c1 p = 1/(2p²) − 1/(3p³)`. -/
def caC1 (p : ℝ) : ℝ := 1 / (2 * p ^ 2) - 1 / (3 * p ^ 3)

/-- `c2 p = caC·log p − 1/(2p(p−1))`, with the coefficient `caC` supplied. -/
def caC2 (c p : ℝ) : ℝ := c * Real.log p - 1 / (2 * p * (p - 1))

/-- The certified lower bound for `caC ε` (via `ψ(ξ) ≤ ξ + 0.45ξ^{3/4} + 2`). -/
def caClo (ξ : ℝ) : ℝ :=
  (1 - 3 / Real.sqrt ξ) /
    ((ξ + 0.45 * ξ ^ (3 / 4 : ℝ) + 2) * Real.log (ξ + 0.45 * ξ ^ (3 / 4 : ℝ) + 2))

/-- `g t = 1/(t² log t)`, the Abel weight of `Σ 1/p²`. -/
def caG (t : ℝ) : ℝ := 1 / (t ^ 2 * Real.log t)

/-- The certified deficit constant: `θ t ≥ t − caDefL t * √t` on `[173,10^5]`. -/
def caDefL (t : ℝ) : ℝ :=
  if t < 220 then 1.76 else if t < 280 then 1.95 else if t < 350 then 1.91
    else if t < 450 then 1.78 else if t < 600 then 1.91 else if t < 800 then 1.59
    else if t < 1000 then 1.76 else if t < 1300 then 1.71 else if t < 1700 then 2.06
    else if t < 2200 then 1.78 else if t < 2800 then 1.9 else if t < 3600 then 1.9
    else if t < 4600 then 1.45 else if t < 6000 then 1.86 else if t < 7800 then 1.83
    else if t < 10000 then 1.76 else 1.95

/-- The certified upper-deficit constant: `θ t ≤ t − caDefU t * √t` on `[173,10^5]`. -/
def caDefU (t : ℝ) : ℝ :=
  if t < 220 then 0.7 else if t < 280 then 0.87 else if t < 350 then 0.64
    else if t < 450 then 1.06 else if t < 600 then 0.73 else if t < 800 then 0.73
    else if t < 1000 then 0.82 else if t < 1300 then 0.69 else if t < 1700 then 0.53
    else if t < 2200 then 0.8 else if t < 2800 then 0.73 else if t < 3600 then 0.61
    else if t < 4600 then 0.65 else if t < 6000 then 0.61 else if t < 7800 then 0.58
    else if t < 10000 then 0.54 else 0.45

/-- `θ`-lower bound function used in the Abel bounds. -/
def caThL (t : ℝ) : ℝ := t - caDefL t * Real.sqrt t

/-- `θ`-upper bound function used in the Abel bounds. -/
def caThU (t : ℝ) : ℝ := t - caDefU t * Real.sqrt t

end
end Work.RHContract.A.RegionII
