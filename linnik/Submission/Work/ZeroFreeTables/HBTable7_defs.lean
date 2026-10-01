/-
# ZeroFreeTables — HBTable7_defs

The numerical side of Heath-Brown's Table 7 (`λ₂` for real `χ₁`, `ρ₁`), in the
shape in which it is read off the paper (HB §8, third method, Lemma 8.7).

## The test function

The certificate uses the extremal test function of HB Lemma 7.1 at the *fixed*
angle `θ = π/4` and parameter `λ`, i.e. HB's closed form

`f_λ(t) = λ(1+tan²θ)[λ(1+tan²θ)(γ - t/2)cos(ζt) + λ(2γ - t) + sin(2θ-ζt)/sin 2θ - 2(1 + sin(θ-ζt)/sin θ)]`

on `[0, 2γ]` (`ζ = λ tan θ`, `γ = θ/ζ`), which for `θ = π/4` reduces to

`f_λ(t) = 2λ[(π/2 - λt - 1)cos(λt) + 2 sin(λt) + π/2 - λt - 2]`.

Writing `u = λt` (so that `t` runs over `[0, π/(2λ)]` as `u` runs over
`[0, π/2]`), the Laplace transform `F_λ(z) = ∫₀^{2γ} e^{-zt} f_λ(t) dt` becomes

`F_λ(z) = Φ(z/λ)`,  `Φ(w) = ∫₀^{π/2} e^{-wu} · shape u du`,

with `shape` the function of `tfShape` below.  The paper's exact values

`F_λ(0) = (π/2 - 2)²`,  `f_λ(0) = 2λ(π - 3)`,  `F_λ(-λ) = 5 - 3π/2`

are the `w = 0`, `w = -1` cases.

## The certificate

For each row `(b, c)` of Table 7 (`λ₁ ≤ b ⟹ λ₂ ≥ c`) the certificate is the
*strict failure* of HB (8.11) at `(b, c)` for suitable `k, λ`:

`(k² + 1/2)(F_λ(-c) - F_λ(b - c)) - 2k F_λ(0) + f_λ(0)·(ψ(k) + E) < 0`,

`ψ(k) = (1/8)(k² + 1/2) + (1/6)(4k + 1)` (`Engine.psi87`) and `E = 2(k+1)²ε` the
slack of the engine `lemma8_7` at the same `ε`.  Since HB (8.11) holds with
`≥ 0` for the true pair `(λ₁, λ₂)`, and its left hand side is increasing in
`λ₂` and in `λ₁`, this forces `λ₂ > c` whenever `λ₁ ≤ b`.

The parameters actually used are the paper's choices: `k = 0.98 - 0.15b`
(`0.965, 0.962, ..., 0.868`) and the per-row `λ` of Table 7 optimised
(`0.9758, 0.9624, ...`); each row's margin is between `6·10⁻⁵` and `9·10⁻⁴`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Engine

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- The shape of HB Lemma 7.1's test function at `θ = π/4`, scaled so that the
test function of parameter `λ` is `t ↦ λ · tfShape (λ t)`. -/
def tfShape (u : ℝ) : ℝ :=
  2 * ((Real.pi / 2 - u - 1) * Real.cos u + 2 * Real.sin u + Real.pi / 2 - u - 2)

/-- The Laplace transform `Φ(w) = ∫₀^{π/2} e^{-wu} tfShape u du` of the shape, so that
`F_λ(z) = tfF λ z`. -/
def tfF (lam z : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..(Real.pi / 2), Real.exp (-(z / lam) * u) * tfShape u

/-- The slack of the engine `lemma8_7` at `ε`: its left hand side carries
`f 0 * ((k²+1/2)(c₁+2ε) + 2k(2c+2ε) + (c+ε))`, and with `c₁ = 1/8`, `c = 1/6`
this is `f 0 * (psi87 k + E)`. -/
def tfSlack (k ε : ℝ) : ℝ := 2 * (k + 1) ^ 2 * ε

/-- The certificate condition of one row `(b, c)`: HB (8.11) with `λ₁ = b`,
`λ₂ = c` is *strictly violated*. -/
def CertRow (b c k lam ε : ℝ) : Prop :=
  0 < lam ∧ 0 ≤ k ∧
    (k ^ 2 + 1 / 2) * (tfF lam (-c) - tfF lam (b - c)) - 2 * k * tfF lam 0
      + (2 * lam * (Real.pi - 3)) * (psi87 k + tfSlack k ε) < 0

end Work.ZeroFreeTables

/-
## Recipe for the certificate (for whoever proves `table7_rows_cert`)

`tfF lam z = Φ (z/lam)` with `Φ w = ∫₀^{π/2} e^{-wu} shape u du`.  Since

`shape u = 2[(π/2 - u - 1)cos u + 2 sin u + π/2 - u - 2]`

is a polynomial times `cos`/`sin`, `Φ` has the explicit closed form

`Φ w = 2[ (π/2-1)·Ic - Iuc + 2·Is + (π/2-2)·Ie - Iue ]`

on `w ≠ 0`, where (all evaluated from `0` to `L = π/2`)

* `Ie  = ∫ e^{-wu}   = (1 - e^{-wL})/w`,
* `Iue = ∫ u e^{-wu} = 1/w² - e^{-wL}(L/w + 1/w²)`,
* `Ic  = ∫ cos u · e^{-wu} = (e^{-wL} + w)/(1+w²)`,
* `Is  = ∫ sin u · e^{-wu} = (1 - w·e^{-wL})/(1+w²)`,
* `Iuc = ∫ u cos u · e^{-wu} = L·Ic(L) - (−w·Ic(L) + Is(L))/(1+w²)`.

At `w = 0`: `Φ 0 = (π/2 - 2)²`.  At `w = -1`: `Φ (-1) = 5 - 3π/2`.

The only transcendental inputs of the closed form at a rational `w = -q` are
`π` and `e^{qπ/2}`.  `π` has rational `norm_num` bounds (`Real.pi_gt_3141592`,
`Real.pi_lt_3141593`, or the `Real.pi_gt_d…`/`Real.pi_lt_d…` family); for
`e^x` (`x = qπ/2 ∈ (π/2, 4.5)` here) use `Real.exp_bound` — it assumes
`|x| ≤ 1`, so write `e^x = (e^{x/m})^m` with `m` chosen so that `|x/m| ≤ 1`,
bound `e^{x/m}` rationally from `Real.exp_bound`, and raise to the `m`-th power
(`m = 10` suffices for the exponents here, and the resulting rational bounds
are `norm_num`-checkable).  Alternatively the `bound` tactic handles `Real.exp`
at rational arguments directly.

The row values used (margins `6·10⁻⁵ … 9·10⁻⁴`, `ε = 10⁻⁶`):

| `b` | `c` | `k = 0.98-0.15b` | `λ` |
|---|---|---|---|
| 0.10 | 2.76 | 0.965 | 0.9758 |
| 0.12 | 2.56 | 0.962 | 0.9624 |
| 0.14 | 2.39 | 0.959 | 0.9497 |
| 0.16 | 2.25 | 0.956 | 0.9395 |
| 0.18 | 2.12 | 0.953 | 0.9281 |
| 0.20 | 2.01 | 0.950 | 0.9187 |
| 0.25 | 1.77 | 0.9425 | 0.8942 |
| 0.30 | 1.58 | 0.935 | 0.8725 |
| 0.35 | 1.42 | 0.9275 | 0.8514 |
| 0.40 | 1.29 | 0.920 | 0.8331 |
| 0.45 | 1.18 | 0.9125 | 0.8164 |
| 0.50 | 1.08 | 0.905 | 0.7988 |
| 0.55 | 1.00 | 0.8975 | 0.7848 |
| 0.60 | 0.92 | 0.890 | 0.7677 |
| 0.65 | 0.85 | 0.8825 | 0.7516 |
| 0.70 | 0.79 | 0.875 | 0.7371 |
| 0.745 | 0.745 | 0.8682 | 0.7260 |
-/
