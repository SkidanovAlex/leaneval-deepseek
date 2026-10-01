/-
# ZeroFreeTables — HB88TentDefs

Shared definitions for the **tent-function route** to `Work.ZeroFreeTables.HBLemma8_8`
(Heath-Brown, PLMS 64 (1992), Lemma 8.8).

## Why the tent

HB's §8.1 test function `f(t) = max (x − t) 0` (`tent x` in `HB88Defs`) has a *completely
explicit* Laplace transform: with `F(z) = ∫₀^x e^{−zt} f(t) dt` and `σ = −z`,

  `G(σ) := ∫₀^x e^{σt} f(t) dt = (e^{σx} − 1)/σ² − x/σ`  (`σ ≠ 0`),  `G(0) = x²/2`,

`f(0) = x`, and `G` is convex increasing on `ℝ`.  This makes the *numerical certificates* of
the five-term (resp. same-character) rows — the strict failure of HB Lemma 8.5 (resp. 6.3) at a
point `(b,c)` of the `λ`-plane — explicit elementary inequalities in exponentials.

Numerically (high precision, `Decimal` 50 digits) the tent certifies, for an optimal width `x`
per row, the *whole target curve* `c = (12/11) log(1/b)` with a margin:

| `b` | target `(12/11)log(1/b)` | max certifiable `c` | best `x` |
|---|---|---|---|
|0.08 | 2.7553 | 2.8992 | 1.20 |
|0.05 | 3.2681 | 3.4791 | 1.16 |
|0.02 | 4.2677 | 4.6162 | 1.11 |
|0.01 | 5.0238 | 5.4740 | 1.09 |
|0.005| 5.7800 | 6.3273 | 1.06 (x=0.60 grid) |
|0.002| 6.7796 | 7.446  | 1.045 |

so a *finite table* of ~20 rows `(b, c, x)` covers `lam1 ∈ [10⁻⁵ , 0.08]`, `HBTable7_proof`
covers `lam1 ∈ [0.08, 0.745]` (its row `(0.10, 2.76)` is the binding one), and for
`lam1 → 0` the *fixed-width* tent (width `x = 2A + η`, `A = 11/24 + 4ε₀`) gives the asymptotic

  `log(1/lam1) ≤ x·lam2 + log(2/(x − 2A)) + 2 log(1/lam2)`,

i.e. `lam2 ≥ (12/11 − ε)·log(1/lam1)` once `log(1/lam1)` is large enough (no uniformity in the test
function is needed: the width is *fixed* per row / per asymptotic).

Everything is phrased in the frozen vocabulary (`Work.LinnikContract`), plus `tent` from
`Work.ZeroFreeTables.HB88Defs`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB88Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- The Laplace transform of the tent of width `X` at `σ` (real argument):
`∫₀^X e^{σ t} max (X − t) 0 dt = (e^{σ X} − 1)/σ² − X/σ` for `σ ≠ 0`, and `X²/2` for `σ = 0`. -/
def tentFm (σ X : ℝ) : ℝ :=
  if σ = 0 then X ^ 2 / 2 else (Real.exp (σ * X) - 1) / σ ^ 2 - X / σ

/-- The five-term combination of HB Lemma 8.5 specialised to the tent of width `X`:
`G(lam2) − G(lam2 − lam1) − G(0) + X·A`. -/
def tentFive (X A lam1 lam2 : ℝ) : ℝ :=
  tentFm lam2 X - tentFm (lam2 - lam1) X - X ^ 2 / 2 + X * A

/-- The same-character (HB Lemma 6.3) combination for the tent of width `X`:
`2G(λ') − 2G(λ' − lam1) − G(0) + X·A`. -/
def tentSame (X A lam1 lamu : ℝ) : ℝ :=
  2 * tentFm lamu X - 2 * tentFm (lamu - lam1) X - X ^ 2 / 2 + X * A

end Work.ZeroFreeTables
