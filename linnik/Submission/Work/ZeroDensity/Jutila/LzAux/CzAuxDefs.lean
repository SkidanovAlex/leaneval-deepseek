import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

/-!
# Auxiliary objects for the evaluation of the continuous model `czModelCont`

For fixed `q` the `(r,t)`-double sum of `czModelCont w y N` factorises (after the `s3c`-identity)
into an inner `r`-sum and an outer `t`-sum, with `Y₁ = N/(q w)`, `Y₂ = N/(q y)`
(`czR w N q = ⌊Y₁⌋`, `czT y N q = ⌊Y₂⌋`):

* `czP w N q t = Σ_{r ≤ ⌊Y₁⌋, (r,t)=1} (μ(r)/κ(r))·(log(Y₁/r) − 1)`,
* `czS w N q t = Σ_{r ≤ ⌊Y₁⌋, (r,t)=1} μ(r)/κ(r)`,
* `czTq w y N q = Σ_{t ≤ ⌊Y₂⌋} (μ(t)/κ(t))·((log(Y₂/t) − 1)·czP w N q t + czS w N q t)`,
* `czG T = Σ_{t ≤ ⌊T⌋} μ(t)·(log(T/t) − 1)/t` (the sharp Mertens sum, `→ 1`).

`czP` and `czS` are evaluated by `KappaMertensInput` (`Bz3Defs.lean`), `czG` by
`BzHard.mertens_log_weighted_one`.
-/

namespace Work.ZeroDensity.Jutila.LzAux

open Finset
open Work.ZeroDensity.Jutila

noncomputable section

/-- `Y₁ = N/(q w)`: the real cut-off whose floor is the upper limit of the `r`-sum. -/
def cY1 (N q : ℕ) (w : ℝ) : ℝ := (N : ℝ) / ((q : ℝ) * w)

/-- `Y₂ = N/(q y)`: the real cut-off whose floor is the upper limit of the `t`-sum. -/
def cY2 (N q : ℕ) (y : ℝ) : ℝ := (N : ℝ) / ((q : ℝ) * y)

/-- `Σ_{r ≤ ⌊Y₁⌋, (r,t)=1} (μ(r)/κ(r))·(log(Y₁/r) − 1)`. -/
def czP (w : ℝ) (N q : ℕ) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (czR w N q),
    (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)
      * (Real.log (cY1 N q w / (r : ℝ)) - 1)

/-- `Σ_{r ≤ ⌊Y₁⌋, (r,t)=1} μ(r)/κ(r)`. -/
def czS (w : ℝ) (N q : ℕ) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (czR w N q),
    (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)

/-- The `t`-sum of the `q`-th slice of `czModelCont`,
`Σ_{t ≤ ⌊Y₂⌋} (μ(t)/κ(t))·((log(Y₂/t) − 1)·czP w N q t + czS w N q t)`. -/
def czTq (w y : ℝ) (N q : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 (czT y N q),
    ((ArithmeticFunction.moebius t : ℝ) / kap t)
      * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t)

/-- `czG T = Σ_{t ≤ ⌊T⌋} (μ(t)/t)·(log(T/t) − 1)`, which tends to `1` (`mertens_log_weighted_one`). -/
def czG (T : ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 ⌊T⌋₊,
    (ArithmeticFunction.moebius t : ℝ) * (Real.log (T / (t : ℝ)) - 1) / (t : ℝ)

end

end Work.ZeroDensity.Jutila.LzAux
