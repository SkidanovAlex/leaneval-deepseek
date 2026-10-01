import Mathlib

/-!
# Definitions for the unimodality of `x ↦ x^(σ-1) · (e^{-x/A} − e^{-x/B})`

For `σ ∈ (0,1]` and `0 < B < A` put `c = 1/B − 1/A > 0` and

`g(x) = x^(σ-1) · (e^{-x/A} − e^{-x/B})`,   `x > 0`.

We have `g(x) = x^(σ-1) · e^{-x/A} · (1 − e^{-cx})` (because `e^{-cx} = e^{-x/B + x/A}`),
so `log g(x) = (σ-1)·log x − x/A + log(1 − e^{-cx})`; its derivative is

`Dlog(x) = (σ-1)/x − 1/A + c/(e^{cx} − 1) = Φ(x)/x`,

where `Φ(x) = x·Dlog(x) = (σ-1) − x/A + c·x/(e^{cx} − 1)`.

`Φ` is strictly antitone on `(0,∞)` (since `t ↦ t/(e^t − 1)` is antitone), is positive
near `0` and negative for large `x`, so it has a single zero `x₀`, which is the unique
maximum of `g`.
-/

noncomputable section

namespace Work.LinnikAreas2

/-- `β t = t / (e^t − 1)`. -/
def beta (t : ℝ) : ℝ := t / (Real.exp t - 1)

/-- `Φ x = x · (d/dx) log g(x)` for `g x = x^(σ-1)·(e^{-x/A} − e^{-x/B})`. -/
def Phi (σ A B : ℝ) (x : ℝ) : ℝ :=
  (σ - 1) - x / A + (1 / B - 1 / A) * x / (Real.exp ((1 / B - 1 / A) * x) - 1)

/-- `log` of the function `g x = x^(σ-1)·(e^{-x/A} − e^{-x/B})` on `(0,∞)`. -/
def Lfun (σ A B : ℝ) (x : ℝ) : ℝ :=
  (σ - 1) * Real.log x - x / A + Real.log (1 - Real.exp (-((1 / B - 1 / A) * x)))

/-- The function `x ↦ x^(σ-1)·(e^{-x/A} − e^{-x/B})`. -/
def gfun (σ A B : ℝ) (x : ℝ) : ℝ :=
  x ^ (σ - 1) * (Real.exp (-(x / A)) - Real.exp (-(x / B)))

end Work.LinnikAreas2
