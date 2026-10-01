/-
# Definitions for the evaluation of the continuous model `s3cont` (`S3ModelEval`)

`Work.ZeroDensity.Jutila.s3cont` is the continuous model of the `S₃` triple sum of
`Bz3MainTerm` (`⌊N/(qrt)⌋` replaced by the real `N/(qrt)`).  Its evaluation
(`S3ModelEval`, An arXiv:2206.10104 §5, `k = ℚ`) proceeds by rewriting the summand with the
"good" weight `μ(n)/κ(n)`, isolating for each `t` the `r`-sum (which is evaluated by the
Mertens-type input `KappaMertensInput`), and then summing over `t` and `q`.

This file fixes the objects of that computation:

* `wm n = μ(n)/κ(n)`, the weight of the (Graham/An) Möbius reciprocal sums, `κ = kap`;
* `RS1 Q t B = Σ_{r ≤ B, (r,t)=1} (μ(r)/κ(r))·(log(Q/r) − 1)`, the inner `r`-sum with the log;
* `RS0 t B = Σ_{r ≤ B, (r,t)=1} μ(r)/κ(r)`, the same without the log;
* `Qf z N q = N/(q z)`, the real cut-off (`= (N/z)/q`), and
* `s3DSabs Q B`, the `t`-sum of the continuous model at cut-off `Q` in "good weight" form.

The two structural facts are `s3cont = ζ(2)^{-1}·Σ_{q ≤ N/z}(N/q)·s3DSabs (Qf z N q) (N/(qz))`
(the pointwise identity `s3c(r t) = ζ(2)^{-1}(r/κ(r))(t/κ(t))` for coprime squarefree `r,t`,
`Bz3Defs.s3c_mul_eq_of_coprime`, together with `N/(q r t) = (N/q)/(r t)`), and
`s3DSabs Q B = ζ(2)·Σ_{t ≤ B}(μ(t)/t)(log(Q/t) − 1) + O(ε(B)(log Q)^4)` (the input applied to
the `r`-sum for squarefree `t`).
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-- The "good weight" `wm n = μ(n)/κ(n)` (`κ = kap c = ∏_{p ∣ c}(p+1)`). -/
def wm (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ) / Work.ZeroDensity.Jutila.kap n

/-- The inner `r`-sum of the continuous model with the logarithm:
`RS1 Q t B = Σ_{r ≤ B, (r,t)=1} (μ(r)/κ(r))·(log(Q/r) − 1)`. -/
def RS1 (Q : ℝ) (t B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 B, (if Nat.Coprime r t then wm r else 0) * (Real.log (Q / (r : ℝ)) - 1)

/-- The inner `r`-sum of the continuous model: `RS0 t B = Σ_{r ≤ B, (r,t)=1} μ(r)/κ(r)`. -/
def RS0 (t B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 B, (if Nat.Coprime r t then wm r else 0)

/-- The real cut-off `Qf z N q = N/(q z) = (N/z)/q`. -/
def Qf (z N q : ℕ) : ℝ := (N : ℝ) / ((q : ℝ) * (z : ℝ))

/-- `s3DSabs Q B` is the `t`-sum of the continuous model at the cut-off `Q` and `B = ⌊Q⌋`:
`Σ_{t ≤ B} (μ(t)/κ(t))·((log(Q/t) − 1)·RS1 Q t B + RS0 t B)`. -/
def s3DSabs (Q : ℝ) (B : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 B,
    wm t * ((Real.log (Q / (t : ℝ)) - 1) * RS1 Q t B + RS0 t B)

end

end Work.LinnikAreas.JutilaPieces
