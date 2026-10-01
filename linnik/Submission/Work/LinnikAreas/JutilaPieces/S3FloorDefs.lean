import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

/-!
# Definitions for the `S₃` floor reduction (`Work.LinnikAreas.JutilaPieces.S3FloorReduce`)

With `X_r = ⌊N/(q r t)⌋`, `x_r = N/(q r t) ∈ ℝ`, and the bracket
`B(M) = (log(M·t/z) − 1)(log(M·r/z) − 1) + 1`, the summand of `s3exact − s3cont`
(fixed `q,t`, after applying `s3c (r*t) = ζ(2)^{-1}(r/κ r)(t/κ t)`) is
`μ(r)·(1/κ r)·Ĝ(r)` where

  `s3Ghat z N q r t = r·( X_r·B(X_r) − x_r·B(x_r) )`.

Everything is left as a real-valued `def` so that the analytic estimates
(`s3Ghat_abs_le`, `s3Ghat_tv_le`) can be stated against it.

Also fixed here: the threshold `s3T0 c z` (a function of `z` and the input's decay
constant `c`, growing like `exp(O((log log z)^2/c^2))`, hence `o(z)`), and the
partial-sum majorant `s3Kt Ch t = max 1 (Ch·σ_{−1/2}(t))`.
-/

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-- The bracket `B(M) = (log(M·t/z) − 1)(log(M·r/z) − 1) + 1` at the natural `M = ⌊N/(q r t)⌋`. -/
def s3Bfloor (z N q r t : ℕ) : ℝ :=
  (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1)
      * (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1

/-- The bracket at the real value `M = N/(q r t)`. -/
def s3Bcont (z N q r t : ℕ) : ℝ :=
  (Real.log ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) * (t : ℝ) / (z : ℝ)) - 1)
      * (Real.log ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) * (r : ℝ) / (z : ℝ)) - 1) + 1

/-- `s3Ghat z N q r t = r·(X_r·B(X_r) − x_r·B(x_r))`, the `r`-weight of the floor reduction
(`x_r·r = N/(q t) =: Y`, `X_r·r = Y − ρ_r`). -/
def s3Ghat (z N q r t : ℕ) : ℝ :=
  (r : ℝ) * (((N / (q * r * t) : ℕ) : ℝ) * s3Bfloor z N q r t
    - ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * s3Bcont z N q r t)

/-- The split threshold: `s3T0 c z = ⌈exp(25·(log(log z + 2) + 1)²/c²)⌉ + 2`.
It satisfies `log (s3T0 c z) ≥ 25(log(log z+2)+1)²/c²`, so that
`e^{−c√(log (s3T0 c z))} ≤ 1/(e (log z + 2)⁴)`, while `s3T0 c z = o(z)`. -/
def s3T0 (c : ℝ) (z : ℕ) : ℕ :=
  Nat.ceil (Real.exp (25 * (Real.log (Real.log (z : ℝ) + 2) + 1) ^ 2 / c ^ 2)) + 2

/-- The partial-sum majorant `max 1 (Ch·σ_{−1/2}(t))`. -/
def s3Kt (Ch : ℝ) (t : ℕ) : ℝ :=
  max 1 (Ch * ∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))

end

end Work.LinnikAreas.JutilaPieces
