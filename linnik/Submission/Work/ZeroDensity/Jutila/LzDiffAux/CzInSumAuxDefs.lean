import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.czReindexDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.ModelBDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

/-!
# Vocabulary for the `czInSum` (Region II) estimate

`czInSum w y N q r` is the `t`-sum of Region II of the two-sided `S₃` boundary term,
`Σ_{t ≤ czTmax} [t ⟂ r]·(μ(t)·t/κ(t))·⌊w/t⌋·czFII w y r t`.  The reference point of the
estimate is the *continuous model* obtained by replacing `⌊w/t⌋` by `w/t` and the floor
defect `log(⌊w/t⌋·t/w)` by `0`: it equals `(w/t)·(2 − log(Y/t))` with `Y = w·r/y`.

Writing `σ_t = log(⌊w/t⌋·t/w) ∈ (−log 2, 0]` (the floor defect of `w/t`, so that
`⌊w/t⌋·t = w·e^{σ_t}`) and `L_t = log(Y/t)`, the logarithmic middle factor splits as

`czFII w y r t = (2 − L_t) + σ_t·(σ_t + L_t − 2)`,

because `log(⌊w/t⌋·r/y) = σ_t + L_t`.  Hence the `t`-th term of `czInSum` is

`(μ(t)/κ(t))·w·[(2 − L_t) + Φ(σ_t,L_t)]`,  `Φ(σ,L) = e^σ·((σ−1)(σ+L−1)+1) − (2−L)`,

and the main term `−(π²/6)·w·κ(r)/r` is produced by the Mertens input (`KappaMertensInput`)
applied to `Σ (μ(t)/κ(t))·(L_t − 1)`, while the floor corrections are `O(σ_t²(1+|L_t|))`.
-/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila

noncomputable section

/-- `Y = w·r/y`: the scale of the `t`-sum of `czInSum`. -/
def czYv (w y : ℝ) (r : ℕ) : ℝ := w * (r : ℝ) / y

/-- `σ_t = log(⌊w/t⌋·t/w)`: the floor defect of `w/t`, so that `⌊w/t⌋·t = w·e^{σ_t}`. -/
def czSv (w : ℝ) (t : ℕ) : ℝ := Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (t : ℝ) / w)

/-- `L_t = log(Y/t)` with `Y = czYv w y r`. -/
def czLv (w y : ℝ) (r t : ℕ) : ℝ := Real.log (czYv w y r / (t : ℝ))

/-- The floor-correction factor `Φ(σ,L) = e^σ·((σ−1)(σ+L−1)+1) − (2−L)`. -/
def czPhiv (s L : ℝ) : ℝ := Real.exp s * ((s - 1) * (s + L - 1) + 1) - (2 - L)

end

end Work.ZeroDensity.Jutila.LzDiffAux
