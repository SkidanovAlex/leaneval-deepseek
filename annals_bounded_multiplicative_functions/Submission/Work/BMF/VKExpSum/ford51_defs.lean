import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.vkford_defs
import Submission.Work.BMF.liouville.vmvt_stechkin_defs
import Submission.Work.BMF.liouville.vmvt_stechkin_small

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Parameters and constants for `ford51_lambda_large`

The Ford §5 extraction (`Work.BMF.vkford_lemma51`) is applied with

`λ = log t / log N`, `μ = log M / log N`, `M = ⌈N^{2/5}⌉` (so `M₁ = M₂ = M`, `μ₁ = μ₂ = μ`),
`h = ⌈λ⌉`, `g = ⌈5λ⌉`, `k = g + 1`, `r' = ⌈300λ²/k⌉`, `r = k r'`, `s' = ⌈200λ²/g⌉`, `s = g s'`.

The final constants of the target theorem are `dC = exp (1000 + 100·stechK)` and `dD = 10^9`.
-/

namespace Work.BMF.VKExpSum

open Finset
open scoped BigOperators

noncomputable section

/-- `h = ⌈λ⌉`. -/
def dH (lam : ℝ) : ℕ := ⌈lam⌉₊

/-- `g = ⌈5λ⌉`. -/
def dG (lam : ℝ) : ℕ := ⌈5 * lam⌉₊

/-- `k = ⌈5λ⌉ + 1`. -/
def dK (lam : ℝ) : ℕ := dG lam + 1

/-- `r' = ⌈300λ²/k⌉`. -/
def dRp (lam : ℝ) : ℕ := ⌈300 * lam ^ 2 / (dK lam : ℝ)⌉₊

/-- `r = k ⌈300λ²/k⌉`. -/
def dR (lam : ℝ) : ℕ := dK lam * dRp lam

/-- `s' = ⌈200λ²/g⌉`. -/
def dSp (lam : ℝ) : ℕ := ⌈200 * lam ^ 2 / (dG lam : ℝ)⌉₊

/-- `s = g ⌈200λ²/g⌉`. -/
def dS (lam : ℝ) : ℕ := dG lam * dSp lam

/-- `M = ⌈N^{2/5}⌉`. -/
def dM (N : ℝ) : ℕ := ⌈N ^ ((2 : ℝ) / 5)⌉₊

/-- `μ = log M / log N`. -/
def dMu (N : ℝ) : ℝ := Real.log (dM N) / Real.log N

/-- The absolute constant `D = 10^9` of the target theorem. -/
def dD : ℝ := (10 : ℝ) ^ 9

/-- The absolute constant `C = exp (1000 + 100·stechK)` of the target theorem. -/
def dC : ℝ := Real.exp (1000 + 100 * Work.BMF.liouville.stechK)

end

end Work.BMF.VKExpSum
