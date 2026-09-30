import Mathlib
import Submission.Work.BMF.liouville.vmvt_stechkin_small
import Submission.Work.BMF.vkford51_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Parameters for the large-`λ` Vinogradov extraction (`vk_lambda_large_assembly`)

`λ = log t / log N`, and the Ford §5 parameters

`M = ⌈N^{2/5}⌉`, `μ = log M / log N`, `h = ⌈λ⌉`, `g = ⌈5λ⌉`, `k = g+1`,
`r' = ⌈300λ²/k⌉`, `r = k·r'`, `s' = ⌈200λ²/g⌉`, `s = g·s'`,

together with the total Stechkin excess `Δ` and the constant `C₀` that survives after the two
Stechkin inputs and the `W`-product bound are substituted into Ford's `Pprod`.
-/

namespace Work.BMF.liouville

open Finset
open scoped BigOperators

noncomputable section

/-- `λ = log t / log N`. -/
def dLam (N t : ℝ) : ℝ := Real.log t / Real.log N

/-- `M = ⌈N^{2/5}⌉`. -/
def dM (N : ℝ) : ℕ := ⌈N ^ ((2 : ℝ) / 5)⌉₊

/-- `μ = log M / log N`. -/
def dMu (N : ℝ) : ℝ := Real.log (dM N) / Real.log N

/-- `h = ⌈λ⌉`. -/
def dH (lam : ℝ) : ℕ := ⌈lam⌉₊

/-- `g = ⌈5λ⌉`. -/
def dG (lam : ℝ) : ℕ := ⌈5 * lam⌉₊

/-- `k = g + 1`. -/
def dK (lam : ℝ) : ℕ := dG lam + 1

/-- `r' = ⌈300λ²/k⌉`. -/
def dRp (lam : ℝ) : ℕ := ⌈300 * lam ^ 2 / (dK lam : ℝ)⌉₊

/-- `r = k·r'`. -/
def dR (lam : ℝ) : ℕ := dK lam * dRp lam

/-- `s' = ⌈200λ²/g⌉`. -/
def dSp (lam : ℝ) : ℕ := ⌈200 * lam ^ 2 / (dG lam : ℝ)⌉₊

/-- `s = g·s'`. -/
def dS (lam : ℝ) : ℕ := dG lam * dSp lam

/-- The exponent `H = Σ_{j=h}^{g} min(jμ₂, min(j-λ, λ-j(1-μ₁-μ₂)))` of Ford's `W`-product. -/
def dHsum (h g : ℕ) (μ1 μ2 lam : ℝ) : ℝ :=
  ∑ j ∈ Icc h g, min ((j : ℝ) * μ2) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - μ1 - μ2)))

/-- The total excess `Δ₁ + Δ₂` of the two Stechkin inputs, evaluated at the parameters
`(k, r')` and `(g, s')`. -/
def dDelta (lam : ℝ) : ℝ :=
  ((dK lam : ℝ) ^ 2 / 2) * (1 - 1 / (dK lam : ℝ)) ^ (dRp lam)
    + ((dG lam : ℝ) ^ 2 / 2) * (1 - 1 / (dG lam : ℝ)) ^ (dSp lam)

/-- The constant that remains after substituting into `Pprod` the Stechkin bounds for
`J r k M` and `J s g M`, Ford's crude incomplete-system bound, and the `W`-product bound. -/
def dC0 (lam : ℝ) : ℝ :=
  (5 * (dR lam : ℝ)) ^ (dK lam) * (dS lam : ℝ) ^ (dH lam - 1)
    * stechF (dK lam) (dRp lam) * stechF (dG lam) (dSp lam)
    * (2 : ℝ) ^ ((dG lam + 3) * (dG lam - dH lam + 1))

/-- The absolute constant `D` of the target theorem. -/
def dD : ℝ := (10 : ℝ) ^ 9

/-- The absolute constant `C = exp (10^33·(1 + stechK) + 100)` of the target theorem. -/
def dC : ℝ := Real.exp ((10 : ℝ) ^ 33 * (1 + stechK) + 100)

lemma dC_pos : 0 < dC := Real.exp_pos _
lemma dD_pos : 0 < dD := by norm_num [dD]
lemma dC_log : Real.log dC = (10 : ℝ) ^ 33 * (1 + stechK) + 100 := Real.log_exp _

end
end Work.BMF.liouville
