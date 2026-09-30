import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the Blanksby–Montgomery argument

The Fourier-analytic proof of `Work.BW.mahlerMeasure_lehmer_bound` averages
`σ k = ∑_j log ‖1 - ε_j · exp (2 π i k θ_j)‖` over `k ≤ K` with the Fejér weights
`w k = 1 - k/(K+1)`, with the two analytic inputs
* `logMoment_le` : `∑_k w k * σ k ≤ 1/2 * ∑_j log (1/(1-ε_j))`, and
* `logMoment_sq_ge_lin` : `∑_k w k * (σ k)^2 ≥ (K+1)/4 * ∑_j ε_j^2 - (∑_j ε_j) * ∑_j log(1/(1-ε_j))`.

The parameters of the argument (Blanksby–Montgomery, §3, with `A = 48/5`, `B = 54/5`) are
`ρ' = 1 - 1/(12 N)` (so that `R = 1/(1-ρ') = 12 N` exactly), `K = ⌊B N log R⌋`, and
`ε_j = min ρ' (‖z_j‖^K)` where `z_j` is the member of the `j`-th inverse pair of roots of
modulus `≤ 1`.
-/

namespace Work.BW

open scoped BigOperators

/-- The dilogarithm `dilog x = ∑_{m ≥ 1} x^m / m^2`. -/
noncomputable def dilog (x : ℝ) : ℝ := ∑' m : ℕ, x^(m+1) / ((m:ℝ)+1)^2

/-- The parameter `A = 48/5` of the averaging argument. -/
noncomputable def A0 : ℝ := 48/5

/-- The parameter `B = 54/5` of the averaging argument. -/
noncomputable def B0 : ℝ := 54/5

/-- `ρ' = 1 - 1/(12 N)`; this makes `R = 1/(1-ρ') = 12 N`. -/
noncomputable def rhoP (N : ℕ) : ℝ := 1 - 1/(12*(N:ℝ))

/-- The averaging range `K = ⌊B N log (12 N)⌋`. -/
noncomputable def KK (N : ℕ) : ℕ := ⌊B0 * (N:ℝ) * Real.log (12*(N:ℝ))⌋₊

/-- The upper bound `log (1/(1-ε))` for `log (1/(1-ε_j))`, where `ε ≥ exp(-1/A)`. -/
noncomputable def c0 : ℝ := Real.log (1/(1 - Real.exp (-(1/A0))))

/-- The upper bound `log (1+ρ')` for `log (1+ε_j)`. -/
noncomputable def ellP (N : ℕ) : ℝ := Real.log (1 + rhoP N)

end Work.BW
