import Mathlib.Algebra.Order.Star.Real

namespace Commons.Combinatorics.EFLArith

set_option linter.unusedVariables false in
/-- Rearrangement lemma: under the constraints `0 < ρ ≤ 1`, `0 < γ`, `1000γ ≤ ρε`,
`1000ε ≤ 1`, `n/200 - 1 ≤ m ≤ n` and `20000 ≤ ρn`, we have
`3ρm/4 ≤ ρ(m - εn) - 13γn - 1`.

The proof reduces to showing `ρ*m/4 ≥ ρ*ε*n + 13*γ*n + 1`, which follows from
`γ ≤ ρε/1000`, `ε ≤ 1/1000` (giving `ρ*ε*n + 13*γ*n ≤ 1013*ρ*n/10^6`) and
`m ≥ n/200 - 1` combined with `ρ*n ≥ 20000`. -/
theorem internal_arith {ρ ε γ m : ℝ} {n : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hγ : 0 < γ)
    (hγε : 1000 * γ ≤ ρ * ε) (hεs : 1000 * ε ≤ 1)
    (hm1 : (n : ℝ) / 200 - 1 ≤ m) (hm2 : m ≤ n) (hρn : 20000 ≤ ρ * n) :
    3 * ρ * m / 4 ≤ ρ * (m - ε * n) - 13 * γ * n - 1 := by
  nlinarith [hρn, hρ, hρ1, hγ, hγε, hεs, hm1, hm2]

end Commons.Combinatorics.EFLArith