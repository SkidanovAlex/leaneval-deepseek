import Mathlib
import Submission.Work.EQ.GermSetup

namespace Work.EQ

open Complex

/-- Telescoping step for the linear part `GlinOf` of the residual: multiplying
`GlinOf a ρ (λ^{2j+1} u)` by `λ^{4j+2}` (with `λ = lamC a`) produces the difference of two
consecutive terms of the geometric family `λ^{4k} ρ(λ^{2k} u)`, scaled by `a`:
`λ^{4j+2} Glin(λ^{2j+1}u) = a λ^{4(j+1)} ρ(λ^{2(j+1)}u) - a λ^{4j} ρ(λ^{2j}u)`.
This is the step that makes `∑_j λ^{4j+2} Glin(λ^{2j+1}u)` telescope. -/
theorem glin_step {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ρ : ℂ → ℂ) (u : ℂ) (j : ℕ) :
    (lamC a) ^ (4 * j + 2) * GlinOf a ρ ((lamC a) ^ (2 * j + 1) * u)
      = (a : ℂ) * ((lamC a) ^ (4 * (j + 1)) * ρ ((lamC a) ^ (2 * (j + 1)) * u))
        - (a : ℂ) * ((lamC a) ^ (4 * j) * ρ ((lamC a) ^ (2 * j) * u)) := by
  have hne : lamC a ≠ 0 := lamC_ne_zero_gs ha0 ha1
  -- `λ * (λ^{2j+1} u) = λ^{2(j+1)} u`
  have harg1 : lamC a * ((lamC a) ^ (2 * j + 1) * u) = (lamC a) ^ (2 * (j + 1)) * u := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ]
    ring
  -- `(λ^{2j+1} u) / λ = λ^{2j} u`
  have harg2 : ((lamC a) ^ (2 * j + 1) * u) / lamC a = (lamC a) ^ (2 * j) * u := by
    rw [div_eq_iff hne, pow_succ]
    ring
  rw [GlinOf, harg1, harg2]
  field_simp
  ring

end Work.EQ
