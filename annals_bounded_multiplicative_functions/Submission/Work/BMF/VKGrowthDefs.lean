import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vinogradov–Korobov growth predicates near `σ = 1`
-/

namespace Work.BMF

noncomputable section

/-- **The Vinogradov–Korobov exponential-sum input** (the inner statement of
`Work.BMF.vk_exp_sum`). -/
def VKExpInput (C c : ℝ) : Prop :=
  0 < C ∧ 0 < c ∧ ∀ (N t : ℝ), 2 ≤ N → N ≤ t →
    Real.log t ≤ c * Real.log N ^ (7 / 6 : ℝ) →
    ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ R : ℝ, N < R → R ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
        C * N ^ (1 - c * (Real.log N / Real.log t) ^ 2 /
          Real.log (Real.log t / Real.log N + 2))

/-- **Growth of the Hurwitz zeta function in the VK strip.**  Uniform in `a ∈ [0,1]`, with the
pole term `a^{-σ}` allowed; the `a = 0` case is the Riemann zeta function. -/
def HurwitzGrowthVK : Prop :=
  ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ σ t : ℝ, 3 ≤ t →
      1 - c * Real.log (t + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * (a ^ (-σ) + Real.log (t + 3) ^ (6 / 7 : ℝ)))

end

end Work.BMF
