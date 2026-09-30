import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ## The two interface predicates shared by N7's re-proof of the V-chain

`VKExpSumRestrictedN7` is node V1 (`Submission.Work.BMF.vk_exp_sum`) verbatim as a hypothesis (so
that V2 can be proved before V1 lands); `ZFVKN7` is node V3
(`Submission.Work.BMF.LFunction_zeroFree_VK`) verbatim as a hypothesis (so that V4 can be proved
before V3 lands).  Both are matched definitionally by the corresponding fleet declarations. -/

namespace Work.BMF

/-- **V1 (node `Work.BMF.vk_exp_sum`) as a hypothesis**, character for character: the Vinogradov
exponential-sum estimate in the restricted range `log t ≤ c (log N)^{7/6}` with the classical
saving `c/λ² · 1/log(λ+2)`, `λ = log t/log N`. -/
def VKExpSumRestrictedN7 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N t : ℝ), 2 ≤ N → N ≤ t →
    Real.log t ≤ c * Real.log N ^ (7 / 6 : ℝ) →
    ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ R : ℝ, N < R → R ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
        C * N ^ (1 - c * (Real.log N / Real.log t) ^ 2 /
          Real.log (Real.log t / Real.log N + 2))

/-- The *conclusion* of node V3 (`Work.BMF.LFunction_zeroFree_VK`) as a hypothesis: the
Vinogradov–Korobov shaped zero-free region for primitive characters mod `N`. -/
def ZFVKN7 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ σ t : ℝ, 3 ≤ |t| →
      1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end Work.BMF
