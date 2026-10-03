import Mathlib
import Submission.Work.ORLyndon.powDefs

namespace Work.ORLyndon

/-- The level of the class of the letter `t` is `1`: the level map `levelOf` sends the generator
`t` to its `t`-exponent sum, which is `1`. -/
theorem levelOf_presentRho_of_eq {α : Type*} [DecidableEq α] (t : α) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) :
    Work.ORLyndon.levelOf t r u l hpow hσ (Work.ORLyndon.presentRho r (FreeGroup.of t)) =
      Multiplicative.ofAdd (1 : ℤ) := by
  rw [Work.ORLyndon.presentRho_of, Work.ORLyndon.levelOf_of, Work.OROneRel.sigma,
    FreeGroup.lift_apply_of]
  simp

theorem levelOf_zpow_presentRho_t {α : Type*} [DecidableEq α] (t : α) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (j : ℤ) :
    Work.ORLyndon.levelOf t r u l hpow hσ
      ((Work.ORLyndon.presentRho r (FreeGroup.of t)) ^ j) = Multiplicative.ofAdd j := by
  rw [map_zpow, levelOf_presentRho_of_eq t r u l hpow hσ, ← ofAdd_zsmul]
  simp

end Work.ORLyndon
