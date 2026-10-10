import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.Genus.Defs
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.min_ordInf_le_ordInf_add
import Submission.Work.Genus.OrderInf.ordInf_polynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- **The valuation at infinity on `𝔽(t)` is `ℤᵐ⁰`-valued and has `ordInf` as its order
function.**  Concretely, take Mathlib's `RatFunc.inftyValuation M`, whose value on `x ≠ 0` is
`exp (x.intDegree)`; since `Work.Genus.ordInf x = -x.intDegree`, the two equivalences are
`WithZero.exp_le_exp` / `WithZero.exp_lt_exp` together with the convention `v 0 = 0`,
`ordInf 0 = 0`.  `TrivOn M` is `RatFunc.inftyValuation.C`.

This is the `M`-side input for `TrivOn`/`FifthPowerValued` statements of route V: the
`ℤᵐ⁰`-valuations of `𝔽(t)` trivial on `𝔽` are exactly the places of `ℙ¹`, and this produces the
place at infinity, with the sign convention of the handoff (`1 < v x` ⟺ `x` has a *pole* at
infinity, i.e. `ordInf x < 0`). -/
theorem valuation_ordInf {M : Type*} [Field M] :
    ∃ v : Valuation (RatFunc M) (WithZero (Multiplicative ℤ)),
      Work.MotV.TrivOn M v ∧
      (∀ x : RatFunc M, v x ≤ 1 ↔ 0 ≤ Work.Genus.ordInf x) ∧
      (∀ x : RatFunc M, 1 < v x ↔ Work.Genus.ordInf x < 0) := by
  classical
  refine ⟨RatFunc.inftyValuation M, ?_, ?_, ?_⟩
  · intro c hc
    rw [RatFunc.algebraMap_eq_C]
    exact RatFunc.inftyValuation.C (F := M) hc
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [RatFunc.inftyValuation_apply, RatFunc.InftyValuation.map_zero',
        Work.Genus.ordInf, RatFunc.intDegree_zero]
    · have hx' : RatFunc.inftyValuation M x = WithZero.exp (RatFunc.intDegree x) := by
        rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero M hx]
      simp only [hx', Work.Genus.ordInf, neg_nonneg]
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [RatFunc.inftyValuation_apply, RatFunc.InftyValuation.map_zero',
        Work.Genus.ordInf, RatFunc.intDegree_zero]
    · have hx' : RatFunc.inftyValuation M x = WithZero.exp (RatFunc.intDegree x) := by
        rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero M hx]
      simp only [hx', Work.Genus.ordInf]
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega

end Work.MotV5
