import Mathlib
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.testFn7_2

/-!
# ZeroFreeTables/HB8GlueDefs

`GlueInput` (audit `ENGINE_AUDIT_LEAD.md` §3.2): the §6 inequality of HB Lemma 6.3 in the shape
`HBTable2and3_of_pieces` consumes it.  It is stated here rather than in `HB8Defs.lean` because it
mentions the Table 2/3 scales `t23lams` (which covers both `t23rows` and `rowG`) and
HB Lemma 7.2's test function `tf72T`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- **The glue between `HBTable2and3` and the F-method (audit §3.2).**

Given a bound `Λ` on `λ(ρ')`, the zero `ρ' ≠ ρ₁` of `χ₁` of minimal `λ`, the §6 inequality
of HB Lemma 6.3 holds at `(λ(ρ'), λ₁)` for every scale `λ` of the Tables 2/3 engine. -/
def GlueInput : Prop :=
  ∀ Λ : ℝ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamOf q ρ₁ ≤ 2 / 5 →
    ∀ ρ' : ℂ, IsZ χ₁ ρ' → ρ' ≠ ρ₁ → lamOf q ρ' ≤ Λ →
    (∀ u : ℂ, IsZ χ₁ u → u ≠ ρ₁ → lamOf q ρ' ≤ lamOf q u) →
    ∀ lam ∈ t23lams, ∀ (hlam : 0 < lam),
      0 ≤ 2 * (tf72T lam hlam).F (-(lamOf q ρ')) - 2 * (tf72T lam hlam).F (lamOf q ρ₁ - lamOf q ρ')
        - (tf72T lam hlam).F 0 + (tf72T lam hlam).f 0 * (1 / 4 + 4 * (1 / 4000))

end Work.ZeroFreeTables
