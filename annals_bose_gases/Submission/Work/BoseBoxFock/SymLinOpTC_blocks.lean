import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.SymBlocks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SymLinOpTC_blocks`

The linear row `linOpTC` of the spectator form `KzOpC` is, by definition,

    linOpTC g E = (ρ z Ŵ₁ω(0)) • Σ_{s ∈ excited Mode} χ̂²(s) • (a_s† + a_s),

i.e. the weighted sum of the creation and annihilation `χ̂²`-blocks
`BchiSqC g E = BchiC (excited Mode) E.hatChiSq 1 g` and
`BchiSqA g E = BchiA (excited Mode) E.hatChiSq 1 g`.  This file records that
splitting with the block vocabulary of `SymBlocks`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The linear row `linOpTC` splits into the two `χ̂²`-blocks `BchiSqC`, `BchiSqA`. -/
theorem SymLinOpTC_blocks {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Work.BoseBoxFock.linOpTC g E =
      (((E.rho * E.z * E.W1omega0 : ℝ)) : ℂ)
        • (Work.BoseBoxFock.BchiSqC g E + Work.BoseBoxFock.BchiSqA g E) := by
  rw [linOpTC, BchiSqC, BchiSqA, BchiC, BchiA]
  simp only [one_mul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_add]

end Work.BoseBoxFock
