/-
# ZeroFreeTables — HBRepZero_red

The *real-real* case of HB's repeated-zero bound from **HB Table 4**: the entry
`(0.7, 1.724)` of the table is a `Lam0Bound` with `c = 1.724` whose first conjunct is
exactly `2 ≤ zeroMult χ₁ ρ₁ → 1.724 ≤ λ₁`.  Hence `HBTable4` alone implies the
repeated-zero bound in the real-real case (the remaining cases are covered by the
multiplicity count of HB Theorem 2; see `HBProps.HBRepZero`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Tables

open DirichletCharacter Complex
open scoped Classical BigOperators

open Work.LinnikContract

namespace Work.ZeroFreeTables

theorem mem_tableR_hbTable4_70 : ((70:ℝ)/100, (1724:ℝ)/1000) ∈ tableR hbTable4 := by
  norm_num [tableR, hbTable4]

/-- The multiplicity conjunct of `Lam0Bound χ₁ ρ₁ 1.724` for a real-real pair with
`λ₁ ≤ 0.7`, i.e. the real-real case of `HBRepZero`, from HB Table 4. -/
theorem hbRepZero_of_table4 (h : HBTable4) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → 2 ≤ zeroMult χ₁ ρ₁ →
      lamOf q ρ₁ ≤ 7/10 → 1724/1000 ≤ lamOf q ρ₁ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun q hq _ χ₁ ρ₁ hm h1 h2 hmult hlam => ?_⟩
  have hlam' : lamOf q ρ₁ ≤ ((70:ℝ)/100, (1724:ℝ)/1000).1 := by
    simp only [Prod.fst]
    norm_num at hlam ⊢
    linarith
  exact (lam0Bound_iff.mp (hN q hq χ₁ ρ₁ hm h1 h2 ((70:ℝ)/100, (1724:ℝ)/1000)
    mem_tableR_hbTable4_70 hlam')).1 hmult

end Work.ZeroFreeTables
