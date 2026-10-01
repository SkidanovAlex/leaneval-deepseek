import Mathlib
import Submission.Work.LinnikAreas.Sieve.Defs
import Submission.Work.LinnikAreas.charValTri
import Submission.Work.Sieve.aFun_basics

/-!
# `a(n) = Σ_{d | n} χ₁(d)` is non-negative and at most the number of divisors

For a real character `χ₁` (`χ₁² = 1`, so `χ₁` takes only the values `0, ±1`), Graham's function
`aFun χ₁ n = Σ_{d | n} (χ₁ d).re` satisfies `0 ≤ a(n) ≤ τ(n) = #(n.divisors)`.

Non-negativity is the deep half (multiplicativity plus the prime-power geometric sum) and is
`Work.Sieve.aFun_basics`; the upper bound is termwise: every summand `(χ₁ d).re` is `0`, `1` or
`-1` (`Work.LinnikAreas.charValTri`), hence `≤ 1`.
-/

open scoped BigOperators
open DirichletCharacter

namespace Work.Sieve

theorem aFun_nonneg_le_card {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (n : ℕ) :
    0 ≤ Work.LinnikAreas.Sieve.aFun χ₁ n ∧ Work.LinnikAreas.Sieve.aFun χ₁ n ≤ (n.divisors.card : ℝ) := by
  refine ⟨(aFun_basics χ₁ hreal).2.1 n, ?_⟩
  unfold Work.LinnikAreas.Sieve.aFun
  calc ∑ d ∈ n.divisors, (χ₁ (d : ZMod q)).re
      ≤ ∑ _d ∈ n.divisors, (1 : ℝ) :=
        Finset.sum_le_sum (fun d _ => by
          obtain h | h | h := (Work.LinnikAreas.charValTri χ₁ hreal (d : ZMod q)).1
          · rw [h]; norm_num
          · rw [h]; norm_num
          · rw [h]; norm_num)
    _ = (n.divisors.card : ℝ) := by simp

end Work.Sieve
