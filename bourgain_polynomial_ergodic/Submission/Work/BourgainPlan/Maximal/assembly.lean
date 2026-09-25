import Mathlib
import Submission.Work.BourgainPlan.Maximal.foundations
import Submission.Work.BourgainPlan.Maximal.kernel_l2

/-!
# Final wiring of the maximal statement

The whole `ℓ²` half of `Submission.BourgainPlan.MaximalStatement` is proved
(`Work.BourgainPlan.Maximal.L2Statement_of_kernel_l2`, axiom-clean), and `p > 2` follows from
`p = 2` by Marcinkiewicz interpolation (`Work.BourgainPlan.Maximal.lp_gt_two_of_l2`).  Hence
`MaximalStatement` is now equivalent to its `1 < p < 2` half, `SubTwoStatement`
(Bourgain 1989, §7).  Once that half is proved, the assignment's target is `one line` away.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Submission.BourgainPlan (NonnegOnNat discAvg)

/-- **`MaximalStatement` from its `1 < p < 2` half alone** (the `ℓ²` half is proved). -/
theorem maximal_statement_of_subtwo (hsub : SubTwoStatement) :
    Submission.BourgainPlan.MaximalStatement :=
  maximal_statement_of_l2_and_subtwo L2Statement_of_kernel_l2 hsub

/-- **The `p ≥ 2` half of `Submission.BourgainPlan.MaximalStatement`, completely proved** for
every `P : ℤ[X]` nonnegative on `ℕ`: the `ℓ²` bound `L2Statement_of_kernel_l2` plus Marcinkiewicz
interpolation `lp_gt_two_of_l2`.  Together with `Submission.ergodic_polynomial_maximal` this gives
the `L^p` (`p ≥ 2`) maximal ergodic inequality for polynomial averages, and it is the maximal-input
needed by the Banach-principle half of the challenge theorem for `p ≥ 2`. -/
theorem maximal_statement_ge_two (p : ℝ) (hp : 2 ≤ p) :
    ∀ P : Polynomial ℤ, NonnegOnNat P → ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
        ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂Measure.count
          ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count := by
  intro P hP
  rcases lt_or_eq_of_le hp with hgt | heq
  · obtain ⟨C, hCpos, hb⟩ := L2Statement_of_kernel_l2 P hP
    obtain ⟨C', hC'pos, hb'⟩ := lp_gt_two_of_l2 P hCpos hb hgt
    exact ⟨C', hC'pos.le, hb'⟩
  · subst heq
    obtain ⟨C, hCpos, hb⟩ := L2Statement_of_kernel_l2 P hP
    refine ⟨C, hCpos.le, fun g hg => ?_⟩
    rw [Real.rpow_ofNat]
    exact hb g hg

end Work.BourgainPlan.Maximal
