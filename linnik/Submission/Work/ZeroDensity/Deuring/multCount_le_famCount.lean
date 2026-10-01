import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroDensity.Deuring

open scoped Classical BigOperators

/-- **The `λ`-count is dominated by the family zero count at height `1`.**

Every zero `ρ` of a completion `Λ(·,χ*)` counted by `multCount q t` — that is, `zeroMult χ ρ ≠ 0`,
`|Im ρ| ≤ 1` and `λ(ρ) = (1-Re ρ) log q ≤ t` — has `0 < Re ρ < 1` (`Work.LinnikAreas.zeroMult_re_pos`
and `Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one`) and `1 - t/log q ≤ Re ρ` (divide
`λ(ρ) ≤ t` by `log q > 0`), hence lies in the box
`max 0 (1 - t/log q) ≤ Re ρ ≤ 1`, `|Im ρ| ≤ 1` which defines `famCount q (max 0 (1-t/log q)) 1`.
Both sums are finitely supported (`Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box`), so the
comparison is termwise. -/
theorem multCount_le_famCount {q : ℕ} [NeZero q] (hq : 2 ≤ q) (t : ℝ) :
    Work.ZeroDensity.multCount q t ≤
      Work.ZeroDensity.famCount q (max 0 (1 - t / Real.log q)) 1 := by
  classical
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have key : ∀ χ : DirichletCharacter ℂ q,
      (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧
          Work.LinnikContract.lamOf q ρ ≤ t
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      ≤ (∑ᶠ ρ : ℂ, if max 0 (1 - t / Real.log (q : ℝ)) ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ 1
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
    intro χ
    refine finsum_le_finsum' ?_ ?_ ?_
    · -- the `λ`-count is finitely supported: it is contained in a compact box
      refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ
        (1 - t / Real.log (q : ℝ)) 1).subset ?_
      intro ρ hρ
      simp only [Function.mem_support] at hρ
      have hc : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧
          Work.LinnikContract.lamOf q ρ ≤ t := by
        by_contra hcon
        exact hρ (if_neg hcon)
      refine ⟨hc.1, ?_, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hc.1),
        hc.2.1⟩
      have h2 : 1 - ρ.re ≤ t / Real.log (q : ℝ) :=
        (le_div_iff₀ hlog).mpr (by simpa [Work.LinnikContract.lamOf] using hc.2.2)
      linarith
    · -- the zero-count is finitely supported as well
      refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ 0 1).subset ?_
      intro ρ hρ
      simp only [Function.mem_support] at hρ
      have hd : max 0 (1 - t / Real.log (q : ℝ)) ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ 1 := by
        by_contra hcon
        exact hρ (if_neg hcon)
      have hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
        have hz : (Work.LinnikContract.zeroMult χ ρ : ℝ) ≠ 0 := by
          rwa [if_pos hd] at hρ
        exact_mod_cast hz
      exact ⟨hzm, le_trans (le_max_left _ _) hd.1, hd.2.1, hd.2.2⟩
    · -- termwise comparison
      intro ρ
      show (if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧
          Work.LinnikContract.lamOf q ρ ≤ t
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ (if max 0 (1 - t / Real.log (q : ℝ)) ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ 1
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      by_cases hc : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧
          Work.LinnikContract.lamOf q ρ ≤ t
      · have hre0 : 0 < ρ.re := Work.LinnikAreas.zeroMult_re_pos χ hc.1
        have hre1 : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hc.1
        have hrel : 1 - t / Real.log (q : ℝ) ≤ ρ.re := by
          have h2 : 1 - ρ.re ≤ t / Real.log (q : ℝ) :=
            (le_div_iff₀ hlog).mpr (by simpa [Work.LinnikContract.lamOf] using hc.2.2)
          linarith
        rw [if_pos hc, if_pos ⟨max_le hre0.le hrel, le_of_lt hre1, hc.2.1⟩]
      · rw [if_neg hc]
        by_cases hd : max 0 (1 - t / Real.log (q : ℝ)) ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ 1
        · rw [if_pos hd]; exact Nat.cast_nonneg _
        · rw [if_neg hd]
  simp only [Work.ZeroDensity.multCount, Work.ZeroDensity.famCount, Work.ZeroDensity.zCount,
    Work.LinnikAreas.zeroCountIn]
  exact Finset.sum_le_sum fun χ _ => key χ

end Work.ZeroDensity.Deuring
