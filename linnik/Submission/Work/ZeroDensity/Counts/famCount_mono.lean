import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroDensity.Counts

open scoped Classical BigOperators

/-- Monotonicity of the family zero count in the two real variables: `famCount` is decreasing in `sigma` (a larger `sigma` restricts the rectangle `sigma <= Re rho <= 1`) and increasing in `T` (a larger `T` enlarges `|Im rho| <= T`), so for `sigma <= sigma'` and `T <= T'` one has `famCount q sigma' T <= famCount q sigma T'`. The per-character statement is also true and follows by the same argument: `zCount chi sigma' T <= zCount chi sigma T'`. Both directions are pointwise on the summand (the indicator of a smaller rectangle is at most the indicator of a larger one, and the coefficient `zeroMult chi rho : Nat` casts to a nonnegative real) and therefore need only the finite support of the summand of `zeroCountIn`, which is `Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box` (used with `finsum_le_finsum'`; compare `Work.LinnikAreas.FamilyZeroCountNonPrincipal`, line 99). No range hypotheses on `sigma`, `sigma'`, `T`, `T'` are needed. -/
theorem famCount_mono {q : ℕ} [NeZero q] {σ σ' T T' : ℝ} (hσ : σ ≤ σ') (hT : T ≤ T') :
    Work.ZeroDensity.famCount q σ' T ≤ Work.ZeroDensity.famCount q σ T' := by
  classical
  -- The per-character inequality: a larger `σ` and a smaller `T` shrink the rectangle.
  have key : ∀ χ : DirichletCharacter ℂ q,
      (∑ᶠ ρ : ℂ, if σ' ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      ≤ (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T'
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
    intro χ
    refine finsum_le_finsum' ?_ ?_ ?_
    · -- the summand with the smaller rectangle is finitely supported
      refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ' T).subset ?_
      intro ρ hρ
      simp only [Function.mem_support] at hρ
      have hc : σ' ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T := by
        by_contra hcon
        exact hρ (if_neg hcon)
      have hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
        have hz : (Work.LinnikContract.zeroMult χ ρ : ℝ) ≠ 0 := by
          rwa [if_pos hc] at hρ
        exact_mod_cast hz
      exact ⟨hzm, hc.1, hc.2.1, hc.2.2⟩
    · -- the summand with the larger rectangle is finitely supported as well
      refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ T').subset ?_
      intro ρ hρ
      simp only [Function.mem_support] at hρ
      have hd : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T' := by
        by_contra hcon
        exact hρ (if_neg hcon)
      have hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
        have hz : (Work.LinnikContract.zeroMult χ ρ : ℝ) ≠ 0 := by
          rwa [if_pos hd] at hρ
        exact_mod_cast hz
      exact ⟨hzm, hd.1, hd.2.1, hd.2.2⟩
    · -- termwise comparison of the two summands
      intro ρ
      show (if σ' ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T'
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      by_cases hc : σ' ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
      · rw [if_pos hc, if_pos ⟨le_trans hσ hc.1, hc.2.1, le_trans hc.2.2 hT⟩]
      · rw [if_neg hc]
        by_cases hd : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T'
        · rw [if_pos hd]; exact Nat.cast_nonneg _
        · rw [if_neg hd]
  simp only [Work.ZeroDensity.famCount, Work.ZeroDensity.zCount,
    Work.LinnikAreas.zeroCountIn]
  exact Finset.sum_le_sum fun χ _ => key χ

end Work.ZeroDensity.Counts
