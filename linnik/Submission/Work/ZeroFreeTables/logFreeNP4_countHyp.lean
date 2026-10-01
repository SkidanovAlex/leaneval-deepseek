import Mathlib
import Submission.Work.ZeroDensity.LogFree.logFreeNPInstances
import Submission.Work.LinnikAreas.Setup

namespace Work.ZeroFreeTables

/-- The `(4+ε)`-form of the log-free non-principal zero-density count on `σ ≥ 3979/5000`.

This is instance I of the unified estimate `logFreeNP (3979/5000) 4` rewritten with the exponent
`(4+ε)(1-σ)`: since `σ ≤ 1` we have `0 ≤ 1-σ` and `4(1-σ) ≤ (4+ε)(1-σ)`, and the base `qT ≥ 2`
satisfies `1 ≤ qT`, so `Real.rpow_le_rpow_of_exponent_le` upgrades the estimate at no cost. -/
theorem logFreeNP4_countHyp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (3979 / 5000 : ℝ) ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((4 + ε) * (1 - σ)) := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
  have hmain := hh q hq σ T hσ hσ1 hT
  have hmain' : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      Work.LinnikAreas.zeroCountIn χ σ T) ≤ C * ((q : ℝ) * T) ^ (4 * (1 - σ)) := by
    simpa only [Work.ZeroDensity.LogFree.famCountNP, Work.ZeroDensity.zCount] using hmain
  refine le_trans hmain' ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  exact Real.rpow_le_rpow_of_exponent_le hbase (by nlinarith [hε, h0])

end Work.ZeroFreeTables
