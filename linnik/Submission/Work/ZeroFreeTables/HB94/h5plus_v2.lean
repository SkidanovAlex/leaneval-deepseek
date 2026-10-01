import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.HB94.h5plus_cases
import Submission.Work.ZeroFreeTables.HB94.h5CaseA_v2
import Submission.Work.ZeroFreeTables.HB94.h5CaseB_six
import Submission.Work.ZeroFreeTables.HB94.L52supply
import Submission.Work.ZeroFreeTables.HB94.L52supply18
import Submission.Work.ZeroFreeTables.HB94.L52supply_pow
import Submission.Work.ZeroFreeTables.HB94.Lam2GeWide
import Submission.Work.ZeroFreeTables.HB94.Lam0Ge
import Submission.Work.LinnikAreas.DhCapped.L52Hyp_mono

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.HB94

open Work.LinnikContract

/-!
# HB Lemma 9.5, `h ≥ 5` case — final assembly

`HBTheorem1_complex_h5plus` (`∃ q₀, ∀ q ≥ q₀, ∀ χ₁ ρ₁, IsMin1WideAt 10 χ₁ ρ₁ →
5 ≤ orderOf χ₁ → 348/1000 ≤ lamOf q ρ₁`) is proved here by the case split of
`h5plus_cases.h5plus_of_cases`:

* **Case A** (`h5CaseA_v2`): every power `χ₁ᵏ` (`1 ≤ k ≤ 4`) admits the `1/8` supply — either
  because `orderOf (χ₁ᵏ) ≤ log(conductor)` (`L52supply18`) or because `(χ₁ᵏ)^60 = 1`
  (`L52supply_pow`; in particular for order `5`, where `5 ∣ 60`).  The `(9.16)` combination at
  `λ* = λ₁` then gives a contradiction;
* **Case B** (`h5CaseB_six`): otherwise some power fails both disjuncts, so `orderOf χ₁ ∤ 60` and
  hence (with `5 ≤ orderOf χ₁`) `6 ≤ orderOf χ₁`; the `1/6` supply `L52supply16`, the
  second-minimum bound `λ₂ ≥ λ₁ + 0.472` (`Lam2GeWide`) and the repulsion `λ₀ ≥ 0.82`
  (`Lam0Ge`, HB Table 8) then contradict `λ₁ ≤ 0.348`.
-/

/-- **HB Lemma 9.5, `h ≥ 5` case.** -/
theorem h5plus_v2 : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → 5 ≤ orderOf χ₁ →
      (348:ℝ)/1000 ≤ lamOf q ρ₁ := by
  -- the three supplies
  obtain ⟨δ₁₆, hδ₁₆0, hδ₁₆1, q₁₆, h16raw⟩ := L52supply16
  obtain ⟨N₁₈, δ₁₈, hδ₁₈0, hδ₁₈1, h18raw⟩ := L52supply18
  obtain ⟨δ₆₀, hδ₆₀0, hδ₆₀1, q₆₀, h60raw⟩ := L52supply_pow
  have h16 : ∀ q : ℕ, q₁₆ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000) δ₁₆ :=
    fun q hq _ χ _ hχ => L52Hyp_mono_eps χ (h16raw q hq χ hχ) (by norm_num)
  -- the disjunctive `1/8` supply: `order ≤ log(conductor)` or `χ^60 = 1`
  set δ₈ : ℝ := min δ₁₈ δ₆₀ with hδ₈def
  have hδ₈0 : 0 < δ₈ := lt_min hδ₁₈0 hδ₆₀0
  have hδ₈1 : δ₈ < 1 := lt_of_le_of_lt (min_le_left _ _) hδ₁₈1
  have hL8 : ∀ q : ℕ, max N₁₈ q₆₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ((orderOf χ : ℝ) ≤ Real.log ((χ.conductor : ℕ) : ℝ) ∨ χ ^ 60 = 1) →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000) δ₈ := by
    intro q hq _inst χ _instc hχ hdisj
    have hN : N₁₈ ≤ q := le_trans (le_max_left _ _) hq
    have hq6 : q₆₀ ≤ q := le_trans (le_max_right _ _) hq
    rcases hdisj with hcond | hpow
    · exact L52Hyp_mono_eps χ
        (Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_left _ _) (h18raw q hN χ hχ hcond))
        (by norm_num)
    · exact L52Hyp_mono_eps χ
        (Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_right _ _) (h60raw q hq6 χ hχ hpow))
        (by norm_num)
  -- the two cases and the assembly
  exact h5plus_of_cases
    (h5CaseA_v2 δ₈ hδ₈0 hδ₈1 (max N₁₈ q₆₀) hL8)
    (h5CaseB_six δ₁₆ hδ₁₆0 hδ₁₆1 q₁₆ h16 Lam0Ge (Lam2GeWide δ₁₆ hδ₁₆0 hδ₁₆1 q₁₆ h16))

end Work.ZeroFreeTables.HB94
