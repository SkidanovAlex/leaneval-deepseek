/-
# ZeroFreeTables/P9/Setup — elementary setup facts for the HB §9 assembly
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.API
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

open Work.LinnikContract

/-- `λ(ρ) ≥ 0` for a zero `ρ` of the working region. -/
theorem lamOf_nonneg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZ χ ρ) : 0 ≤ lamOf q ρ := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hne : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ ≠ 0 :=
    h.2.1
  have hχ : χ ≠ 1 := h.1
  have hprim' : χ.primitiveCharacter ≠ 1 := by
    intro hh
    refine hχ ?_
    have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hh, map_one] at h2
    exact h2.symm
  have hz : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hne
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hprim'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hz
  have hlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  rw [lamOf]
  exact mul_nonneg (by linarith [hstrip.2]) hlog

/-- `cond913` together with `0 ≤ λ₁ ≤ λ₀` bounds `α = a+λ₁` by the constant `a(Kond K+1)^{1/3}`. -/
theorem alpha_cube_le {a lam₁ lam₀ K : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hlam : lam₁ ≤ lam₀)
    (hcond : cond913 lam₁ lam₀ a K) :
    (a + lam₁) ^ 3 ≤ a ^ 3 * (Kond K + 1) := by
  have hApos : 0 < a + lam₁ := by linarith
  have hL0 : a + lam₁ ≤ a + lam₀ := by linarith
  have hA3 : 0 < (a + lam₁) ^ 3 := pow_pos hApos 3
  have hL03 : 0 < (a + lam₀) ^ 3 := pow_pos (by linarith : 0 < a + lam₀) 3
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  have hinv : 1 / (a + lam₀) ^ 3 ≤ 1 / (a + lam₁) ^ 3 :=
    one_div_le_one_div_of_le hA3 (pow_le_pow_left₀ (le_of_lt hApos) hL0 3)
  have h := hcond
  rw [cond913, ge_iff_le] at h
  have h2 : 1 / a ^ 3 ≤ (Kond K + 1) / (a + lam₁) ^ 3 := by
    have h3 : Kond K / (a + lam₁) ^ 3 + 1 / (a + lam₀) ^ 3
        ≤ (Kond K + 1) / (a + lam₁) ^ 3 := by
      have : (Kond K + 1) / (a + lam₁) ^ 3
          = Kond K / (a + lam₁) ^ 3 + 1 / (a + lam₁) ^ 3 := by ring
      linarith [hinv, this.le, this.ge]
    linarith
  rw [div_le_div_iff₀ ha3 hA3] at h2
  linarith [h2]

end Work.ZeroFreeTables.P9
