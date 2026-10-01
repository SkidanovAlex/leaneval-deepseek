import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.siegelZeroSimple_ldUpper
import Submission.Work.LinnikAreas.siegelZeroSimple_zeroSum
import Submission.Work.LinnikAreas.siegelZeroSimple_arith

/-!
# Simplicity of the exceptional (Siegel) zero — self-contained copy

`Work.LinnikAreas.siegelZeroSimple` is the same statement, but its module imports
`Submission.Work.LinnikAreas.area6`, which is (temporarily) not compiling because of unrelated
work in progress.  The proof below depends only on `SiegelBase` and the three analytic
sub-modules `siegelZeroSimple_ldUpper / _zeroSum / _arith`, so it can be built independently.
-/

open DirichletCharacter Complex
open scoped Classical

noncomputable section

set_option linter.unusedVariables false

namespace Work.LinnikAreas.DhCapped

open Work.LinnikAreas
open Work.LinnikContract

/-- The exceptional real zero of a real character is simple. -/
theorem siegelZeroSimple' : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ 1 / 100 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) = 1 := by
  obtain ⟨C, hC⟩ := siegelZeroSimple_ldUpper
  obtain ⟨q0, hq0⟩ := siegelZeroSimple_arith C
  refine ⟨max q0 2, ?_⟩
  intro q hq hne χ₁ β₁ hχ1 hsq hβ1 hz hlam
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hq0le : q0 ≤ q := le_trans (le_max_left _ _) hq
  have hq1 : 1 < q := by omega
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hlogq_ne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogq_pos
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχ'ne : χ₁.primitiveCharacter ≠ 1 := Siegel.primitive_ne_one hχ1
  have hχ'sq : χ₁.primitiveCharacter ^ 2 = 1 := Siegel.primitive_sq_one hsq
  have hχ'prim : (χ₁.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hz' : completedLFunction χ₁.primitiveCharacter (β₁ : ℂ) = 0 :=
    Siegel.completedLFunction_eq_zero_of_zeroMult χ₁ hz
  have hβ0 : 0 < β₁ := Siegel.re_mem_Ioo hχ1 hβ1 hz
  have hNne : χ₁.conductor ≠ 0 := χ₁.conductor_ne_zero
  have hN2 : 2 ≤ χ₁.conductor := by
    by_contra hcon
    have hN1 : χ₁.conductor = 1 := by omega
    exact hχ'ne (DirichletCharacter.level_one' (χ := χ₁.primitiveCharacter) hN1)
  have hNdvd : χ₁.conductor ∣ q := χ₁.conductor_dvd_level
  have hNle : χ₁.conductor ≤ q := Nat.le_of_dvd (by omega) hNdvd
  have hlam_eq : lamOf q (β₁ : ℂ) = (1 - β₁) * Real.log (q : ℝ) := by
    simp [Work.LinnikContract.lamOf]
  have hlam_pos : 0 < lamOf q (β₁ : ℂ) := by
    rw [hlam_eq]; exact mul_pos (by linarith) hlogq_pos
  have hbeta_eq : β₁ = 1 - lamOf q (β₁ : ℂ) / Real.log (q : ℝ) := by
    rw [hlam_eq]; field_simp; ring
  set σ : ℝ := 1 + Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ) with hσdef
  have hσ_gt1 : 1 < σ := by
    rw [hσdef]
    have h1 : 0 < Real.sqrt (lamOf q (β₁ : ℂ)) := Real.sqrt_pos.mpr hlam_pos
    have h2 : 0 < Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ) := div_pos h1 hlogq_pos
    linarith
  have hsqrt_le : Real.sqrt (lamOf q (β₁ : ℂ)) ≤ 1 / 10 := by
    have h := Real.sqrt_le_sqrt hlam
    rwa [show Real.sqrt (1 / 100 : ℝ) = 1 / 10 by
      rw [show (1:ℝ)/100 = (1/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hlogq_ge : (2 : ℝ) / 5 ≤ Real.log (q : ℝ) := by
    have h1 : (2 : ℝ) / 5 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact le_trans h1 (Real.log_le_log (by norm_num) (by exact_mod_cast hq2))
  have hσ_le : σ ≤ 5 / 4 := by
    have hle : Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hlogq_pos]; nlinarith [hsqrt_le, hlogq_ge]
    rw [hσdef]; linarith
  have hB : (logDeriv (completedLFunction χ₁.primitiveCharacter) (σ : ℂ)).re ≤ 1 / (σ - 1) + C :=
    hC χ₁.conductor χ₁.primitiveCharacter hχ'ne σ hσ_gt1 hσ_le
  have hsum := siegelZeroSimple_zeroSum χ₁.conductor χ₁.primitiveCharacter hχ'ne hχ'prim β₁ σ
    (1 / (σ - 1) + C) hβ0 hβ1 hz' hσ_gt1 hσ_le hB
  have hm_eq : ((zeroMult χ₁ (β₁ : ℂ) : ℕ) : ℝ) =
      ((analyticOrderNatAt (completedLFunction χ₁.primitiveCharacter) (β₁ : ℂ)) : ℝ) := by
    simp only [Work.LinnikContract.zeroMult]
  have hspos : 0 < σ - β₁ := by linarith
  have hmul : (zeroMult χ₁ (β₁ : ℂ) : ℝ) ≤
      (1 / (σ - 1) + C + Real.log (χ₁.conductor : ℝ) + Real.log 2 / 2 + 3 / 2) * (σ - β₁) := by
    rw [← hm_eq] at hsum
    have h2 := mul_le_mul_of_nonneg_right hsum hspos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hspos)] at h2
    linarith [h2]
  have harith := hq0 q hq0le (χ₁.conductor : ℝ) (lamOf q (β₁ : ℂ))
    (by exact_mod_cast hq2) (by exact_mod_cast hN2) (by exact_mod_cast hNle) hlam_pos hlam
  have e1 : 1 / (σ - 1) = 1 / ((1 + Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ)) - 1) := by
    rw [hσdef]
  have e2 : σ - β₁ = (1 + Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ)) -
      (1 - lamOf q (β₁ : ℂ) / Real.log (q : ℝ)) := by
    rw [hσdef]; linarith only [hbeta_eq]
  have hlt : (zeroMult χ₁ (β₁ : ℂ) : ℝ) < 2 := by
    have h3 : (1 / (σ - 1) + C + Real.log (χ₁.conductor : ℝ) + Real.log 2 / 2 + 3 / 2) *
        (σ - β₁) < 2 := by
      rw [e1, e2]
      exact harith
    linarith [hmul, h3]
  have hge : 1 ≤ zeroMult χ₁ (β₁ : ℂ) := Nat.one_le_iff_ne_zero.mpr hz
  have h2 : zeroMult χ₁ (β₁ : ℂ) < 2 := by exact_mod_cast hlt
  omega

end Work.LinnikAreas.DhCapped
