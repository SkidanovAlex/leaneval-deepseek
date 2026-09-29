import Mathlib
import Submission.Work.TMC7Core.Scale.lyapAvg_lipschitz
import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Scale

set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open Work.TMC7Core
open Work.TMC7Core.Cocycle
open Work.TMC7Core.Lyap

/-- `Scale.lyapAvg_lipschitz` with its explicit constant `lipK` exposed (its proof already
refines with `⟨lipK lam N R, …⟩`, so this is the same estimate, just not hidden behind an
`∃ K`). Needed for the *crude* transfer in Case I of `p_bj_of_dichotomy`, where the scale
`N₀` is not fixed in advance (it satisfies `N₀ ≤ W q`), so the constant must be bounded
explicitly by `lipK lam (2*N₀) R ≤ 2 lipL lam exp (Γ * 2N₀)` (S0, `Scale.lipK_le_exp`).
Should live in `namespace Work.TMC7Core.Scale`. -/
theorem lyapAvg_lipschitz_lipK (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (R : ℝ) (hR : 0 < R) :
    ∀ α E α' E' : ℝ, |α| ≤ R → |E| ≤ R → |α'| ≤ R → |E'| ≤ R →
      |Work.TMC7Core.lyapAvg α lam (E : ℂ) N - Work.TMC7Core.lyapAvg α' lam (E' : ℂ) N|
        ≤ Work.TMC7Core.Scale.lipK lam N R * (|α - α'| + |E - E'|) := by
  intro α E α' E' hα hE hα' hE'
  set e : ℝ := |α - α'| + |E - E'| with hedef
  have he0 : 0 ≤ e := by positivity
  have hNpos : (0:ℝ) < (N:ℝ) := by
    exact_mod_cast (show 0 < N from lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hpt : ∀ x : ℝ,
      |Real.log (frob (iterC α lam (E:ℂ) N x)) - Real.log (frob (iterC α' lam (E':ℂ) N x))|
        ≤ lipC lam N R * e := by
    intro x
    rw [hedef]
    exact log_frob_iterC_diff_le lam R N hN α E α' E' x hE hE'
  have hcont1 : Continuous (fun x : ℝ => Real.log (frob (iterC α lam (E:ℂ) N x))) :=
    Continuous.log (continuous_frob_iterC α lam (E:ℂ) N)
      (fun x => ne_of_gt (frob_iterC_pos α lam (E:ℂ) N x))
  have hcont2 : Continuous (fun x : ℝ => Real.log (frob (iterC α' lam (E':ℂ) N x))) :=
    Continuous.log (continuous_frob_iterC α' lam (E':ℂ) N)
      (fun x => ne_of_gt (frob_iterC_pos α' lam (E':ℂ) N x))
  have hI1 : IntervalIntegrable (fun x : ℝ => Real.log (frob (iterC α lam (E:ℂ) N x)))
      volume (0:ℝ) 1 := intervalIntegrable_log_frob α lam (E:ℂ) N
  have hI2 : IntervalIntegrable (fun x : ℝ => Real.log (frob (iterC α' lam (E':ℂ) N x)))
      volume (0:ℝ) 1 := intervalIntegrable_log_frob α' lam (E':ℂ) N
  have hsub : (∫ x in (0:ℝ)..1, (Real.log (frob (iterC α lam (E:ℂ) N x))
        - Real.log (frob (iterC α' lam (E':ℂ) N x))))
      = (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam (E:ℂ) N x)))
        - (∫ x in (0:ℝ)..1, Real.log (frob (iterC α' lam (E':ℂ) N x))) :=
    intervalIntegral.integral_sub hI1 hI2
  have hlyap : lyapAvg α lam (E:ℂ) N - lyapAvg α' lam (E':ℂ) N
      = (∫ x in (0:ℝ)..1, (Real.log (frob (iterC α lam (E:ℂ) N x))
          - Real.log (frob (iterC α' lam (E':ℂ) N x)))) / (N:ℝ) := by
    rw [lyapAvg, lyapAvg, div_sub_div_same, ← hsub]
  have hmain : |lyapAvg α lam (E:ℂ) N - lyapAvg α' lam (E':ℂ) N|
      ≤ (∫ x in (0:ℝ)..1, |Real.log (frob (iterC α lam (E:ℂ) N x))
          - Real.log (frob (iterC α' lam (E':ℂ) N x))|) / (N:ℝ) := by
    rw [hlyap, abs_div, abs_of_pos hNpos]
    apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
    exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hmono : (∫ x in (0:ℝ)..1, |Real.log (frob (iterC α lam (E:ℂ) N x))
          - Real.log (frob (iterC α' lam (E':ℂ) N x))|)
      ≤ ∫ x in (0:ℝ)..1, (lipC lam N R * e) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
    · exact ((hcont1.sub hcont2).abs).intervalIntegrable 0 1
    · intro x _; exact hpt x
  have hintc : (∫ x in (0:ℝ)..1, (lipC lam N R * e)) = lipC lam N R * e := by
    rw [intervalIntegral.integral_const]; simp
  have hC0 : 0 ≤ lipC lam N R := by
    rw [lipC, lipD, lipL]
    apply mul_nonneg
    · exact mul_nonneg (by positivity) (pow_nonneg (le_trans zero_le_one (lipM_ge_one lam R)) N)
    · exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by positivity)
  calc |lyapAvg α lam (E:ℂ) N - lyapAvg α' lam (E':ℂ) N|
      ≤ (∫ x in (0:ℝ)..1, |Real.log (frob (iterC α lam (E:ℂ) N x))
          - Real.log (frob (iterC α' lam (E':ℂ) N x))|) / (N:ℝ) := hmain
    _ ≤ (∫ x in (0:ℝ)..1, (lipC lam N R * e)) / (N:ℝ) :=
          div_le_div_of_nonneg_right hmono (le_of_lt hNpos)
    _ = (lipC lam N R * e) / (N:ℝ) := by rw [hintc]
    _ ≤ lipK lam N R * e := by
          rw [lipK]
          have h1 : (lipC lam N R * e) / (N:ℝ) ≤ lipC lam N R * e := by
            rw [div_le_iff₀ hNpos]
            simpa using mul_le_mul_of_nonneg_left hN1 (mul_nonneg hC0 he0)
          have h2 : lipC lam N R * e ≤ max 1 (lipC lam N R) * e :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) he0
          linarith

end Work.TMC7Core.Scale
