import Mathlib
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **Finite support of the height-truncated multiplicity weight.**  The function
`ρ ↦ (zeroMult χ ρ : ℝ)` restricted to zeros of bounded `λ(ρ) = lamOf q ρ ≤ t` and bounded height
`|Im ρ| log q ≤ T`, with the single pair `(χ, β₁)` excluded, has finite support.

Indeed, the only points where the function fails to vanish are zeros with
`1 - t / log q ≤ Re ρ`, `Re ρ < 1` and `|Im ρ| ≤ T / log q`, a subset of the compact box whose
zeros are finite by `boxMaxZeroAux.finite_zeroMult_box`. -/
theorem support_pairCountHeight_finite {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) {t T : ℝ} (χ : DirichletCharacter ℂ q) :
    (Function.support (fun ρ : ℂ =>
      if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ Work.LinnikContract.lamOf q ρ ≤ t
        ∧ |ρ.im| * Real.log q ≤ T ∧ ¬(χ = χ₁ ∧ ρ = β₁)
      then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)).Finite := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine (boxMaxZeroAux.finite_zeroMult_box χ (1 - t / Real.log q) (T / Real.log q)).subset ?_
  intro ρ hρ
  rw [Function.mem_support] at hρ
  by_cases hP : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ Work.LinnikContract.lamOf q ρ ≤ t
      ∧ |ρ.im| * Real.log q ≤ T ∧ ¬(χ = χ₁ ∧ ρ = β₁)
  · obtain ⟨hzm, hlam, him, -⟩ := hP
    refine ⟨hzm, ?_, le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ hzm), ?_⟩
    · have h : 1 - ρ.re ≤ t / Real.log q :=
        (le_div_iff₀ hlog).mpr (by simpa [Work.LinnikContract.lamOf] using hlam)
      linarith
    · exact (le_div_iff₀ hlog).mpr him
  · rw [if_neg hP] at hρ
    exact absurd rfl hρ

end Work.LinnikAreas
