import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_core.fp_base
import Submission.Work.BMF.mr_core.fp_qf_sq
import Submission.Work.BMF.mr_core.fp_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-!
# `Work.BMF.mr_core.fineParams_le`

All the "fine-parameter" inequalities of the Matomäki–Radziwiłł core hold for all sufficiently
large `Y`.  Writing `x = log Y`, the fine parameters are

* `P_f = exp (384 log x)`, `log Q_f = (x^{1/8}/ε) · 384 log x`, `K_f = x^{1/4}/ε`,

so the assertions are elementary statements about `x → ∞`:

* `2 ≤ P_f`, `3 ≤ K_f`, `P_f ≤ Q_f`, `Q_f^2 ≤ Y`,
* `(K_f+1)^4 (log (Q_f/P_f) + 1)^2 ≤ (log Y)^{5/2} (log log Y)^2`,
* and the two exponent inequalities, which are *equalities* because
  `a ^ t = exp (t · log a)` and `log Q_f`, `log P_f` are explicit.

The three elementary "eventually" bounds are proved in `fp_base`, `fp_qf_sq`, `fp_prod`; here we
take the maximum of their thresholds and package the result in the form needed downstream.
-/

/-- The fine parameters of the Matomäki–Radziwiłł core satisfy, for all sufficiently large `Y`,
the whole list of size and growth conditions used in the critical regime. -/
theorem fineParams_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      Real.exp 1 ≤ Y ∧
      1 ≤ Real.log Y ∧
      1 ≤ Real.log (Real.log Y) ∧
      2 ≤ Work.BMF.mrCore.Pf Y ∧
      3 ≤ Work.BMF.mrCore.Kf ε Y ∧
      Work.BMF.mrCore.Pf Y ≤ Work.BMF.mrCore.Qf ε Y ∧
      (Work.BMF.mrCore.Qf ε Y) ^ 2 ≤ Y ∧
      (Work.BMF.mrCore.Kf ε Y + 1) ^ 4 *
        (Real.log (Work.BMF.mrCore.Qf ε Y / Work.BMF.mrCore.Pf Y) + 1) ^ 2
        ≤ (Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ 2 ∧
      (Work.BMF.mrCore.Qf ε Y) ^ (1 - 2 * Work.BMF.mrCore.alphaF) ≤
        Real.exp (((1 - 2 * Work.BMF.mrCore.alphaF) * 384 / ε) *
          (Real.log Y) ^ ((1 : ℝ) / 8) * Real.log (Real.log Y)) ∧
      (Work.BMF.mrCore.Pf Y) ^ (-(2 * Work.BMF.mrCore.alphaF)) ≤
        Real.exp (-(768 * Work.BMF.mrCore.alphaF) * Real.log (Real.log Y)) := by
  obtain ⟨L₁, h₁⟩ := fp_base ε hε hε1
  obtain ⟨L₂, h₂⟩ := fp_qf_sq ε hε hε1
  obtain ⟨L₃, h₃⟩ := fp_prod ε hε hε1
  set M : ℝ := max 100 (max L₁ (max L₂ L₃)) with hM
  have hM100 : (100 : ℝ) ≤ M := by rw [hM]; exact le_max_left _ _
  have hML₁ : L₁ ≤ M := by
    rw [hM]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hML₂ : L₂ ≤ M := by
    rw [hM]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hML₃ : L₃ ≤ M := by
    rw [hM]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨Real.exp M, Real.one_le_exp (le_trans (by norm_num : (0 : ℝ) ≤ 100) hM100), ?_⟩
  intro Y hY
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos M) hY
  have hx : M ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos M) hY
    rwa [Real.log_exp] at h
  have h100 : (100 : ℝ) ≤ Real.log Y := le_trans hM100 hx
  have HP := h₁ (Real.log Y) (le_trans hML₁ hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc Real.exp 1 ≤ Real.exp (Real.log Y) := Real.exp_le_exp.mpr (le_trans (by norm_num) h100)
      _ = Y := Real.exp_log hYpos
  · exact le_trans (by norm_num : (1 : ℝ) ≤ 100) h100
  · exact HP.2.1
  · simpa [Work.BMF.mrCore.Pf, Work.BMF.mrCore.logPf] using HP.2.2.2.1
  · simpa [Work.BMF.mrCore.Kf] using HP.2.2.2.2.1
  · simpa [Work.BMF.mrCore.Pf, Work.BMF.mrCore.logPf, Work.BMF.mrCore.Qf, Work.BMF.mrCore.logQf,
      Work.BMF.mrCore.Af] using HP.2.2.2.2.2
  · simpa [Work.BMF.mrCore.Qf, Work.BMF.mrCore.logQf, Work.BMF.mrCore.Af, Work.BMF.mrCore.logPf,
      Real.exp_log hYpos] using h₂ (Real.log Y) (le_trans hML₂ hx)
  · simpa [Work.BMF.mrCore.Pf, Work.BMF.mrCore.logPf, Work.BMF.mrCore.Qf, Work.BMF.mrCore.logQf,
      Work.BMF.mrCore.Af, Work.BMF.mrCore.Kf] using h₃ (Real.log Y) (le_trans hML₃ hx)
  · have hQf : Work.BMF.mrCore.Qf ε Y = Real.exp (Work.BMF.mrCore.logQf ε Y) := rfl
    rw [hQf, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    apply Real.exp_le_exp.mpr
    have key : Work.BMF.mrCore.logQf ε Y * (1 - 2 * Work.BMF.mrCore.alphaF)
        = (1 - 2 * Work.BMF.mrCore.alphaF) * 384 / ε * Real.log Y ^ (1 / 8 : ℝ) *
          Real.log (Real.log Y) := by
      simp only [Work.BMF.mrCore.logQf, Work.BMF.mrCore.Af, Work.BMF.mrCore.logPf]
      field_simp
    linarith [le_of_eq key]
  · have hPf : Work.BMF.mrCore.Pf Y = Real.exp (Work.BMF.mrCore.logPf Y) := rfl
    rw [hPf, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    apply Real.exp_le_exp.mpr
    have key : Work.BMF.mrCore.logPf Y * (-(2 * Work.BMF.mrCore.alphaF))
        = -(768 * Work.BMF.mrCore.alphaF) * Real.log (Real.log Y) := by
      simp only [Work.BMF.mrCore.logPf, Work.BMF.mrCore.alphaF, Work.BMF.mrCore.etaF]
      ring
    linarith [le_of_eq key]

end Work.BMF.mr_core
