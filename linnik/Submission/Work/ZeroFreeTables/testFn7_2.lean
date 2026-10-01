import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HB4_1
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.tf72Fc_imag_re_nonneg
import Submission.Work.ZeroFreeTables.tf72Fc_differentiableOn
import Submission.Work.ZeroFreeTables.tf72Fc_continuousOn
import Submission.Work.ZeroFreeTables.tf72Fc_decay
import Submission.Work.ZeroFreeTables.tf72Fc_zero_re
import Submission.Work.ZeroFreeTables.tf72Fc_neglam_re

namespace Work.ZeroFreeTables

noncomputable section

/-- HB Lemma 4.1 applied to the Laplace transform of HB Lemma 7.2's test function:
`Re (F z) ≥ 0` throughout `Re z ≥ 0` (HB's Condition 2). -/
theorem tf72Fc_re_nonneg (lam : ℝ) (hlam : 0 < lam) :
    ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (tf72Fc lam z).re := by
  have hbd : ∀ y : ℝ,
      (tf72Fc lam ((y : ℂ) * Complex.I)).re ≥ ‖(fun _ : ℂ => (0:ℂ)) ((y : ℂ) * Complex.I)‖ :=
    fun y => by simpa using tf72Fc_imag_re_nonneg lam hlam y
  have hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖tf72Fc lam z‖ < ε ∧ ‖(fun _ : ℂ => (0:ℂ)) z‖ < ε := fun ε hε => by
    obtain ⟨R, hRpos, hR⟩ := tf72Fc_decay lam hlam ε hε
    exact ⟨R, hRpos, fun w hw hRw => ⟨hR w hw hRw, by simpa using hε⟩⟩
  simpa using hb_lemma4_1 (F1 := tf72Fc lam) (F2 := fun _ : ℂ => (0:ℂ))
    (tf72Fc_differentiableOn lam hlam)
    (differentiableOn_const (0:ℂ))
    (tf72Fc_continuousOn lam hlam)
    continuousOn_const hbd hdec

/-- HB Lemma 7.2's optimal test function, as an element of HB's class of test
functions satisfying Conditions 1 and 2. -/
def tf72T (lam : ℝ) (hlam : 0 < lam) : TestFn where
  x₀ := 2 / lam
  f := tf72f lam
  Fc := tf72Fc lam
  x₀_pos := by positivity
  f0_pos := by rw [tf72f_at_zero lam hlam]; positivity
  f_nonneg := tf72f_nonneg lam hlam
  f_cont := tf72f_cont lam hlam
  f_diff := tf72f_diff lam hlam
  f_bound := tf72f_bound lam hlam
  f_supp := tf72f_supp lam hlam
  Fc_spec := fun z => rfl
  Fc_re_nonneg := tf72Fc_re_nonneg lam hlam

theorem testFn7_2 (lam : ℝ) (hlam : 0 < lam) :
    ∃ T : TestFn, T.x₀ = 2 / lam ∧ T.f 0 = 16 * lam / 15 ∧ T.F 0 = 8 / 9 ∧ T.F (-lam) = 8 / 5 := by
  refine ⟨tf72T lam hlam, rfl, tf72f_at_zero lam hlam, ?_, ?_⟩
  · show (tf72Fc lam ((0:ℝ) : ℂ)).re = 8 / 9
    rw [show ((0:ℝ) : ℂ) = 0 from by norm_num]
    exact tf72Fc_zero_re lam hlam
  · show (tf72Fc lam (((-lam : ℝ)) : ℂ)).re = 8 / 5
    exact tf72Fc_neglam_re lam hlam

end
end Work.ZeroFreeTables
