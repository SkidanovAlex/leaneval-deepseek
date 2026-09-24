import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.cbar_integral_le

set_option linter.unusedVariables false

namespace Work.NumberTheory.Chen.BTermCount

open MeasureTheory intervalIntegral

/-- The BJS integrand `β ↦ log (2 - 3β) / (β (1 - β))`, packaged as a function so that it can
be passed around as a whole. -/
private noncomputable def cbarIntegrand (β : ℝ) : ℝ := Real.log (2 - 3*β)/(β*(1-β))

/-- Pointwise bound used for the relaxed tail: on `[7/100, 1/14]` the BJS integrand is at most
`10`.  Indeed `log (2 - 3β) ≤ log (179/100) = log 2 + log (1 - 21/200) ≤ log 2 - 21/200 < 13/20`,
while `10 β (1 - β) ≥ 13/20` there. -/
private lemma cbarIntegrand_le_ten {β : ℝ} (hβ7 : (7:ℝ)/100 ≤ β) (hβ14 : β ≤ 1/14) :
    cbarIntegrand β ≤ 10 := by
  have hlog179 : Real.log (179/100) ≤ 13/20 := by
    have hmul : Real.log (179/100) = Real.log 2 + Real.log (1 - 21/200) := by
      have h := Real.log_mul (show (2:ℝ) ≠ 0 by norm_num) (show (1:ℝ) - 21/200 ≠ 0 by norm_num)
      have heq : (2:ℝ) * (1 - 21/200) = 179/100 := by norm_num
      rw [heq] at h; exact h
    have hsub : Real.log (1 - 21/200) ≤ -(21/200) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - 21/200 by norm_num)
      linarith
    have h3 : Real.log 2 < 6931471808/10^10 := log_two_lt_rat
    have h4 : (6931471808:ℝ)/10^10 + -(21/200) ≤ 13/20 := by norm_num
    linarith
  have hden : (0:ℝ) < β*(1-β) := by nlinarith
  have hnum : Real.log (2 - 3*β) ≤ 13/20 := by
    have h1 : (2:ℝ) - 3*β ≤ 179/100 := by linarith
    have h2 : (0:ℝ) < 2 - 3*β := by linarith
    exact le_trans (Real.log_le_log h2 h1) hlog179
  have hbig : (13:ℝ)/20 ≤ 10*(β*(1-β)) := by nlinarith
  show Real.log (2 - 3*β)/(β*(1-β)) ≤ 10
  rw [div_le_iff₀ hden]
  linarith

/-- Relaxed form of `cbar_integral_le` (BJS integral `≤ 0.75`): allowing the lower limit to undershoot `1/14` by up to `δ ≤ 1/700` only costs `10δ`. -/
theorem cbar_integral_le_relaxed {β₀ b δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/700)
    (hβ₀ : (1:ℝ)/14 - δ ≤ β₀) (hβ₀0 : 0 < β₀) (hb : b ≤ 1/3) (hb0 : β₀ ≤ b) :
    (∫ β in β₀..b, Real.log (2 - 3*β)/(β*(1-β))) ≤ 0.75 + 10*δ := by
  change (∫ β in β₀..b, cbarIntegrand β) ≤ 0.75 + 10*δ
  -- `β₀` stays in `[7/100, 1/3]`
  have hβ₀7 : (7:ℝ)/100 ≤ β₀ := by linarith
  have hβ₀3 : β₀ ≤ 1/3 := le_trans hb0 hb
  -- the integrand is nonnegative on `[7/100, 1/3]`
  have hnn : ∀ β ∈ Set.Icc ((7:ℝ)/100) (1/3), 0 ≤ cbarIntegrand β := by
    intro β hβ
    have hβ7 : (7:ℝ)/100 ≤ β := hβ.1
    have hβ3 : β ≤ 1/3 := hβ.2
    have hden : (0:ℝ) < β*(1-β) := by nlinarith
    show 0 ≤ Real.log (2 - 3*β)/(β*(1-β))
    exact div_nonneg (Real.log_nonneg (by linarith)) (le_of_lt hden)
  -- the integrand is interval integrable on every subinterval of `[7/100, 1/3]`
  have hII : ∀ a c : ℝ, (7:ℝ)/100 ≤ a → a ≤ c → c ≤ 1/3 →
      IntervalIntegrable cbarIntegrand volume a c := by
    intro a c ha hac hc
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hac]
    show ContinuousOn (fun β : ℝ => Real.log (2 - 3*β)/(β*(1-β))) (Set.Icc a c)
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro β hβ
      have : β ≤ 1/3 := le_trans hβ.2 hc
      linarith
    · fun_prop
    · intro β hβ
      have h1 : (7:ℝ)/100 ≤ β := le_trans ha hβ.1
      have h2 : β ≤ 1/3 := le_trans hβ.2 hc
      exact ne_of_gt (by nlinarith)
  -- monotonicity: enlarging the right endpoint increases the integral
  have hmono : ∀ a c : ℝ, (7:ℝ)/100 ≤ a → a ≤ b → b ≤ c → c ≤ 1/3 →
      (∫ β in a..b, cbarIntegrand β) ≤ ∫ β in a..c, cbarIntegrand β := by
    intro a c ha hab hbc hc
    have h1 : (∫ β in a..b, cbarIntegrand β) + (∫ β in b..c, cbarIntegrand β)
        = ∫ β in a..c, cbarIntegrand β :=
      intervalIntegral.integral_add_adjacent_intervals (hII a b ha hab (le_trans hbc hc))
        (hII b c (le_trans ha hab) hbc hc)
    have h2 : 0 ≤ ∫ β in b..c, cbarIntegrand β :=
      intervalIntegral.integral_nonneg hbc
        (fun u hu => hnn u ⟨le_trans (le_trans ha hab) hu.1, le_trans hu.2 hc⟩)
    linarith
  rcases lt_or_ge β₀ ((1:ℝ)/14) with hβ₀lt | hβ₀14
  · -- Case `β₀ < 1/14`: the extra piece makes no more than `10 δ`.
    have htail : (∫ β in β₀..((1:ℝ)/14), cbarIntegrand β) ≤ 10*δ := by
      have hta : (∫ β in β₀..((1:ℝ)/14), cbarIntegrand β)
          ≤ ∫ β in β₀..((1:ℝ)/14), (10:ℝ) := by
        apply intervalIntegral.integral_mono_on (le_of_lt hβ₀lt)
          (hII β₀ (1/14) hβ₀7 (le_of_lt hβ₀lt) (by norm_num))
          intervalIntegrable_const
        intro x hx
        exact cbarIntegrand_le_ten (le_trans hβ₀7 hx.1) hx.2
      rw [intervalIntegral.integral_const] at hta
      simp only [smul_eq_mul] at hta
      have h14δ : ((1:ℝ)/14 - β₀) ≤ δ := by linarith
      linarith [hta, h14δ]
    rcases lt_or_ge b ((1:ℝ)/14) with hblt | hb14
    · have h1 := hmono β₀ (1/14) hβ₀7 hb0 (le_of_lt hblt) (by norm_num)
      linarith [h1, htail, hδ0]
    · have hadj : (∫ β in β₀..((1:ℝ)/14), cbarIntegrand β) + (∫ β in ((1:ℝ)/14)..b, cbarIntegrand β)
            = ∫ β in β₀..b, cbarIntegrand β :=
        intervalIntegral.integral_add_adjacent_intervals
          (hII β₀ (1/14) hβ₀7 (le_of_lt hβ₀lt) (by norm_num))
          (hII (1/14) b (by norm_num) hb14 hb)
      have h2 : (∫ β in ((1:ℝ)/14)..b, cbarIntegrand β) ≤ 0.75 := by
        have h3 := hmono ((1:ℝ)/14) (1/3) (by norm_num) hb14 hb le_rfl
        have h4 : (∫ β in ((1:ℝ)/14)..(1/3), cbarIntegrand β) ≤ 0.75 :=
          cbar_integral_le (1/14) le_rfl (by norm_num)
        linarith [h3, h4]
      linarith [hadj, htail, h2]
  · -- Case `1/14 ≤ β₀`: the plain bound applies directly.
    have h1 := hmono β₀ (1/3) hβ₀7 hb0 hb le_rfl
    have h2 : (∫ β in β₀..(1/3), cbarIntegrand β) ≤ 0.75 := cbar_integral_le β₀ hβ₀14 hβ₀3
    linarith [h1, h2, hδ0]

end Work.NumberTheory.Chen.BTermCount
