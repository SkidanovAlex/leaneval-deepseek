import Mathlib
import Submission.Commons.Analysis.StationaryPhase.log_phase_prim_left_general

namespace Commons.Analysis.StationaryPhase

open MeasureTheory Set Complex
open scoped Real Interval Topology

noncomputable section

/-- The oscillatory integrand of the log phase. -/
private def LF (t s : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))

private lemma LF_norm (t s : ℝ) : ‖LF t s‖ = 1 := by
  rw [LF, show Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ)
      = (((t * (Real.log s - s)) : ℝ) : ℂ) * Complex.I from by ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma continuousOn_LF (t : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (LF t) (Set.uIcc a b) := by
  have hsub : Set.uIcc a b ⊆ ({0}ᶜ : Set ℝ) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact ne_of_gt (lt_of_lt_of_le ha h1)
    · exact ne_of_gt (lt_of_lt_of_le hb h1)
  have hlog : ContinuousOn (fun s : ℝ => Real.log s - s) (Set.uIcc a b) :=
    (Real.continuousOn_log.mono hsub).sub continuousOn_id
  have hinner : ContinuousOn
      (fun s : ℝ => Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ)) (Set.uIcc a b) :=
    continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hlog))
  exact Complex.continuous_exp.comp_continuousOn hinner

private lemma intervalIntegrable_LF (t : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (LF t) volume a b :=
  (continuousOn_LF t ha hb).intervalIntegrable

theorem log_phase_half_line_left :
    ∃ C : ℝ, 0 < C ∧ ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
        ≤ C / Real.sqrt t := by
  refine ⟨26, by norm_num, ?_⟩
  intro t p z ht hp hpz hz
  change ‖∫ s in p..z, LF t s‖ ≤ 26 / Real.sqrt t
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  set δ : ℝ := 1 / Real.sqrt t with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have htδ : t * δ = Real.sqrt t := by
    rw [hδdef, mul_one_div, div_eq_iff (ne_of_gt hst)]
    exact (Real.mul_self_sqrt (le_of_lt ht0)).symm
  have hδ_le : δ ≤ 2 / Real.sqrt t := by
    rw [hδdef, div_le_div_iff₀ hst hst]
    nlinarith [hst]
  have hδ26 : δ ≤ 26 / Real.sqrt t := by
    rw [hδdef, div_le_div_iff₀ hst hst]
    nlinarith [hst]
  by_cases hcase : z ≤ 1 - δ
  · -- the whole interval stays away from the stationary point `1`
    have hzlt : z < 1 := by linarith
    have hb := Commons.Analysis.StationaryPhase.log_phase_prim_left_general t p z ht1
      (by linarith) hpz hzlt
    have hb1 : ‖∫ s in p..z, LF t s‖ ≤ min (z - p) (24 / (t * (1 - z))) := by
      simpa only [LF] using hb
    have hb' : ‖∫ s in p..z, LF t s‖ ≤ 24 / (t * (1 - z)) :=
      le_trans hb1 (min_le_right (z - p) (24 / (t * (1 - z))))
    have h1z : 0 < 1 - z := by linarith
    have hden : Real.sqrt t ≤ t * (1 - z) := by
      have h1 : t * δ ≤ t * (1 - z) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt ht0)
      rwa [htδ] at h1
    have h24 : 24 / (t * (1 - z)) ≤ 26 / Real.sqrt t := by
      rw [div_le_div_iff₀ (by positivity) hst]
      have h1 : (24:ℝ) * Real.sqrt t ≤ 24 * (t * (1 - z)) :=
        mul_le_mul_of_nonneg_left hden (by norm_num)
      have h2 : (24:ℝ) * (t * (1 - z)) ≤ 26 * (t * (1 - z)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith
    exact le_trans hb' h24
  · push Not at hcase
    -- hcase : 1 - δ < z
    by_cases hcaseB : 1 - δ ≤ p
    · -- the whole interval lies in the final short piece
      have h : ‖∫ s in p..z, LF t s‖ ≤ 1 * |z - p| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x _
        exact le_of_eq (LF_norm t x)
      rw [abs_of_nonneg (sub_nonneg.mpr hpz), one_mul] at h
      have hle : z - p ≤ δ := by linarith
      linarith
    · push Not at hcaseB
      -- hcaseB : p < 1 - δ
      have h1δpos : 0 < 1 - δ := by linarith
      have hp0 : (0:ℝ) < p := by linarith
      have hleft_ibp := Commons.Analysis.StationaryPhase.log_phase_prim_left_general
        t p (1 - δ) ht1 (by linarith) hcaseB.le (by linarith)
      have hleft : ‖∫ s in p..(1 - δ), LF t s‖ ≤ 24 / Real.sqrt t := by
        have hb1 : ‖∫ s in p..(1 - δ), LF t s‖
            ≤ min ((1 - δ) - p) (24 / (t * (1 - (1 - δ)))) := by
          simpa only [LF] using hleft_ibp
        have hb' : ‖∫ s in p..(1 - δ), LF t s‖ ≤ 24 / (t * (1 - (1 - δ))) :=
          le_trans hb1 (min_le_right ((1 - δ) - p) (24 / (t * (1 - (1 - δ)))))
        have hsimp : 24 / (t * (1 - (1 - δ))) = 24 / Real.sqrt t := by
          rw [show (1:ℝ) - (1 - δ) = δ from by ring, htδ]
        rwa [hsimp] at hb'
      have hright : ‖∫ s in (1 - δ)..z, LF t s‖ ≤ δ := by
        have h : ‖∫ s in (1 - δ)..z, LF t s‖ ≤ 1 * |z - (1 - δ)| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro x _
          exact le_of_eq (LF_norm t x)
        rw [abs_of_nonneg (sub_nonneg.mpr hcase.le), one_mul] at h
        have hzδ : z - (1 - δ) ≤ δ := by linarith
        linarith
      have hint1 := intervalIntegrable_LF t (a := p) (b := 1 - δ) hp0 h1δpos
      have hint2 := intervalIntegrable_LF t (a := 1 - δ) (b := z) h1δpos (by linarith)
      have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      have hsum : ‖∫ s in p..z, LF t s‖ ≤ 24 / Real.sqrt t + δ := by
        rw [← hadd]
        calc ‖(∫ s in p..(1 - δ), LF t s) + ∫ s in (1 - δ)..z, LF t s‖
            ≤ ‖∫ s in p..(1 - δ), LF t s‖ + ‖∫ s in (1 - δ)..z, LF t s‖ := norm_add_le _ _
          _ ≤ 24 / Real.sqrt t + δ := add_le_add hleft hright
      have hfin : 24 / Real.sqrt t + δ ≤ 26 / Real.sqrt t := by
        have h2 : 24 / Real.sqrt t + 2 / Real.sqrt t = 26 / Real.sqrt t := by ring
        linarith [hδ_le]
      exact le_trans hsum hfin

end

end Commons.Analysis.StationaryPhase
