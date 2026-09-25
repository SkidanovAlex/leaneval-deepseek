import Mathlib
import Submission.Commons.NumberTheory.Robin.caXi2_lower
import Submission.Commons.NumberTheory.Robin.caXi2_upper
import Submission.Commons.Analysis.Real.log_one_add_inv_bounds
import Submission.Commons.Analysis.Log.log_1530_bounds
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF

namespace Commons.NumberTheory.Robin

/-! ## Auxiliary: the "level-two threshold" function

`phi t = log (1 + 1/(t + t²)) / log t` is (for `t > 1`) the value `F(t,2)` of the CA
level-two threshold function.  It is strictly antitone (Mathlib-level lemma
`caXi2_upper_f2_strict`), which together with `caXi2_lower` gives the level-two bound. -/
private noncomputable def phi (t : ℝ) : ℝ := Real.log (1 + 1 / (t + t ^ 2)) / Real.log t

private lemma phi_continuousOn_Ioi_one : ContinuousOn phi (Set.Ioi (1 : ℝ)) := by
  unfold phi
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · apply ContinuousOn.add continuousOn_const
      apply ContinuousOn.div continuousOn_const
      · exact (continuousOn_id.add (continuousOn_id.pow 2))
      · intro x hx
        have hx1 : (1 : ℝ) < x := hx
        nlinarith [sq_nonneg x]
    · intro x hx
      have hx1 : (1 : ℝ) < x := hx
      have : 0 < x + x ^ 2 := by nlinarith [sq_nonneg x]
      positivity
  · exact continuousOn_id.log (fun x hx => ne_of_gt (lt_trans zero_lt_one hx))
  · intro x hx
    exact ne_of_gt (Real.log_pos hx)

theorem ca_level_two_lower {ε ξ : ℝ} (hε : 0 < ε) (hξ : 1530 ≤ ξ)
    (hεξ : ε ≤ Real.log (1 + 1 / ξ) / Real.log ξ) {p : ℕ} (hp : Nat.Prime p)
    (h : (p : ℝ) ≤ Real.sqrt (2 * ξ) * (1 - Real.log 2 / (2 * Real.log ξ))) :
    (2 : ℝ) ≤ Real.log (((p : ℝ) ^ (1 + ε) - 1) / ((p : ℝ) ^ (1 + ε) - (p : ℝ))) / Real.log (p : ℝ) := by
  have hξ1 : (1 : ℝ) < ξ := by linarith
  have hξpos : (0 : ℝ) < ξ := by linarith
  have hlogξ_pos : 0 < Real.log ξ := Real.log_pos hξ1
  have hlogξ_ge : (7.333 : ℝ) ≤ Real.log ξ := by
    have hb := Commons.Analysis.Log.log_1530_bounds.1
    have h2 : Real.log 1530 ≤ Real.log ξ := Real.log_le_log (by norm_num) hξ
    linarith
  set c : ℝ := Real.log (1 + 1 / ξ) / Real.log ξ with hcdef
  have hc_pos : 0 < c := by
    rw [hcdef]
    exact div_pos (Real.log_pos (by linarith [one_div_pos.mpr hξpos])) hlogξ_pos
  have hc_le : c ≤ 1 / 1000 := by
    rw [hcdef]
    have hlog_le : Real.log (1 + 1 / ξ) ≤ 1 / ξ :=
      (Commons.Analysis.Real.log_one_add_inv_bounds hξpos).2
    have h1 : Real.log (1 + 1 / ξ) / Real.log ξ ≤ (1 / ξ) / Real.log ξ :=
      div_le_div_of_nonneg_right hlog_le (le_of_lt hlogξ_pos)
    have h2 : (1 / ξ) / Real.log ξ = 1 / (ξ * Real.log ξ) := by ring
    rw [h2] at h1
    have h4 : (1000 : ℝ) ≤ ξ * Real.log ξ := by nlinarith [hξ, hlogξ_ge]
    exact le_trans h1 (one_div_le_one_div_of_le (by norm_num) h4)
  have hεc : ε ≤ c := by rw [hcdef]; exact hεξ
  -- `phi 2 ≥ c`
  have hphi2 : c ≤ phi 2 := by
    have h1 : (1 : ℝ) / 7 < Real.log (1 + 1 / 6) := by
      have hb := (Commons.Analysis.Real.log_one_add_inv_bounds (t := 6) (by norm_num)).1
      linarith
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h4 : (1 : ℝ) / 7 < Real.log (1 + 1 / 6) / Real.log 2 := by
      rw [lt_div_iff₀ h3]
      have h5 : (1 : ℝ) / 7 * Real.log 2 ≤ 1 / 7 * 1 :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
      linarith
    have h5 : phi 2 = Real.log (1 + 1 / 6) / Real.log 2 := by
      unfold phi
      norm_num
    rw [h5]
    linarith [hc_le]
  -- `phi (1/c) ≤ c`
  have hphib : phi (1 / c) ≤ c := by
    have hb_ge : (1000 : ℝ) ≤ 1 / c := by
      rw [le_div_iff₀ hc_pos]
      nlinarith [hc_le]
    have hbpos : 0 < (1 : ℝ) / c := div_pos one_pos hc_pos
    have hlog1000 : (1 : ℝ) ≤ Real.log 1000 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 1000)]
      linarith [Real.exp_one_lt_d9]
    have hlogb_ge : (1 : ℝ) ≤ Real.log (1 / c) :=
      le_trans hlog1000 (Real.log_le_log (by norm_num) hb_ge)
    have hden_pos : 0 < Real.log (1 / c) := lt_of_lt_of_le one_pos hlogb_ge
    have hnum_pos : 0 < (1 / c) + (1 / c) ^ 2 := by nlinarith [hbpos, sq_nonneg (1 / c)]
    have hnum_le : Real.log (1 + 1 / ((1 / c) + (1 / c) ^ 2)) ≤ 1 / ((1 / c) + (1 / c) ^ 2) := by
      have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / ((1 / c) + (1 / c) ^ 2) by
        positivity)
      linarith
    have hstep : 1 / ((1 / c) + (1 / c) ^ 2) ≤ 1 / (1 / c) ^ 2 := by
      apply one_div_le_one_div_of_le (pow_pos hbpos 2)
      linarith [hbpos]
    have hle1 : phi (1 / c) ≤ (1 / (1 / c) ^ 2) / Real.log (1 / c) := by
      unfold phi
      apply div_le_div_of_nonneg_right (le_trans hnum_le hstep) (le_of_lt hden_pos)
    have hc2eq : (1 / (1 / c) ^ 2 : ℝ) = c ^ 2 := by
      rw [one_div, one_div, inv_pow, inv_inv]
    have hfin : (1 / (1 / c) ^ 2) / Real.log (1 / c) ≤ c := by
      rw [hc2eq]
      have h1 : c ^ 2 / Real.log (1 / c) ≤ c ^ 2 / 1 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hlogb_ge
      have h2 : c ^ 2 / 1 = c ^ 2 := by ring
      rw [h2] at h1
      have hc1 : c ≤ 1 := by linarith [hc_le]
      have h3 : c ^ 2 ≤ c := sq_le (le_of_lt hc_pos) hc1
      linarith
    linarith
  have h2c : (2 : ℝ) ≤ 1 / c := by
    rw [le_div_iff₀ hc_pos]
    nlinarith [hc_le]
  -- IVT: there is `ξ₂ > 1` with `phi ξ₂ = c`
  have hcont : ContinuousOn phi (Set.Icc (2 : ℝ) (1 / c)) :=
    phi_continuousOn_Ioi_one.mono (fun x hx => lt_of_lt_of_le one_lt_two hx.1)
  have hmem : c ∈ Set.Icc (phi (1 / c)) (phi 2) := ⟨hphib, hphi2⟩
  obtain ⟨ξ2, hξ2mem, hξ2phi⟩ := intermediate_value_Icc' h2c hcont hmem
  have hξ2gt1 : (1 : ℝ) < ξ2 := lt_of_lt_of_le one_lt_two hξ2mem.1
  have hF : Real.log (1 + 1 / (ξ2 + ξ2 ^ 2)) / Real.log ξ2 = Real.log (1 + 1 / ξ) / Real.log ξ := by
    have h := hξ2phi
    rw [hcdef] at h
    simpa only [phi] using h
  have hXle : Real.sqrt (2 * ξ) * (1 - Real.log 2 / (2 * Real.log ξ)) ≤ ξ2 :=
    caXi2_lower ξ ξ2 hξ hξ2gt1 hF
  have hpξ2 : (p : ℝ) ≤ ξ2 := le_trans h hXle
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hphi_le : phi ξ2 ≤ phi p := by
    rcases lt_or_eq_of_le hpξ2 with hlt | heq
    · have hh := caXi2_upper_f2_strict hp1 hlt
      exact le_of_lt (by simpa only [phi] using hh)
    · exact le_of_eq (by rw [heq])
  have hφp : c ≤ phi p := by rw [← hξ2phi]; exact hphi_le
  have hεphi : ε ≤ phi p := le_trans hεc hφp
  -- Convert `ε ≤ phi p` into the final log statement, via `caMu_ge_iff_caF`
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hkey : Real.log (((p : ℝ) ^ (2 + 1 : ℕ) - 1) / (((p : ℝ) ^ (2 + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ)
      = Real.log (1 + 1 / ((p : ℝ) + (p : ℝ) ^ 2)) / Real.log (p : ℝ) := by
    have h3 : ((p : ℝ) ^ (2 + 1 : ℕ)) = (p : ℝ) ^ 3 := by norm_num
    rw [h3]
    have hpd : (p : ℝ) ^ 3 - (p : ℝ) ≠ 0 := by
      have hpe : (0 : ℝ) < (p : ℝ) ^ 3 - (p : ℝ) := by
        have heq : (p : ℝ) ^ 3 - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) + 1) := by ring
        rw [heq]
        exact mul_pos (mul_pos hp0 (by linarith)) (by linarith)
      exact ne_of_gt hpe
    have hpp : (p : ℝ) + (p : ℝ) ^ 2 ≠ 0 := by
      have : 0 < (p : ℝ) + (p : ℝ) ^ 2 := by nlinarith [hp0, sq_nonneg (p : ℝ)]
      exact ne_of_gt this
    have hfrac : ((p : ℝ) ^ 3 - 1) / ((p : ℝ) ^ 3 - (p : ℝ)) = 1 + 1 / ((p : ℝ) + (p : ℝ) ^ 2) := by
      rw [div_eq_iff hpd]
      field_simp
      ring
    rw [hfrac]
  have hεkey : ε ≤ Real.log (((p : ℝ) ^ (2 + 1 : ℕ) - 1) / (((p : ℝ) ^ (2 + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ) := by
    rw [hkey]
    simpa only [phi] using hεphi
  exact (caMu_ge_iff_caF p ε 2 hp.two_le hε (by norm_num)).mpr hεkey

end Commons.NumberTheory.Robin
