import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Model

namespace Work.Parabolic

/-- **The superlevel sets of the model Green function of `ℍ` have compact closures.**

Here `greenUpperHalfPlane w = Real.log (‖(w:ℂ) + I‖ / ‖(w:ℂ) - I‖)` (`Submission/Work/Parabolic/Model.lean`), the classical Green function of the upper half plane with pole `i`.

Route.  Put `a = (w:ℂ).re`, `b = (w:ℂ).im`.  For `w` with `ε ≤ greenUpperHalfPlane w`:
* `Real.exp ε * ‖(w:ℂ) - I‖ ≤ ‖(w:ℂ) + I‖` (from `Real.le_log_iff_exp_le`; note `w ≠ iUHP`, since otherwise `greenUpperHalfPlane w = Real.log 0 = 0 < ε`);
* *far region*: `‖(w:ℂ) - I‖ ≤ 2 / (Real.exp ε - 1)`, because `‖(w:ℂ) + I‖ ≤ ‖(w:ℂ) - I‖ + 2`;
* *near the boundary*: `(Real.exp ε - 1) / (Real.exp ε + 1) ≤ b`.  Squaring the first display and using
  `Complex.normSq (w ± I) = a² + (b ± 1)²` gives `(Real.exp ε)^2 * (a² + (b-1)²) ≤ a² + (b+1)²`; when `b ≤ 1`
  this forces `Real.exp ε * (1 - b) ≤ b + 1`, and when `1 ≤ b` there is nothing to prove.
So the superlevel set is contained in `K = {w : UpperHalfPlane | δ ≤ (w:ℂ).im ∧ ‖(w:ℂ) - I‖ ≤ r}` with
`δ = (Real.exp ε - 1) / (Real.exp ε + 1)`, `r = 2 / (Real.exp ε - 1)`, and `K` is compact: it is the image of
the closed and bounded (hence compact) set `{z : ℂ | δ ≤ z.im} ∩ Metric.closedBall I r` under the continuous
inclusion `z ↦ ⟨z, ·⟩` into `ℍ` (`Continuous.subtype_mk`).  Finish with `IsCompact.of_isClosed_subset`, or with
`Work.Parabolic.isCompact_closure_iff_exists_isCompact_superset` (`Submission/Work/Parabolic/Basic.lean`). -/
theorem isCompact_closure_superlevel_greenUpperHalfPlane {ε : ℝ} (hε : 0 < ε) :
    IsCompact (closure {w : UpperHalfPlane | ε ≤ greenUpperHalfPlane w}) := by
  set e := Real.exp ε with he
  have he1 : 1 < e := he ▸ Real.one_lt_exp_iff.mpr hε
  have he0 : (0 : ℝ) < e := lt_trans zero_lt_one he1
  have hesub1 : 0 < e - 1 := by linarith
  have hden : 0 < e + 1 := by linarith
  set δ := (e - 1) / (e + 1) with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hesub1 hden
  set r := 2 / (e - 1) with hr
  -- The superlevel set is contained in the closed Apollonius-type region `{δ ≤ im} ∩ B(I, r)`.
  have key : ∀ w : UpperHalfPlane, ε ≤ greenUpperHalfPlane w →
      δ ≤ (w : ℂ).im ∧ ‖(w : ℂ) - Complex.I‖ ≤ r := by
    intro w hw
    have hw' : ε ≤ Real.log (‖(w : ℂ) + Complex.I‖ / ‖(w : ℂ) - Complex.I‖) := by
      simpa only [greenUpperHalfPlane] using hw
    set z : ℂ := (w : ℂ) with hz
    have hb : 0 < z.im := by rw [hz]; exact w.im_pos
    -- the pole `i` is not in the superlevel set
    have hzne : z ≠ Complex.I := by
      intro h
      rw [h] at hw'
      norm_num at hw'
      linarith
    have hden' : 0 < ‖z - Complex.I‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hzne
    have hznemI : z + Complex.I ≠ 0 := by
      intro h
      have h1 : (z + Complex.I).im = 0 := by rw [h]; simp
      simp at h1
      linarith
    have hnum' : 0 < ‖z + Complex.I‖ := by
      rw [norm_pos_iff]; exact hznemI
    have hq : 0 < ‖z + Complex.I‖ / ‖z - Complex.I‖ := div_pos hnum' hden'
    -- the basic inequality `exp ε * ‖z - i‖ ≤ ‖z + i‖`
    have hquot : e ≤ ‖z + Complex.I‖ / ‖z - Complex.I‖ :=
      he ▸ (Real.le_log_iff_exp_le hq).mp hw'
    have hmul : e * ‖z - Complex.I‖ ≤ ‖z + Complex.I‖ := (le_div_iff₀ hden').mp hquot
    have hns_sub : Complex.normSq (z - Complex.I) = z.re ^ 2 + (z.im - 1) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.I_re,
        Complex.I_im]
      ring
    have hns_add : Complex.normSq (z + Complex.I) = z.re ^ 2 + (z.im + 1) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.I_re,
        Complex.I_im]
      ring
    refine ⟨?_, ?_⟩
    · -- near the boundary of `ℍ`
      have hsq : e ^ 2 * (z.re ^ 2 + (z.im - 1) ^ 2) ≤ z.re ^ 2 + (z.im + 1) ^ 2 := by
        have hs : (e * ‖z - Complex.I‖) ^ 2 ≤ ‖z + Complex.I‖ ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg he0.le (norm_nonneg _)) hmul 2
        rw [mul_pow, Complex.sq_norm, Complex.sq_norm, hns_sub, hns_add] at hs
        exact hs
      have hkey : e ^ 2 * (1 - z.im) ^ 2 ≤ (z.im + 1) ^ 2 := by
        nlinarith [hsq, sq_nonneg z.re, sq_nonneg (e * z.re), sq_nonneg (e - 1)]
      have hlin : e * (1 - z.im) ≤ z.im + 1 :=
        le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by linarith)
          (by rw [mul_pow]; exact hkey)
      rw [hδ, div_le_iff₀ hden]
      linarith
    · -- far from the pole
      have h2 : ‖z + Complex.I‖ ≤ ‖z - Complex.I‖ + 2 := by
        have hz2 : z + Complex.I = (z - Complex.I) + 2 * Complex.I := by ring
        calc ‖z + Complex.I‖ = ‖(z - Complex.I) + 2 * Complex.I‖ := by rw [hz2]
          _ ≤ ‖z - Complex.I‖ + ‖(2 : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = ‖z - Complex.I‖ + 2 := by simp [Complex.norm_I]
      have h3 : (e - 1) * ‖z - Complex.I‖ ≤ 2 := by linarith
      rw [hr, le_div_iff₀ hesub1]
      linarith
  -- the region is compact: its image in `ℂ` is closed and bounded
  have hKcomp : IsCompact {w : UpperHalfPlane | δ ≤ (w : ℂ).im ∧
      ‖(w : ℂ) - Complex.I‖ ≤ r} := by
    rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
    have hKimage : (UpperHalfPlane.coe '' {w : UpperHalfPlane |
          δ ≤ (w : ℂ).im ∧ ‖(w : ℂ) - Complex.I‖ ≤ r}) =
        {z : ℂ | δ ≤ z.im} ∩ Metric.closedBall Complex.I r := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw.1, by rw [Metric.mem_closedBall, Complex.dist_eq]; exact hw.2⟩
      · rintro ⟨hz1, hz2⟩
        have hz0 : 0 < z.im := lt_of_lt_of_le hδpos hz1
        refine ⟨⟨z, hz0⟩, ⟨hz1, ?_⟩, rfl⟩
        rw [Metric.mem_closedBall, Complex.dist_eq] at hz2
        exact hz2
    rw [hKimage]
    exact (isCompact_closedBall Complex.I r).inter_left
      (isClosed_le continuous_const Complex.continuous_im)
  exact IsCompact.of_isClosed_subset hKcomp isClosed_closure
    (closure_minimal (fun w hw => key w hw) hKcomp.isClosed)

end Work.Parabolic
