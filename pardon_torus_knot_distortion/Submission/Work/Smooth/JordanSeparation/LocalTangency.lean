import Submission.Work.Smooth.JordanSeparation.Jump
import Submission.Work.Smooth.JordanSeparation.LocalSides

/-!
# Tangency of a `C¹` curve at a regular parameter, in the local frame

Two bricks used by the proof of `collar_side` (the two-sidedness of a collar,
`SCHOENFLIES.md` §2(a)⁗):

* `deriv_locR_zero` — in the local frame `(locE, locN)` at a regular parameter, the curve's
  transverse coordinate `locR` has derivative `0`: the curve is tangent to `locE`;
* `exists_locR_le_mul_locS` — consequently `locR = o(locS)` there: for every `κ > 0` and small `t`,
  `|locR c t| ≤ κ |locS c t|`.

Together with `deriv_locS_zero` (`deriv (locS c) 0 = ‖deriv c.γ 0‖ ≠ 0`), already in
`LocalFrame.lean`, these are the analytic input for the statement that the collar points
`c.γ 0 ± u·v 0` lie in the same components of the complement of the trace as the normal points
`c.γ 0 ± u·locN`, hence in the two different sides of the curve.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section


/-- `locR` has derivative `0` at a regular parameter: the curve is tangent to `locE` there. -/
theorem deriv_locR_zero (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) :
    deriv (locR c) 0 = 0 := by
  have hd : HasDerivAt c.γ (deriv c.γ 0) 0 := (c.differentiable 0).hasDerivAt
  have hsub : HasDerivAt (fun s : ℝ => c.γ s - c.γ 0) (deriv c.γ 0) 0 := hd.sub_const _
  have hdiv : HasDerivAt (fun s : ℝ => (c.γ s - c.γ 0) / locE c) (deriv c.γ 0 / locE c) 0 :=
    hsub.div_const _
  have him : HasDerivAt (fun s : ℝ => ((c.γ s - c.γ 0) / locE c).im) (deriv c.γ 0 / locE c).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hdiv
  have hfun : (fun s : ℝ => ((c.γ s - c.γ 0) / locE c).im) = locR c := rfl
  rw [hfun] at him
  rw [him.deriv, div_locE_eq_re c hreg, Complex.ofReal_im]

/-- **The tangency gives `locR = o(locS)`.** -/
theorem exists_locR_le_mul_locS (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < |t| → |t| < η → |locR c t| ≤ κ * |locS c t| := by
  set m : ℝ := ‖deriv c.γ 0‖ with hm
  have hmpos : 0 < m := norm_pos_iff.mpr hreg
  -- the difference quotient of the curve
  have hslope : Filter.Tendsto (fun t : ℝ => (c.γ t - c.γ 0) / locE c / (t : ℂ))
      (nhdsWithin 0 {t : ℝ | t ≠ 0}) (nhds (deriv c.γ 0 / locE c)) := by
    have hd : HasDerivAt c.γ (deriv c.γ 0) 0 := (c.differentiable 0).hasDerivAt
    have hsub : HasDerivAt (fun s : ℝ => c.γ s - c.γ 0) (deriv c.γ 0) 0 := hd.sub_const _
    have hdiv : HasDerivAt (fun s : ℝ => (c.γ s - c.γ 0) / locE c) (deriv c.γ 0 / locE c) 0 :=
      hsub.div_const _
    refine (hdiv.tendsto_slope).congr' ?_
    filter_upwards with t
    simp [slope]
    ring
  have hS : Filter.Tendsto (fun t : ℝ => locS c t / t) (nhdsWithin 0 {t : ℝ | t ≠ 0})
      (nhds m) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hslope
    have h2 : (fun t : ℝ => locS c t / t)
        = fun t => (((c.γ t - c.γ 0) / locE c) / (t : ℂ)).re := by
      funext t
      rw [Complex.div_ofReal_re]
      rfl
    rw [div_locE_eq_re c hreg, Complex.ofReal_re] at h
    rw [h2, hm]
    exact h
  have hR : Filter.Tendsto (fun t : ℝ => locR c t / t) (nhdsWithin 0 {t : ℝ | t ≠ 0})
      (nhds 0) := by
    have h := Complex.continuous_im.continuousAt.tendsto.comp hslope
    have h2 : (fun t : ℝ => locR c t / t)
        = fun t => (((c.γ t - c.γ 0) / locE c) / (t : ℂ)).im := by
      funext t
      rw [Complex.div_ofReal_im]
      rfl
    rw [div_locE_eq_re c hreg, Complex.ofReal_im] at h
    rw [h2]
    simpa [Function.comp_def] using h
  -- epsilonics
  have hSpos : ∀ᶠ t in nhdsWithin 0 {t : ℝ | t ≠ 0}, m / 2 ≤ |locS c t / t| := by
    have h := (hS.abs).eventually (eventually_ge_nhds (show |m| / 2 < |m| by
      rw [abs_of_pos hmpos]; linarith))
    simpa [abs_of_pos hmpos] using h
  have hRsmall : ∀ᶠ t in nhdsWithin 0 {t : ℝ | t ≠ 0},
      |locR c t / t| < κ * m / 2 := by
    have h := (hR.abs).eventually (eventually_lt_nhds (show |(0:ℝ)| < κ * m / 2 by
      rw [abs_zero]; positivity))
    simpa using h
  have hboth := hSpos.and hRsmall
  rw [eventually_nhdsWithin_iff] at hboth
  obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.mp hboth
  refine ⟨η, hηpos, fun t ht htη => ?_⟩
  have hmem : t ∈ ({0}ᶜ : Set ℝ) := abs_pos.mp ht
  have hdist : dist t (0:ℝ) < η := by rw [Real.dist_eq, sub_zero]; exact htη
  obtain ⟨h1, h2⟩ := hη hdist hmem
  have htpos : (0:ℝ) < |t| := abs_pos.mpr (abs_pos.mp ht)
  rw [abs_div] at h1 h2
  have h1' : m / 2 * |t| ≤ |locS c t| := (le_div_iff₀ htpos).mp h1
  have h2' : |locR c t| < κ * m / 2 * |t| := (div_lt_iff₀ htpos).mp h2
  have h3 : κ * (m / 2 * |t|) ≤ κ * |locS c t| :=
    mul_le_mul_of_nonneg_left h1' hκ.le
  linarith
end

end Work.Smooth.JordanSeparation
