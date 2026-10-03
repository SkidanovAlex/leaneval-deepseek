import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.annulus_le_boundary

namespace Work.Potential

/-! ## Auxiliary facts about the logarithmic barrier `z ↦ log (ρ / ‖z‖)` -/

/-- The barrier `z ↦ Real.log (ρ / ‖z‖)` is harmonic at every point different from `0`. -/
private lemma harmonicAt_log_div_norm {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log (ρ / ‖w‖)) z := by
  have hlog : InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ‖w‖) z := by
    have h := AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w) analyticAt_id
      (by simpa using hz)
    simpa using h
  have h2 : InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ρ - Real.log ‖w‖) z :=
    (InnerProductSpace.harmonicAt_const (Real.log ρ)).sub hlog
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr h2
  filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hz] with w hw
  rw [Real.log_div (ne_of_gt hρ) (norm_ne_zero_iff.mpr hw)]

/-- The barrier `z ↦ Real.log (ρ / ‖z‖)` is continuous on any set avoiding `0`. -/
private lemma continuousOn_log_div_norm {ρ : ℝ} (hρ : 0 < ρ) {s : Set ℂ}
    (hs : ∀ z ∈ s, z ≠ 0) : ContinuousOn (fun z : ℂ => Real.log (ρ / ‖z‖)) s := by
  have hne : ∀ z ∈ s, ‖z‖ ≠ 0 := fun z hz => norm_ne_zero_iff.mpr (hs z hz)
  have h1 : ContinuousOn (fun z : ℂ => ρ / ‖z‖) s :=
    continuousOn_const.div continuous_norm.continuousOn hne
  exact h1.log (fun z hz => div_ne_zero (ne_of_gt hρ) (hne z hz))

set_option linter.unusedVariables false in
/-- **Linear barrier bound on an annulus.**  If `W : ℂ → ℝ` is harmonic on the open annulus
`{z | δ < ‖z‖ < ρ}`, continuous on the closed annulus, bounded by `B ≥ 0` on the inner circle
`‖z‖ = δ` and by `0` on the outer circle `‖z‖ = ρ`, then `W z ≤ B · log(ρ/‖z‖) / log(ρ/δ)` on the
closed annulus.  Suggested route: apply the maximum principle on the closed annulus
`Commons.Analysis.Complex.Harmonic.annulus_le_boundary` (available in this workspace at file
`Submission/Commons/Analysis/Complex/Harmonic/annulus_le_boundary.lean`) to
`W - B * (Real.log (ρ/δ))⁻¹ • (fun z => Real.log (ρ / ‖z‖))`, using that the log barrier is harmonic
away from `0`. -/
theorem annulus_barrier_le {W : ℂ → ℝ} {δ ρ B : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ) (hB : 0 ≤ B)
    (hharm : ∀ z : ℂ, δ < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt W z)
    (hcont : ContinuousOn W {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ})
    (hinner : ∀ z : ℂ, ‖z‖ = δ → W z ≤ B)
    (houter : ∀ z : ℂ, ‖z‖ = ρ → W z ≤ 0) :
    ∀ z : ℂ, δ ≤ ‖z‖ → ‖z‖ ≤ ρ →
      W z ≤ B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖z‖) := by
  classical
  have hρ : 0 < ρ := lt_trans hδ hδρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hLpos : 0 < Real.log (ρ / δ) := by
    rw [Real.log_pos_iff (le_of_lt (div_pos hρ hδ))]
    exact (one_lt_div hδ).mpr hδρ
  have hLne : Real.log (ρ / δ) ≠ 0 := ne_of_gt hLpos
  -- The barrier `V` is harmonic on the open annulus.
  have hVharm : InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ => W z - B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖z‖))
      {z : ℂ | δ < ‖z‖ ∧ ‖z‖ < ρ} := by
    intro z hz
    have hzne : z ≠ 0 := by
      intro h0
      have hz0 : ‖z‖ = 0 := by rw [h0, norm_zero]
      linarith [hz.1, hδ]
    have hβ : InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log (ρ / ‖w‖)) z :=
      harmonicAt_log_div_norm hρ hzne
    have hsum : InnerProductSpace.HarmonicAt
        (fun w : ℂ => W w - B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖w‖)) z := by
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr
        ((hharm z hz.1 hz.2).sub (hβ.const_smul (c := B * (Real.log (ρ / δ))⁻¹)))
      filter_upwards with w
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hsum
  -- `V` is continuous on the closed annulus.
  have hVcont : ContinuousOn
      (fun z : ℂ => W z - B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖z‖))
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
    refine hcont.sub ?_
    refine (continuousOn_log_div_norm hρ ?_).const_mul (B * (Real.log (ρ / δ))⁻¹)
    intro z hz h0
    have hz0 : ‖z‖ = 0 := by rw [h0, norm_zero]
    linarith [hz.1, hδ]
  -- `V ≤ 0` on both boundary circles.
  have hVbd : ∀ z : ℂ, (‖z‖ = δ ∨ ‖z‖ = ρ) →
      W z - B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖z‖) ≤ 0 := by
    intro z hz
    rcases hz with hz | hz
    · have hBd : W z ≤ B := hinner z hz
      have h3 : B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / δ) = B := by
        rw [mul_assoc, inv_mul_cancel₀ hLne, mul_one]
      rw [hz, h3]
      linarith
    · have h0 : W z ≤ 0 := houter z hz
      have hlog : Real.log (ρ / ‖z‖) = 0 := by rw [hz, div_self hρne, Real.log_one]
      rw [hlog, mul_zero, sub_zero]
      exact h0
  intro z hz1 hz2
  have h := Commons.Analysis.Complex.Harmonic.annulus_le_boundary
    (u := fun z : ℂ => W z - B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖z‖))
    (r := δ) (R := ρ) (M := 0) hδ hδρ hVharm hVcont hVbd z hz1 hz2
  linarith

end Work.Potential
