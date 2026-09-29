import Mathlib

namespace Work.ANum3

open Complex Metric Filter
open scoped Topology

/-- **No two zeros.**  A function holomorphic on the closed disc of radius `R` around `0`, bounded
by `M` on the circle of radius `R`, cannot have two zeros (counted with multiplicity) inside the
open disc of radius `ρ`, provided `M ρ^2 < ‖F 0‖ (R - ρ)^2`.

The proof is the classical two-zero maximum modulus argument: writing
`g = dslope (dslope F a) b`, the function `g` is holomorphic on the disc of radius `R` and equals
`F z / ((z - a) (z - b))` away from `a, b`; the hypothesis `deriv F a = 0` when `a = b` is exactly
what makes the second divided difference well behaved.  On the circle `|z| = R` we have
`|z - a|, |z - b| ≥ R - ρ` (strictly), so `‖g z‖ ≤ M / (R - ρ)^2`; the maximum modulus principle
then gives `‖F 0‖ / (‖a‖ ‖b‖) ≤ M / (R - ρ)^2`, i.e. `‖F 0‖ (R - ρ)^2 ≤ M ‖a‖ ‖b‖`, and this
contradicts `M ρ^2 < ‖F 0‖ (R - ρ)^2` because `‖a‖ ‖b‖ < ρ^2`. -/
theorem no_two_zeros {F : ℂ → ℂ} {R ρ M : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ < R)
    (hM : 0 ≤ M)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R))
    (hsup : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ≤ M)
    (hbig : M * ρ ^ 2 < ‖F 0‖ * (R - ρ) ^ 2)
    {a b : ℂ} (ha : ‖a‖ < ρ) (hb : ‖b‖ < ρ) (hFa : F a = 0) (hFb : F b = 0)
    (hdouble : a = b → deriv F a = 0) : False := by
  have hρlam : 0 < R - ρ := by linarith
  -- degenerate cases: a zero at the origin makes the hypothesis on `‖F 0‖` impossible
  by_cases ha0 : a = 0
  · subst ha0
    have h : F 0 = 0 := hFa
    rw [h, norm_zero, zero_mul] at hbig
    nlinarith [hM, sq_nonneg ρ]
  by_cases hb0 : b = 0
  · subst hb0
    have h : F 0 = 0 := hFb
    rw [h, norm_zero, zero_mul] at hbig
    nlinarith [hM, sq_nonneg ρ]
  have hFdiff : DifferentiableOn ℂ F (closedBall (0 : ℂ) R) := hF.differentiableOn
  have hmemA : a ∈ ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith
  have hmemB : b ∈ ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith
  have hnhdsA : closedBall (0 : ℂ) R ∈ 𝓝 a := Metric.closedBall_mem_nhds_of_mem hmemA
  have hnhdsB : closedBall (0 : ℂ) R ∈ 𝓝 b := Metric.closedBall_mem_nhds_of_mem hmemB
  -- the two divided differences, removing the two zeros
  set g : ℂ → ℂ := dslope (dslope F a) b with hgdef
  have hg1 : DifferentiableOn ℂ (dslope F a) (closedBall (0 : ℂ) R) :=
    (differentiableOn_dslope hnhdsA).mpr hFdiff
  have hg2 : DifferentiableOn ℂ g (closedBall (0 : ℂ) R) :=
    (differentiableOn_dslope hnhdsB).mpr hg1
  -- the first divided difference vanishes at `b` (here the double-zero hypothesis is used)
  have hgab : dslope F a b = 0 := by
    rcases eq_or_ne b a with hba | hba
    · rw [hba, dslope_same, hdouble hba.symm]
    · rw [dslope_of_ne F hba, slope_def_field, hFb, hFa, sub_self, zero_div]
  have h0a : (0 : ℂ) ≠ a := fun h => ha0 h.symm
  have h0b : (0 : ℂ) ≠ b := fun h => hb0 h.symm
  have hg0 : g 0 = F 0 / (a * b) := by
    rw [hgdef, dslope_of_ne _ h0b, slope_def_field, dslope_of_ne F h0a, slope_def_field, hgab,
      hFa]
    field_simp
    ring
  have hgDiffCont : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
    refine DiffContOnCl.mk ?_ ?_
    · exact hg2.mono ball_subset_closedBall
    · rw [closure_ball 0 hR.ne']
      exact hg2.continuousOn
  -- boundary bound for `g`
  have hbound : ∀ w ∈ frontier (ball (0 : ℂ) R), ‖g w‖ ≤ M / (R - ρ) ^ 2 := by
    intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    have hwr : ‖w‖ = R := by
      have := Metric.mem_sphere.mp hw
      rwa [dist_eq_norm, sub_zero] at this
    have hwa : w ≠ a := by intro h; rw [h] at hwr; linarith [ha]
    have hwb : w ≠ b := by intro h; rw [h] at hwr; linarith [hb]
    have hgw : g w = F w / ((w - a) * (w - b)) := by
      rw [hgdef, dslope_of_ne _ hwb, slope_def_field, dslope_of_ne F hwa, slope_def_field, hgab,
        hFa]
      field_simp
      ring
    rw [hgw, norm_div, norm_mul]
    have hnum : ‖F w‖ ≤ M := hsup w hwr
    have hda : R - ρ ≤ ‖w - a‖ := by
      have h1 := norm_sub_norm_le w a
      rw [hwr] at h1
      linarith [ha]
    have hdb : R - ρ ≤ ‖w - b‖ := by
      have h1 := norm_sub_norm_le w b
      rw [hwr] at h1
      linarith [hb]
    have hprod : (R - ρ) ^ 2 ≤ ‖w - a‖ * ‖w - b‖ := by
      have h2 : (0 : ℝ) ≤ R - ρ := le_of_lt hρlam
      calc (R - ρ) ^ 2 = (R - ρ) * (R - ρ) := by ring
        _ ≤ ‖w - a‖ * ‖w - b‖ := mul_le_mul hda hdb h2 (norm_nonneg _)
    have hden_pos : 0 < ‖w - a‖ * ‖w - b‖ :=
      mul_pos (lt_of_lt_of_le hρlam hda) (lt_of_lt_of_le hρlam hdb)
    calc ‖F w‖ / (‖w - a‖ * ‖w - b‖)
        ≤ M / (‖w - a‖ * ‖w - b‖) := div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
      _ ≤ M / (R - ρ) ^ 2 := div_le_div_of_nonneg_left hM (pow_pos hρlam 2) hprod
  have hzcl : (0 : ℂ) ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball 0 hR.ne', Metric.mem_closedBall, dist_self]
    linarith
  -- maximum modulus principle at the centre
  have hmax : ‖g 0‖ ≤ M / (R - ρ) ^ 2 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgDiffCont hbound hzcl
  rw [hg0, norm_div, norm_mul] at hmax
  have habpos : 0 < ‖a‖ * ‖b‖ := mul_pos (norm_pos_iff.mpr ha0) (norm_pos_iff.mpr hb0)
  have hdpos : 0 < (R - ρ) ^ 2 := pow_pos hρlam 2
  have h2 : ‖F 0‖ * (R - ρ) ^ 2 ≤ M * (‖a‖ * ‖b‖) := (div_le_div_iff₀ habpos hdpos).mp hmax
  have hxy : ‖a‖ * ‖b‖ < ρ ^ 2 := by
    have h1 : ‖a‖ * ‖b‖ ≤ ‖a‖ * ρ := mul_le_mul_of_nonneg_left hb.le (norm_nonneg a)
    have h3 : ‖a‖ * ρ < ρ * ρ := mul_lt_mul_of_pos_right ha hρ
    nlinarith
  have h3 : M * (‖a‖ * ‖b‖) ≤ M * ρ ^ 2 := mul_le_mul_of_nonneg_left hxy.le hM
  linarith [hbig, h2, h3]

end Work.ANum3
