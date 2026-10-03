import Mathlib
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.phi_ne_zero_far
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Parab.inversion.exists_mul_log_lt

namespace Work.PertCrux

open Complex Metric Filter

/-!
# `Work.PertCrux.Xc_local_three`

**The curve `Xc d = τ₀ ∘ φ₀` of a §4.1 datum is locally the identity, far out in the repelling
sector `QLeft ξ₀`.**  There is `R > 0` such that for every `z ∈ QLeft ξ₀` with `‖z‖ ≥ R` whose
`‖z‖/10`-ball still lies in `QLeft ξ₀`, the curve is holomorphic at `z` and

`‖Xc'(z) - 1‖ ≤ 1/2`.

The statement is exactly the *derivative* half of the two-term asymptotic
`τ₀(φ₀ w) = w + a log(-w) + b + o(1)` (`d.φ_asymp`), and the work is entirely done by
`Work.Pert.Ksub2.Xcurve_bounds`: it produces a constant `C > 0` with
`‖deriv (Xc d) u - 1‖ ≤ C (1 + log ‖u‖)/‖u‖` on such balls, and it remains to observe that
`C (1 + log x) ≤ x/2` for all large `x` (`log = o(x)`, here via
`Real.isLittleO_log_id_atTop`), which gives the bound `1/2`.  Differentiability at `z` is
re-derived: on the ball `φ₀` is holomorphic (`d.φ_holo` on `Dφ ⊇ QLeft ξ₀`) and nonvanishing
(asymptotic + `Work.Pert.exists_norm_add_clog_bound`), so `τ₀ ∘ φ₀` is holomorphic there.
-/

theorem Xc_local_three {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, z ∈ MandelDim.QLeft d.ξ₀ → R ≤ ‖z‖ →
      Metric.ball z (‖z‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ →
      DifferentiableAt ℂ (Work.Pert.Xc d) z ∧
        ‖deriv (Work.Pert.Xc d) z - 1‖ ≤ 1 / 2 := by
  -- the two bounds of Appendix A.1: the derivative estimate and the nonvanishing of `φ₀`
  obtain ⟨C, hCpos, hXcur⟩ := Work.Pert.Ksub2.Xcurve_bounds d
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨RA, hRA⟩ := hasym 1 one_pos
  obtain ⟨RB, hRB⟩ := Work.Pert.exists_norm_add_clog_bound a b 1 one_pos
  -- `C * (1 + log x) ≤ x / 2` for all large `x`
  have hlog : (fun x : ℝ => Real.log x) =o[Filter.atTop] (id : ℝ → ℝ) :=
    Real.isLittleO_log_id_atTop
  have hf : (fun x : ℝ => C * Real.log x) =o[Filter.atTop] (id : ℝ → ℝ) := hlog.const_mul_left C
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, ‖C * Real.log x‖ ≤ (1 / 4 : ℝ) * ‖x‖ :=
    Asymptotics.isLittleO_iff.mp hf (c := (1 / 4 : ℝ)) (by norm_num)
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, C * (1 + Real.log x) ≤ x / 2 := by
    filter_upwards [h1, Filter.eventually_ge_atTop (max 1 (4 * C))] with x hx1 hx2
    have hxge1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx2
    have hxge : 4 * C ≤ x := le_trans (le_max_right _ _) hx2
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxge1
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxge1
    have hx1' : C * Real.log x ≤ x / 4 := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (le_of_lt hCpos) hlogx),
        abs_of_nonneg (le_of_lt hxpos)] at hx1
      linarith
    have hCx : C ≤ x / 4 := by linarith
    nlinarith [hx1', hCx]
  -- collect all the thresholds into one eventual statement
  have h3 : ∀ᶠ x : ℝ in Filter.atTop,
      C ≤ x ∧ (1 : ℝ) ≤ x ∧ (10 / 9) * (max RA RB + 1) ≤ x ∧
        C * (1 + Real.log x) ≤ x / 2 := by
    filter_upwards [h2, Filter.eventually_ge_atTop C, Filter.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop ((10 / 9) * (max RA RB + 1))] with x hx2 hxC hx1 hxAB
    exact ⟨hxC, hx1, hxAB, hx2⟩
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp h3
  refine ⟨max R₁ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hzQ hzR hball
  have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (le_max_right _ _) hzR
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz1
  obtain ⟨hzC, hz1', hzAB, hzbnd⟩ := hR₁ ‖z‖ (le_trans (le_max_left _ _) hzR)
  -- `φ₀` does not vanish on the ball: the asymptotic fights the coercivity bound on it
  have hφnz : ∀ w ∈ Metric.ball z (‖z‖ / 10), d.φ w ≠ 0 := by
    intro w hw hzero
    have hwn : 9 * ‖z‖ / 10 ≤ ‖w‖ := by
      have h1 : dist w z < ‖z‖ / 10 := Metric.mem_ball.mp hw
      rw [dist_eq_norm] at h1
      have h2 : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        have h := norm_add_le (z - w) w
        rwa [sub_add_cancel] at h
      have h3 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
      linarith
    have hwQ : w ∈ MandelDim.QLeft d.ξ₀ := hball hw
    have hMA : max RA RB + 1 ≤ ‖w‖ := by linarith
    have hRAw : RA < ‖w‖ := by
      have h : RA ≤ max RA RB := le_max_left _ _
      linarith
    have hRBw : RB ≤ ‖w‖ := by
      have h : RB ≤ max RA RB := le_max_right _ _
      linarith
    have hs := hRA w hwQ hRAw
    have hb := hRB w hRBw
    have hz' : MandelDim.tau0 (d.φ w) = 0 := by rw [hzero]; simp [MandelDim.tau0]
    rw [hz', zero_sub, norm_neg] at hs
    linarith
  have hφd : DifferentiableOn ℂ d.φ (Metric.ball z (‖z‖ / 10)) :=
    d.φ_holo.mono (fun w hw => d.Q_sub (hball hw))
  have hτ : DifferentiableOn ℂ MandelDim.tau0 ({0}ᶜ : Set ℂ) :=
    (differentiableOn_const (-1 : ℂ)).div differentiableOn_id (fun x hx => hx)
  have hXcd : DifferentiableOn ℂ (Work.Pert.Xc d) (Metric.ball z (‖z‖ / 10)) :=
    hτ.comp hφd (fun w hw => by simpa using hφnz w hw)
  refine ⟨hXcd.differentiableAt (Metric.ball_mem_nhds z (by linarith)), ?_⟩
  obtain ⟨-, hder⟩ := hXcur z hzQ hzC hball
  have hstep : C * (1 + Real.log ‖z‖) / ‖z‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hzpos]
    linarith
  linarith

end Work.PertCrux
