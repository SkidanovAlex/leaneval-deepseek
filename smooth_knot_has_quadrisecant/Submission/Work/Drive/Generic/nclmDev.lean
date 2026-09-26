import Mathlib
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Generic.interp_error_meanValue

/-!
# The second-order structure of the deviation of a retained arc

`Work.Drive.loopDev r D σ ξ` is the deviation of the point at fraction `ξ` of the retained arc at
sweep parameter `σ` from the corresponding point of the chord.  This module proves the *signed*,
second-order structure that the chart estimates of `Work.Drive.Generic.needleChartLoop_margin` use:

    ⟪loopDev (σ, ξ), z⟫ + (ξ (1-ξ)/2) * w(σ)² * ⟪r'' (taR σ), z⟫ = O (ξ (1-ξ) * w(σ)³)

for every *unit* `z`, where `w(σ) = sweepW' D σ`.  The margin is proved by the interpolation-error
mean-value formula `Work.Generic.interp_error_meanValue` applied to the scalar function
`y ↦ ⟪r y, z⟫`, together with a Lipschitz bound for `r''` near the collapsed end.

Two consequences are recorded:

* `nclm_dev_smul_sign` — with `⟪z, r''⟫ ≥ κ > 0` on the window's arcs, the pairing of the deviation
  with `z` is negative with the explicit margin `(ξ(1-ξ)/2) * w² * κ/2`;
* `nclm_dev_bound` — the *absolute* bound `|⟪loopDev, z⟫| ≤ (ξ(1-ξ)/2) * w² * K * w` whenever `z` is
  orthogonal to the acceleration at the collapsed end (this is the estimate that shows the chart
  direction is transverse).
-/

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData}

/-- **A Lipschitz bound for the acceleration.**  For an analytic knot the acceleration
`deriv (deriv r)` is Lipschitz on the whole line, with a constant given by a bound on the third
derivative. -/
lemma nclm_lipschitz_r'' {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, ‖deriv (deriv r) x - deriv (deriv r) y‖ ≤ C * |x - y| := by
  obtain ⟨B, hB0, hB⟩ := Work.Drive.exists_bound_iteratedDeriv_knot hr 3
  have hs : ContDiff ℝ cInfT r := hr.smooth.of_le le_top
  have hd : ContDiff ℝ cInfT (deriv (deriv r)) := by
    have h1 : ContDiff ℝ cInfT (deriv r) := ((contDiff_infty_iff_deriv (𝕜 := ℝ)).mp hs).2
    exact ((contDiff_infty_iff_deriv (𝕜 := ℝ)).mp h1).2
  have hderiv : ∀ x : ℝ, HasDerivAt (deriv (deriv r)) (deriv (deriv (deriv r)) x) x :=
    fun x => (hd.differentiable (by simp) x).hasDerivAt
  have hcont : Continuous (deriv (deriv (deriv r))) := hd.continuous_deriv (by simp)
  have hb : ∀ x : ℝ, ‖deriv (deriv (deriv r)) x‖ ≤ B := by
    intro x
    have h2 : iteratedDeriv 2 r = deriv (deriv r) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h3 : iteratedDeriv 3 r = deriv (deriv (deriv r)) := by
      rw [iteratedDeriv_succ, h2]
    rw [← h3]
    exact hB x
  refine ⟨B + 1, by linarith, ?_⟩
  intro x y
  rcases le_total x y with hxy | hyx
  · have hint : IntervalIntegrable (deriv (deriv (deriv r))) volume x y :=
      hcont.intervalIntegrable _ _
    have hftc : (∫ t in x..y, deriv (deriv (deriv r)) t)
        = deriv (deriv r) y - deriv (deriv r) x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
    rw [norm_sub_rev, ← hftc, abs_sub_comm,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
    calc ‖∫ t in x..y, deriv (deriv (deriv r)) t‖
        ≤ ∫ t in x..y, ‖deriv (deriv (deriv r)) t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hxy
      _ ≤ ∫ t in x..y, B := by
          refine intervalIntegral.integral_mono_on hxy ?_ ?_ ?_
          · exact hcont.norm.intervalIntegrable _ _
          · exact intervalIntegrable_const
          · intro t _; exact hb t
      _ = B * (y - x) := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      _ ≤ (B + 1) * (y - x) := by nlinarith [hB0]
  · have hint : IntervalIntegrable (deriv (deriv (deriv r))) volume y x :=
      hcont.intervalIntegrable _ _
    have hftc : (∫ t in y..x, deriv (deriv (deriv r)) t)
        = deriv (deriv r) x - deriv (deriv r) y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
    rw [← hftc, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
    calc ‖∫ t in y..x, deriv (deriv (deriv r)) t‖
        ≤ ∫ t in y..x, ‖deriv (deriv (deriv r)) t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hyx
      _ ≤ ∫ t in y..x, B := by
          refine intervalIntegral.integral_mono_on hyx ?_ ?_ ?_
          · exact hcont.norm.intervalIntegrable _ _
          · exact intervalIntegrable_const
          · intro t _; exact hb t
      _ = B * (x - y) := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      _ ≤ (B + 1) * (x - y) := by nlinarith [hB0]

/-- The second derivative of the scalar function `y ↦ ⟪r y, z⟫` is `⟪r'' y, z⟫`. -/
lemma nclm_deriv2_inner {r : ℝ → Space} (hr : IsSmoothKnot r) (z : Space) (y : ℝ) :
    deriv (deriv (fun t : ℝ => inner ℝ (r t) z)) y
      = inner ℝ (deriv (deriv r) y) z := by
  have hs : ContDiff ℝ cInfT r := hr.smooth.of_le le_top
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ (deriv r) t := by
    have h1 : ContDiff ℝ cInfT (deriv r) := ((contDiff_infty_iff_deriv (𝕜 := ℝ)).mp hs).2
    exact fun t => (h1.differentiable (by simp)) t
  have hderiv1 : deriv (fun t : ℝ => inner ℝ (r t) z) = fun t => inner ℝ (velocity r t) z := by
    funext t
    have h1 : HasDerivAt r (velocity r t) t :=
      ((hr.smooth.differentiable (by simp)) t).hasDerivAt
    have h2 := h1.inner ℝ (hasDerivAt_const (x := t) (c := z))
    rw [h2.deriv]
    simp [inner_zero_right, inner_add_right]
  rw [hderiv1]
  have hderiv2 : deriv (fun t : ℝ => inner ℝ (velocity r t) z)
      = fun t => inner ℝ (deriv (velocity r) t) z := by
    funext t
    have h1 : HasDerivAt (velocity r) (deriv (velocity r) t) t := (hdiff t).hasDerivAt
    have h2 := h1.inner ℝ (hasDerivAt_const (x := t) (c := z))
    rw [h2.deriv]
    simp [inner_zero_right, inner_add_right]
  rw [hderiv2]
  rfl

/-- **The signed second-order structure of the deviation.**  For every unit `z` there are `ε₀ > 0`
and `C > 0` such that, for every retained arc in the window of radius `ε ≤ ε₀`,

    |⟪loopDev (σ, ξ), z⟫ + (ξ (1-ξ)/2) * w² * ⟪r'' (taR σ), z⟫| ≤ (ξ (1-ξ)/2) * w² * (C * w).

In particular the deviation is, up to a *relative* error `O (w)`, the second-order term
`-(ξ (1-ξ)/2) * w² * r'' (taR σ)`. -/
theorem nclm_dev_scalar {d : BandArcData} (D : Work.Drive.SweepData d) {r : ℝ → Space}
    (hr : IsSmoothKnot r) (z : Space) (hz : ‖z‖ = 1) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < C ∧
      ∀ (σ ξ : ℝ), 0 < σ → σ < 1 → σ ≤ ε₀ → ξ ∈ Set.Icc (0 : ℝ) 1 →
        |inner ℝ (Work.Drive.loopDev r D σ ξ) z
            + (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 *
              inner ℝ (deriv (deriv r) (Work.Drive.taR D σ)) z|
          ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * (C * Work.Drive.sweepW' D σ) := by
  obtain ⟨C₀, hC₀, hLip⟩ := nclm_lipschitz_r'' hr
  refine ⟨1 / 2, C₀, by norm_num, le_rfl, hC₀, ?_⟩
  intro σ ξ hσ0 hσ1 hσε hξ
  have hwpos : 0 < Work.Drive.sweepW' D σ := by
    have h : 0 < Work.Drive.sweepW D (⟨σ, ⟨hσ0.le, hσ1.le⟩⟩ : Set.Icc (0:ℝ) 1) :=
      (Work.Drive.sweepW_pos_lt D _ ⟨hσ0, hσ1⟩).1
    rw [Work.Drive.sweepW', Work.Drive.taR, Work.Drive.tbR, wds_clampI_eq hσ0.le hσ1.le]
    exact h
  have hf : ContDiff ℝ 2 (fun t : ℝ => inner ℝ (r t) z) := by
    have h1 : ContDiff ℝ 2 r := hr.smooth.of_le le_top
    exact ContDiff.inner ℝ h1 contDiff_const
  have hba : Work.Drive.taR D σ < Work.Drive.taR D σ + Work.Drive.sweepW' D σ := by linarith
  obtain ⟨ζ, hζ, hζeq⟩ := Work.Generic.interp_error_meanValue
    (a := Work.Drive.taR D σ) (b := Work.Drive.taR D σ + Work.Drive.sweepW' D σ) (ξ := ξ)
    (f := fun t : ℝ => inner ℝ (r t) z) hba hξ hf
  have hdev : inner ℝ (Work.Drive.loopDev r D σ ξ) z
      = inner ℝ (r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) z
        - ((1 - ξ) * inner ℝ (r (Work.Drive.taR D σ)) z
            + ξ * inner ℝ (r (Work.Drive.taR D σ + Work.Drive.sweepW' D σ)) z) := by
    have h1 : Work.Drive.loopDev r D σ ξ = r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)
        - ((1 - ξ) • r (Work.Drive.taR D σ) + ξ • r (Work.Drive.tbR D σ)) := rfl
    have h2 : Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ := by
      rw [Work.Drive.sweepW']; ring
    rw [h1, h2, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
      RCLike.conj_to_real, RCLike.conj_to_real]
  have hζeq' : inner ℝ (r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) z
      - ((1 - ξ) * inner ℝ (r (Work.Drive.taR D σ)) z
          + ξ * inner ℝ (r (Work.Drive.taR D σ + Work.Drive.sweepW' D σ)) z)
      = -((ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2
          * inner ℝ (deriv (deriv r) ζ) z) := by
    have h := hζeq
    rw [show Work.Drive.taR D σ + ξ * (Work.Drive.taR D σ + Work.Drive.sweepW' D σ
          - Work.Drive.taR D σ) = Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ from by ring,
      show Work.Drive.taR D σ + Work.Drive.sweepW' D σ - Work.Drive.taR D σ
        = Work.Drive.sweepW' D σ from by ring, nclm_deriv2_inner hr z ζ] at h
    exact h
  have hmain : inner ℝ (Work.Drive.loopDev r D σ ξ) z
      = -((ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2
          * inner ℝ (deriv (deriv r) ζ) z) := by
    rw [hdev, hζeq']
  have hnn : (0:ℝ) ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 := by
    have h1 : 0 ≤ ξ * (1 - ξ) := mul_nonneg hξ.1 (by linarith [hξ.2])
    positivity
  have hkey : |inner ℝ (Work.Drive.loopDev r D σ ξ) z
      + (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 *
        inner ℝ (deriv (deriv r) (Work.Drive.taR D σ)) z|
      = (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 *
        |inner ℝ (deriv (deriv r) (Work.Drive.taR D σ)) z
          - inner ℝ (deriv (deriv r) ζ) z| := by
    rw [hmain]
    rw [show -((ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * inner ℝ (deriv (deriv r) ζ) z)
        + (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 *
          inner ℝ (deriv (deriv r) (Work.Drive.taR D σ)) z
        = (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 *
          (inner ℝ (deriv (deriv r) (Work.Drive.taR D σ)) z
            - inner ℝ (deriv (deriv r) ζ) z) from by ring]
    rw [abs_mul, abs_of_nonneg hnn]
  have hdiff : |inner ℝ (deriv (deriv r) (Work.Drive.taR D σ)) z
      - inner ℝ (deriv (deriv r) ζ) z| ≤ C₀ * Work.Drive.sweepW' D σ := by
    have h1 : inner ℝ (deriv (deriv r) (Work.Drive.taR D σ)) z
        - inner ℝ (deriv (deriv r) ζ) z
        = inner ℝ (deriv (deriv r) (Work.Drive.taR D σ) - deriv (deriv r) ζ) z := by
      rw [inner_sub_left]
    rw [h1]
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    rw [hz, mul_one]
    refine le_trans (hLip _ _) ?_
    have hb : Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ := by
      rw [Work.Drive.sweepW']; ring
    rw [abs_of_nonpos (by linarith [hζ.1] : Work.Drive.taR D σ - ζ ≤ 0)]
    have hle : -(Work.Drive.taR D σ - ζ) ≤ Work.Drive.sweepW' D σ := by linarith [hζ.2]
    exact mul_le_mul_of_nonneg_left hle hC₀.le
  rw [hkey]
  exact mul_le_mul_of_nonneg_left hdiff hnn

/-- **The deviation, against an arbitrary direction, in absolute value.**  This is the raw form of
`nclm_dev_scalar` (no fixed direction: the bound on `r''` along the arc is a hypothesis), which is
what a direction that depends on the box (the needle's chord direction `v`) needs. -/
theorem nclm_dev_scalar_le {d : BandArcData} (D : Work.Drive.SweepData d) {r : ℝ → Space}
    (hr : IsSmoothKnot r) {y : Space} {B σ ξ : ℝ} (hw : 0 < Work.Drive.sweepW' D σ)
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1)
    (hbdd : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
      |inner ℝ (deriv (deriv r) x) y| ≤ B) :
    |inner ℝ (Work.Drive.loopDev r D σ ξ) y| ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * B := by
  have hf : ContDiff ℝ 2 (fun t : ℝ => inner ℝ (r t) y) := by
    have h1 : ContDiff ℝ 2 r := hr.smooth.of_le le_top
    exact ContDiff.inner ℝ h1 contDiff_const
  have hba : Work.Drive.taR D σ < Work.Drive.taR D σ + Work.Drive.sweepW' D σ := by linarith
  obtain ⟨ζ, hζ, hζeq⟩ := Work.Generic.interp_error_meanValue
    (a := Work.Drive.taR D σ) (b := Work.Drive.taR D σ + Work.Drive.sweepW' D σ) (ξ := ξ)
    (f := fun t : ℝ => inner ℝ (r t) y) hba hξ hf
  have hdev : inner ℝ (Work.Drive.loopDev r D σ ξ) y
      = inner ℝ (r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) y
        - ((1 - ξ) * inner ℝ (r (Work.Drive.taR D σ)) y
            + ξ * inner ℝ (r (Work.Drive.taR D σ + Work.Drive.sweepW' D σ)) y) := by
    have h1 : Work.Drive.loopDev r D σ ξ = r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)
        - ((1 - ξ) • r (Work.Drive.taR D σ) + ξ • r (Work.Drive.tbR D σ)) := rfl
    have h2 : Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ := by
      rw [Work.Drive.sweepW']; ring
    rw [h1, h2, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
      RCLike.conj_to_real, RCLike.conj_to_real]
  have hmain : inner ℝ (Work.Drive.loopDev r D σ ξ) y
      = -((ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2
          * inner ℝ (deriv (deriv r) ζ) y) := by
    rw [hdev]
    have h := hζeq
    rw [show Work.Drive.taR D σ + ξ * (Work.Drive.taR D σ + Work.Drive.sweepW' D σ
          - Work.Drive.taR D σ) = Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ from by ring,
      show Work.Drive.taR D σ + Work.Drive.sweepW' D σ - Work.Drive.taR D σ
        = Work.Drive.sweepW' D σ from by ring, nclm_deriv2_inner hr y ζ] at h
    rw [← h]
  rw [hmain, abs_neg, abs_mul]
  have hnn : (0:ℝ) ≤ ξ * (1 - ξ) / 2 * (Work.Drive.sweepW' D σ) ^ 2 := by
    have h1 : 0 ≤ ξ * (1 - ξ) := mul_nonneg hξ.1 (by linarith [hξ.2])
    positivity
  rw [abs_of_nonneg hnn]
  refine mul_le_mul_of_nonneg_left ?_ hnn
  have hb := hbdd ζ (by
    rw [show Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ from by
      rw [Work.Drive.sweepW']; ring] at hζ
    exact ⟨le_of_lt hζ.1, le_of_lt hζ.2⟩)
  exact hb

/-- **The deviation, against an arbitrary direction, with a *sign*** (and the explicit margin). -/
theorem nclm_dev_scalar_ge {d : BandArcData} (D : Work.Drive.SweepData d) {r : ℝ → Space}
    (hr : IsSmoothKnot r) {y : Space} {c σ ξ : ℝ} (hw : 0 < Work.Drive.sweepW' D σ)
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1)
    (hbdd : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
      inner ℝ (deriv (deriv r) x) y ≤ -c) :
    (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * c
      ≤ inner ℝ (Work.Drive.loopDev r D σ ξ) y := by
  -- the same identity as above, with the sign of the mean value
  have hf : ContDiff ℝ 2 (fun t : ℝ => inner ℝ (r t) y) := by
    have h1 : ContDiff ℝ 2 r := hr.smooth.of_le le_top
    exact ContDiff.inner ℝ h1 contDiff_const
  have hba : Work.Drive.taR D σ < Work.Drive.taR D σ + Work.Drive.sweepW' D σ := by linarith
  obtain ⟨ζ, hζ, hζeq⟩ := Work.Generic.interp_error_meanValue
    (a := Work.Drive.taR D σ) (b := Work.Drive.taR D σ + Work.Drive.sweepW' D σ) (ξ := ξ)
    (f := fun t : ℝ => inner ℝ (r t) y) hba hξ hf
  have hdev : inner ℝ (Work.Drive.loopDev r D σ ξ) y
      = inner ℝ (r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) y
        - ((1 - ξ) * inner ℝ (r (Work.Drive.taR D σ)) y
            + ξ * inner ℝ (r (Work.Drive.taR D σ + Work.Drive.sweepW' D σ)) y) := by
    have h1 : Work.Drive.loopDev r D σ ξ = r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)
        - ((1 - ξ) • r (Work.Drive.taR D σ) + ξ • r (Work.Drive.tbR D σ)) := rfl
    have h2 : Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ := by
      rw [Work.Drive.sweepW']; ring
    rw [h1, h2, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
      RCLike.conj_to_real, RCLike.conj_to_real]
  have hmain : inner ℝ (Work.Drive.loopDev r D σ ξ) y
      = -((ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2
          * inner ℝ (deriv (deriv r) ζ) y) := by
    rw [hdev]
    have h := hζeq
    rw [show Work.Drive.taR D σ + ξ * (Work.Drive.taR D σ + Work.Drive.sweepW' D σ
          - Work.Drive.taR D σ) = Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ from by ring,
      show Work.Drive.taR D σ + Work.Drive.sweepW' D σ - Work.Drive.taR D σ
        = Work.Drive.sweepW' D σ from by ring, nclm_deriv2_inner hr y ζ] at h
    rw [← h]
  rw [hmain]
  have hζmem : ζ ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) := by
    have h2 : Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ := by
      rw [Work.Drive.sweepW']; ring
    rw [h2] at hζ
    exact ⟨le_of_lt hζ.1, le_of_lt hζ.2⟩
  have hstep := hbdd ζ hζmem
  have hnn : (0:ℝ) ≤ ξ * (1 - ξ) / 2 * (Work.Drive.sweepW' D σ) ^ 2 := by
    have h1 : 0 ≤ ξ * (1 - ξ) := mul_nonneg hξ.1 (by linarith [hξ.2])
    positivity
  nlinarith [hstep, hnn]

end Work.Drive.Generic
