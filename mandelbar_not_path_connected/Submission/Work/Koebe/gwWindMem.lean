import Mathlib
import Submission.Work.Koebe.gwDefs
import Submission.Work.Area.circleIntegral_deriv_div_eq_zero
import Submission.Work.Area.circleIntegral_deriv_div_eq_two_pi_I
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Koebe

open Complex Metric Set MeasureTheory
open scoped Topology

/-- **Winding-number membership for a univalent expansion.**

Let `F z = 1/z + H z` on the punctured unit disc, with `H` holomorphic on the disc and `F`
injective there.  For `0 < r < 1` and `z` outside the curve `F '' (|z| = r)`:

* the winding number of the curve `θ ↦ F (r e^{iθ})` around `z` is `-1` or `0`;
* it is `-1` exactly for those `z` lying *outside* the region `F ({0 < |z| < r})`, i.e. for the
  points enclosed by the curve.

The proof writes `F w - z = h w / w` with `h w = 1 + w (H w - z)` holomorphic on the disc, so the
integrand of `winding` is the logarithmic derivative of `h` minus `1/w`.  Since `F` is univalent,
`h` has at most one zero in the disc, and that zero is simple
(`Work.ELRig.deriv_ne_zero_of_injOn`), so the two special cases of the argument principle
`Work.Area.circleIntegral_deriv_div_eq_zero` and
`Work.Area.circleIntegral_deriv_div_eq_two_pi_I` determine the integral. -/
theorem gwWindMem (F H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hF : Set.InjOn F (Metric.ball 0 1 \ {0}))
    (hexp : ∀ z ∈ Metric.ball 0 1 \ {0}, F z = 1 / z + H z)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : z ∉ F '' (Metric.sphere 0 r)) :
    (Work.Koebe.winding F r z = -1 ∨ Work.Koebe.winding F r z = 0) ∧
      (Work.Koebe.winding F r z = -1 ↔ z ∉ F '' {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < r}) := by
  set D : Set ℂ := Metric.ball 0 1 \ {0} with hD
  have hDopen : IsOpen D := Metric.isOpen_ball.sdiff isClosed_singleton
  -- `F` is holomorphic on the punctured disc.
  have hFd : DifferentiableOn ℂ F D := by
    refine ((differentiableOn_id.inv ?_).add (hH.mono ?_)).congr ?_
    · intro w hw; exact hw.2
    · intro w hw; exact hw.1
    · intro w hw
      have h := hexp w hw
      rw [one_div] at h
      exact h
  -- and its derivative is the derivative of its explicit expression.
  have hderivF : ∀ w ∈ D, deriv F w = -(w ^ 2)⁻¹ + deriv H w := by
    intro w hw
    have hw1 : w ∈ Metric.ball (0 : ℂ) 1 := hw.1
    have hw0 : w ≠ 0 := hw.2
    have hev : F =ᶠ[𝓝 w] fun u : ℂ => u⁻¹ + H u := by
      filter_upwards [hDopen.mem_nhds hw] with u hu
      have h := hexp u hu
      rw [one_div] at h
      exact h
    rw [hev.deriv_eq]
    have h2 : deriv (fun u : ℂ => u⁻¹ + H u) w
        = deriv (fun u : ℂ => u⁻¹) w + deriv H w :=
      deriv_add (differentiableAt_id.inv hw0)
        (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hw1))
    rw [h2, deriv_inv]
  -- The holomorphic function `h w = 1 + w (H w - z)`; note `h w = w (F w - z)` for `w ≠ 0`.
  set h : ℂ → ℂ := fun w => 1 + w * (H w - z) with hhdef
  have hhd : DifferentiableOn ℂ h (Metric.ball 0 1) := by
    rw [hhdef]
    exact (differentiableOn_const (c := (1 : ℂ))).add
      (differentiableOn_id.mul (hH.sub_const z))
  have hh0 : h 0 = 1 := by simp [hhdef]
  have hh_eq : ∀ w ∈ D, h w = w * (F w - z) := by
    intro w hw
    have hw0 : w ≠ 0 := hw.2
    have h := hexp w hw
    rw [one_div] at h
    show 1 + w * (H w - z) = w * (F w - z)
    rw [h]
    field_simp
    ring
  -- elementary facts about the circle `|w| = r`
  have hsp_norm : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖w‖ = r := by
    intro w hw
    simpa [Metric.mem_sphere, dist_zero_right] using hw
  have hsp_ne : ∀ w ∈ Metric.sphere (0 : ℂ) r, w ≠ 0 := by
    intro w hw h0
    have hwn := hsp_norm w hw
    rw [h0] at hwn
    simp only [norm_zero] at hwn
    linarith
  have hsp_D : ∀ w ∈ Metric.sphere (0 : ℂ) r, w ∈ D := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hsp_norm w hw]
      exact hr1
    · simp only [Set.mem_singleton_iff]
      exact hsp_ne w hw
  have hsp_h_ne : ∀ w ∈ Metric.sphere (0 : ℂ) r, h w ≠ 0 := by
    intro w hw
    rw [hh_eq w (hsp_D w hw)]
    refine mul_ne_zero (hsp_ne w hw) (sub_ne_zero.mpr ?_)
    intro hcon
    exact hz ⟨w, hw, hcon⟩
  -- the pointwise identity for the integrand on the circle
  have hident : ∀ w ∈ Metric.sphere (0 : ℂ) r,
      deriv F w / (F w - z) = deriv h w / h w - w⁻¹ := by
    intro w hw
    rw [div_eq_mul_inv, mul_comm]
    have hw0 : w ≠ 0 := hsp_ne w hw
    have hwD : w ∈ D := hsp_D w hw
    have hFwz : F w - z ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      exact hz ⟨w, hw, hcon⟩
    have hFw : F w = w⁻¹ + H w := by
      have h := hexp w hwD
      rw [one_div] at h
      exact h
    have hdh : deriv h w = (H w - z) + w * deriv H w := by
      have hHu : DifferentiableAt ℂ (fun u : ℂ => H u - z) w :=
        (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hwD.1)).sub_const z
      have hid : DifferentiableAt ℂ (fun u : ℂ => u) w := differentiableAt_id
      rw [hhdef]
      change deriv (fun u : ℂ => 1 + u * (H u - z)) w = (H w - z) + w * deriv H w
      rw [deriv_const_add,
        show (fun u : ℂ => u * (H u - z)) = (fun u : ℂ => u) * (fun u : ℂ => H u - z)
          from rfl,
        deriv_mul hid hHu,
        show deriv (fun u : ℂ => u) w = 1 from (hasDerivAt_id' (x := w)).deriv,
        show deriv (fun u : ℂ => H u - z) w = deriv H w from
          ((hH.differentiableAt (Metric.isOpen_ball.mem_nhds hwD.1)).hasDerivAt.sub_const z).deriv]
      ring
    have hstep : deriv h w = w * deriv F w + (F w - z) := by
      rw [hdh, hderivF w hwD, hFw]
      field_simp
      ring
    rw [hstep, hh_eq w hwD]
    field_simp
    ring
  -- integral bookkeeping
  have hderiv_h_cont : ContinuousOn (deriv h) (Metric.sphere (0 : ℂ) r) :=
    (hhd.deriv Metric.isOpen_ball).continuousOn.mono fun w hw => (hsp_D w hw).1
  have hh_cont : ContinuousOn h (Metric.sphere (0 : ℂ) r) :=
    hhd.continuousOn.mono fun w hw => (hsp_D w hw).1
  have hci1 : CircleIntegrable (fun w : ℂ => deriv h w / h w) 0 r :=
    ((hderiv_h_cont.div hh_cont fun w hw => hsp_h_ne w hw)).circleIntegrable hr.le
  have hci2 : CircleIntegrable (fun w : ℂ => w⁻¹) 0 r :=
    ((continuousOn_id.inv₀ fun w hw => hsp_ne w hw)).circleIntegrable hr.le
  have hstep2 : circleIntegral (fun w : ℂ => deriv h w / h w - w⁻¹) 0 r
      = circleIntegral (fun w : ℂ => deriv h w / h w) 0 r - 2 * (Real.pi : ℂ) * Complex.I := by
    rw [circleIntegral.integral_sub hci1 hci2]
    congr 1
    simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) (ne_of_gt hr)
  have hwind_eq : winding F r z = (2 * Real.pi * Complex.I)⁻¹ *
      (circleIntegral (fun w : ℂ => deriv h w / h w) 0 r - 2 * (Real.pi : ℂ) * Complex.I) := by
    have h1 : circleIntegral (fun w : ℂ => deriv F w / (F w - z)) 0 r
        = circleIntegral (fun w : ℂ => deriv h w / h w - w⁻¹) 0 r :=
      circleIntegral.integral_congr hr.le fun w hw => hident w hw
    rw [winding, h1, hstep2]
  -- `h` vanishes on the closed disc exactly when `z` lies in the image of the punctured disc
  have himg_iff : (∃ w ∈ Metric.closedBall (0 : ℂ) r, h w = 0) ↔
      z ∈ F '' {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < r} := by
    constructor
    · rintro ⟨p, hp_mem, hp0⟩
      have hp0ne : p ≠ 0 := by
        intro h0
        rw [h0, hh0] at hp0
        exact one_ne_zero hp0
      have hpnorm : ‖p‖ < r := by
        have hle : ‖p‖ ≤ r := by
          have h := hp_mem
          rwa [Metric.mem_closedBall, dist_zero_right] at h
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exfalso
          have hsp : p ∈ Metric.sphere (0 : ℂ) r := by
            rw [Metric.mem_sphere, dist_zero_right, h]
          exact hsp_h_ne p hsp hp0
      have hpD : p ∈ D :=
        ⟨by rw [Metric.mem_ball, dist_zero_right]; linarith, by simp [hp0ne]⟩
      refine ⟨p, ⟨by rw [norm_pos_iff]; exact hp0ne, hpnorm⟩, ?_⟩
      have hh := hh_eq p hpD
      rw [hp0] at hh
      rcases mul_eq_zero.mp hh.symm with h1 | h1
      · exact absurd h1 hp0ne
      · exact sub_eq_zero.mp h1
    · rintro ⟨p, ⟨hp0, hpr⟩, hpF⟩
      refine ⟨p, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact le_of_lt hpr
      · have hpD : p ∈ D :=
          ⟨by rw [Metric.mem_ball, dist_zero_right]; linarith, norm_pos_iff.mp hp0⟩
        rw [hh_eq p hpD, hpF, sub_self, mul_zero]
  by_cases hcase : ∀ w ∈ Metric.closedBall (0 : ℂ) r, h w ≠ 0
  · -- no zero on the closed disc: only the pole at `0` contributes, `winding = -1`
    have hzero := Work.Area.circleIntegral_deriv_div_eq_zero hr hr1 hhd hcase
    have hval : winding F r z = -1 := by
      rw [hwind_eq, hzero, zero_sub, mul_neg, inv_mul_cancel₀ Complex.two_pi_I_ne_zero]
    have hno : ¬ ∃ w ∈ Metric.closedBall (0 : ℂ) r, h w = 0 :=
      by rintro ⟨w, hw, hw0⟩; exact hcase w hw hw0
    have hnotim : z ∉ F '' {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < r} :=
      fun hmem => hno (himg_iff.mpr hmem)
    exact ⟨Or.inl hval, ⟨fun _ => hnotim, fun _ => hval⟩⟩
  · -- one simple zero at an interior point `p`: `winding = 0`
    push Not at hcase
    obtain ⟨p, hp_mem, hp_zero⟩ := hcase
    have hp0_ne : p ≠ 0 := by
      intro h0
      rw [h0, hh0] at hp_zero
      exact one_ne_zero hp_zero
    have hp_ball : p ∈ Metric.ball (0 : ℂ) r := by
      have hle : dist p 0 ≤ r := hp_mem
      have hne : dist p 0 ≠ r := by
        intro hd
        exact hsp_h_ne p (by rwa [Metric.mem_sphere]) hp_zero
      exact Metric.mem_ball.mpr (lt_of_le_of_ne hle hne)
    have hp_D : p ∈ D :=
      ⟨Metric.ball_subset_ball hr1.le hp_ball, by simp [hp0_ne]⟩
    have hpF : F p = z := by
      have h := hh_eq p hp_D
      rw [hp_zero] at h
      rcases mul_eq_zero.mp h.symm with h1 | h1
      · exact absurd h1 hp0_ne
      · exact sub_eq_zero.mp h1
    have huniq : ∀ w ∈ Metric.closedBall (0 : ℂ) r, h w = 0 → w = p := by
      intro w hw hhw
      have hwball : w ∈ Metric.ball (0 : ℂ) 1 := by
        have hle : ‖w‖ ≤ r := by
          have h := hw
          rwa [Metric.mem_closedBall, dist_zero_right] at h
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, hh0] at hhw
        exact one_ne_zero hhw
      have hwD : w ∈ D := ⟨hwball, by simp [hw0]⟩
      have hFw : F w = z := by
        have h := hh_eq w hwD
        rw [hhw] at h
        rcases mul_eq_zero.mp h.symm with h1 | h1
        · exact absurd h1 hw0
        · exact sub_eq_zero.mp h1
      exact hF hwD hp_D (by rw [hFw, hpF])
    have hpderiv : deriv h p ≠ 0 := by
      have hp_at : DifferentiableAt ℂ F p :=
        (hFd p hp_D).differentiableAt (hDopen.mem_nhds hp_D)
      have hev : h =ᶠ[𝓝 p] fun w : ℂ => w * (F w - z) := by
        filter_upwards [hDopen.mem_nhds hp_D] with w hw
        exact hh_eq w hw
      have hderiv : deriv h p = p * deriv F p := by
        have hFz : DifferentiableAt ℂ (fun u : ℂ => F u - z) p := hp_at.sub_const z
        have hid : DifferentiableAt ℂ (fun u : ℂ => u) p := differentiableAt_id
        rw [hev.deriv_eq,
          show (fun u : ℂ => u * (F u - z)) = (fun u : ℂ => u) * (fun u : ℂ => F u - z)
            from rfl,
          deriv_mul hid hFz,
          show deriv (fun u : ℂ => u) p = 1 from (hasDerivAt_id' (x := p)).deriv,
          show deriv (fun u : ℂ => F u - z) p = deriv F p from
            (hp_at.hasDerivAt.sub_const z).deriv,
          hpF]
        ring
      rw [hderiv]
      exact mul_ne_zero hp0_ne (Work.ELRig.deriv_ne_zero_of_injOn hFd hDopen hF hp_D)
    have hpi : circleIntegral (fun w : ℂ => deriv h w / h w) 0 r
        = 2 * (Real.pi : ℂ) * Complex.I :=
      Work.Area.circleIntegral_deriv_div_eq_two_pi_I hr hr1 hhd hp_ball hp_zero hpderiv huniq
    have hval : winding F r z = 0 := by
      rw [hwind_eq, hpi, sub_self, mul_zero]
    have him : z ∈ F '' {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < r} :=
      himg_iff.mp ⟨p, hp_mem, hp_zero⟩
    refine ⟨Or.inr hval, ⟨fun h => ?_, fun hnot => absurd him hnot⟩⟩
    rw [hval] at h
    exact absurd h (by norm_num)

end Work.Koebe
