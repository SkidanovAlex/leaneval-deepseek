import Mathlib
import Submission.Work.EQ.CycleDefs

/-!
The requested statement text is reproduced verbatim below (it contains the binder name `hλ`,
which is not a valid Lean identifier in this toolchain: `Char.isAlpha '\u03bb' = false`, so
`hλ` cannot be lexed as one identifier).  The declaration itself uses the equivalent binder
name `hlam`; binder names are not part of a declaration's type.
-/

/-
theorem eq_of_fan_comp_eq {a : ℝ} {h : ℂ → ℂ} {η : List Bool} {N : ℕ} {c c' : ℂ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hλ : Work.EQ.eqLam a ≠ 0) {δf : ℝ} (hδf : 0 < δf)
    (han : AnalyticOnNhd ℂ (Work.EQ.fan a h η) (Metric.ball 0 δf))
    (hderiv : deriv (fun u => (Work.EQ.fan a h η u).2) 0 ≠ 0)
    {B : Set ℂ} (hB : IsOpen B) (hBne : B.Nonempty)
    (hB1 : ∀ w ∈ B, w ≠ 0 ∧ ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c / w)‖ < δf)
    (hB2 : ∀ w ∈ B, ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c' / w)‖ < δf)
    (heq : ∀ w ∈ B, Work.EQ.fan a h η (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c / w)) =
                        Work.EQ.fan a h η (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c' / w))) : c = c' := by
-/

def _requestedStatementText : String := "
theorem eq_of_fan_comp_eq {a : ℝ} {h : ℂ → ℂ} {η : List Bool} {N : ℕ} {c c' : ℂ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hλ : Work.EQ.eqLam a ≠ 0) {δf : ℝ} (hδf : 0 < δf)
    (han : AnalyticOnNhd ℂ (Work.EQ.fan a h η) (Metric.ball 0 δf))
    (hderiv : deriv (fun u => (Work.EQ.fan a h η u).2) 0 ≠ 0)
    {B : Set ℂ} (hB : IsOpen B) (hBne : B.Nonempty)
    (hB1 : ∀ w ∈ B, w ≠ 0 ∧ ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c / w)‖ < δf)
    (hB2 : ∀ w ∈ B, ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c' / w)‖ < δf)
    (heq : ∀ w ∈ B, Work.EQ.fan a h η (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c / w)) =
                        Work.EQ.fan a h η (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c' / w))) : c = c' := by
"

namespace Work.EQ

open Complex Filter _root_.Topology

open scoped Topology

theorem eq_of_fan_comp_eq {a : ℝ} {h : ℂ → ℂ} {η : List Bool} {N : ℕ} {c c' : ℂ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hlam : Work.EQ.eqLam a ≠ 0) {δf : ℝ} (hδf : 0 < δf)
    (han : AnalyticOnNhd ℂ (Work.EQ.fan a h η) (Metric.ball 0 δf))
    (hderiv : deriv (fun u => (Work.EQ.fan a h η u).2) 0 ≠ 0)
    {B : Set ℂ} (hB : IsOpen B) (hBne : B.Nonempty)
    (hB1 : ∀ w ∈ B, w ≠ 0 ∧ ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c / w)‖ < δf)
    (hB2 : ∀ w ∈ B, ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c' / w)‖ < δf)
    (heq : ∀ w ∈ B, Work.EQ.fan a h η (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c / w)) =
                        Work.EQ.fan a h η (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (c' / w))) : c = c' := by
  let μ : ℂ := ((eqLam a : ℝ) : ℂ) ^ N
  have hμ : μ ≠ 0 := pow_ne_zero N (Complex.ofReal_ne_zero.mpr hlam)
  obtain ⟨w0, hw0B⟩ := hBne
  have hw0ne : w0 ≠ 0 := (hB1 w0 hw0B).1
  set z0 : ℂ := μ / w0 with hz0def
  have hz0ne : z0 ≠ 0 := by rw [hz0def]; exact div_ne_zero hμ hw0ne
  set R : ℝ := min (δf / ‖c‖) (δf / ‖c'‖) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact lt_min (div_pos hδf (norm_pos_iff.mpr hc)) (div_pos hδf (norm_pos_iff.mpr hc'))
  have hc_an : AnalyticOnNhd ℂ (fun z : ℂ => c * z) (Metric.ball 0 R) :=
    (analyticOnNhd_const (v := c)).mul analyticOnNhd_id
  have hc'an : AnalyticOnNhd ℂ (fun z : ℂ => c' * z) (Metric.ball 0 R) :=
    (analyticOnNhd_const (v := c')).mul analyticOnNhd_id
  have hmapc : Set.MapsTo (fun z : ℂ => c * z) (Metric.ball 0 R) (Metric.ball 0 δf) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc ‖c * z‖ = ‖c‖ * ‖z‖ := norm_mul c z
      _ < ‖c‖ * R := mul_lt_mul_of_pos_left hz (norm_pos_iff.mpr hc)
      _ ≤ ‖c‖ * (δf / ‖c‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
            rw [hRdef]; exact min_le_left _ _
      _ = δf := by rw [← mul_div_assoc, mul_div_cancel_left₀ δf (norm_ne_zero_iff.mpr hc)]
  have hmapc' : Set.MapsTo (fun z : ℂ => c' * z) (Metric.ball 0 R) (Metric.ball 0 δf) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc ‖c' * z‖ = ‖c'‖ * ‖z‖ := norm_mul c' z
      _ < ‖c'‖ * R := mul_lt_mul_of_pos_left hz (norm_pos_iff.mpr hc')
      _ ≤ ‖c'‖ * (δf / ‖c'‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg c')
            rw [hRdef]; exact min_le_right _ _
      _ = δf := by rw [← mul_div_assoc, mul_div_cancel_left₀ δf (norm_ne_zero_iff.mpr hc')]
  have hFan : AnalyticOnNhd ℂ (fun z : ℂ => fan a h η (c * z)) (Metric.ball 0 R) :=
    han.comp hc_an hmapc
  have hFan' : AnalyticOnNhd ℂ (fun z : ℂ => fan a h η (c' * z)) (Metric.ball 0 R) :=
    han.comp hc'an hmapc'
  have hz0r : z0 = ((eqLam a : ℝ) : ℂ) ^ N / w0 := by rw [hz0def]
  have hz0_c : ‖c * z0‖ < δf := by
    have hh := (hB1 w0 hw0B).2
    have he : ((eqLam a : ℝ) : ℂ) ^ N * (c / w0) = c * z0 := by
      rw [hz0r, div_eq_mul_inv, div_eq_mul_inv]; ring
    rwa [he] at hh
  have hz0_c' : ‖c' * z0‖ < δf := by
    have hh := (hB2 w0 hw0B)
    have he : ((eqLam a : ℝ) : ℂ) ^ N * (c' / w0) = c' * z0 := by
      rw [hz0r, div_eq_mul_inv, div_eq_mul_inv]; ring
    rwa [he] at hh
  have hz0mem : z0 ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, hRdef]
    apply lt_min
    · have hh := hz0_c; rw [norm_mul] at hh
      rw [lt_div_iff₀ (norm_pos_iff.mpr hc)]; rwa [mul_comm]
    · have hh := hz0_c'; rw [norm_mul] at hh
      rw [lt_div_iff₀ (norm_pos_iff.mpr hc')]; rwa [mul_comm]
  have hfreq : (fun z : ℂ => fan a h η (c * z)) =ᶠ[𝓝 z0]
      (fun z : ℂ => fan a h η (c' * z)) := by
    have hz0val : μ / z0 = w0 := by
      rw [hz0def, div_div_eq_mul_div]
      exact mul_div_cancel_left₀ w0 hμ
    have hcont : ContinuousAt (fun z : ℂ => μ / z) z0 := by fun_prop
    have hmem1 : ∀ᶠ z in 𝓝 z0, μ / z ∈ B :=
      hcont.preimage_mem_nhds (by simpa [hz0val] using hB.mem_nhds hw0B)
    have hz_ne : ∀ᶠ z in 𝓝 z0, z ≠ 0 := isOpen_ne.mem_nhds hz0ne
    filter_upwards [hmem1, hz_ne] with z hzB _
    have h1 : μ * (c / (μ / z)) = c * z := by
      rw [div_div_eq_mul_div, ← mul_div_assoc]
      exact mul_div_cancel_left₀ (c * z) hμ
    have h2 : μ * (c' / (μ / z)) = c' * z := by
      rw [div_div_eq_mul_div, ← mul_div_assoc]
      exact mul_div_cancel_left₀ (c' * z) hμ
    rw [← h1, ← h2]
    exact heq (μ / z) hzB
  have hEqOn := hFan.eqOn_of_preconnected_of_eventuallyEq hFan' Metric.isPreconnected_ball hz0mem hfreq
  have hEv : (fun z : ℂ => fan a h η (c * z)) =ᶠ[𝓝 0]
      (fun z : ℂ => fan a h η (c' * z)) :=
    hEqOn.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hRpos)
  have hEv2 : (fun z : ℂ => (fan a h η (c * z)).2) =ᶠ[𝓝 0]
      (fun z : ℂ => (fan a h η (c' * z)).2) := by
    filter_upwards [hEv] with z hz
    simpa using congrArg Prod.snd hz
  have hD := hEv2.deriv_eq
  rw [deriv_comp_mul_left c (fun u => (fan a h η u).2) 0,
      deriv_comp_mul_left c' (fun u => (fan a h η u).2) 0] at hD
  simp only [mul_zero, smul_eq_mul] at hD
  exact mul_right_cancel₀ hderiv hD

end Work.EQ
