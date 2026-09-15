import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Submission.Commons.Analysis.Integral.interval_le_const

/-! Compatibility alias: in the local Mathlib revision `circleMap` lives at the root. -/
namespace Complex
noncomputable abbrev circleMap := _root_.circleMap
end Complex

open Complex MeasureTheory Metric Set Topology
open scoped Interval Real

noncomputable section

namespace Commons.Analysis.Complex

def circleTheta (u : ℂ) (ρ θ : ℝ) : ℝ :=
  if ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1 then ‖u - _root_.circleMap 0 ρ θ‖⁻¹ else 0

lemma circleTheta_nonneg (u : ℂ) (ρ θ : ℝ) : 0 ≤ circleTheta u ρ θ := by
  unfold circleTheta
  by_cases h : ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1
  · rw [if_pos h]; positivity
  · rw [if_neg h]

/-- pointwise bound by `η⁻¹` when the circle is at distance ≥ η -/
lemma circleTheta_le {u : ℂ} {ρ η : ℝ} (hη : 0 < η)
    (hu : ∀ θ, η ≤ ‖u - _root_.circleMap 0 ρ θ‖) : ∀ θ, circleTheta u ρ θ ≤ η⁻¹ := by
  intro θ
  unfold circleTheta
  by_cases h : ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1
  · rw [if_pos h]
    exact inv_anti₀ hη (hu θ)
  · rw [if_neg h]
    exact inv_nonneg.mpr (le_of_lt hη)

/-- Norm of the radius-`ρ` circle point equals `ρ` for `ρ ≥ 0`. -/
lemma norm_circleMap_ofReal {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) : ‖_root_.circleMap 0 ρ θ‖ = ρ := by
  have hcm : _root_.circleMap 0 ρ θ = (ρ : ℂ) * cexp ((θ : ℂ) * I) := by
    simp [_root_.circleMap]
  rw [hcm]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
  have he : ‖cexp ((θ : ℂ) * I)‖ = 1 := by
    simpa [mul_comm] using (norm_exp_ofReal_mul_I θ)
  rw [he, mul_one]

/-- Distance from `u` to the circle of radius `ρ` is at least `|‖u‖ − ρ|`. -/
lemma dist_circle_ge {ρ : ℝ} (hρ : 0 ≤ ρ) (u : ℂ) (θ : ℝ) :
    |‖u‖ - ρ| ≤ ‖u - _root_.circleMap 0 ρ θ‖ := by
  calc
    |‖u‖ - ρ| = |‖u‖ - ‖_root_.circleMap 0 ρ θ‖| := by rw [norm_circleMap_ofReal hρ]
    _ ≤ ‖u - _root_.circleMap 0 ρ θ‖ := abs_norm_sub_norm_le u (_root_.circleMap 0 ρ θ)

/-- Exact squared distance from the real point `r` to the circle point `ρ e^{iθ}`:
`‖r − ρe^{iθ}‖² = (r−ρ)² + 4rρ sin²(θ/2)`. -/
lemma normSq_sub_circleMap_sq {r ρ : ℝ} (θ : ℝ) :
    ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ^ 2 = (r - ρ)^2 + 4 * r * ρ * (Real.sin (θ / 2))^2 := by
  have hz : (↑r : ℂ) - _root_.circleMap 0 ρ θ =
      { re := r - ρ * Real.cos θ, im := -(ρ * Real.sin θ) } := by
    rw [_root_.circleMap]
    rw [Complex.exp_mul_I]
    apply Complex.ext <;> simp [sub_eq_add_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.mul_re, Complex.mul_im]
  rw [hz, Complex.sq_norm, Complex.normSq_mk]
  have hθ : θ = 2 * (θ / 2) := by ring
  have hcos : Real.cos θ = 2 * (Real.cos (θ / 2)) ^ 2 - 1 := by
    conv_lhs => rw [hθ]
    exact Real.cos_two_mul (θ / 2)
  have hpy : (Real.sin (θ / 2)) ^ 2 + (Real.cos (θ / 2)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (θ / 2)
  have hcos2 : Real.cos θ = 1 - 2 * (Real.sin (θ / 2)) ^ 2 := by
    nlinarith
  have hsin2 : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  ring_nf
  rw [hsin2, hcos2]
  ring_nf


/-! ## geometry: arcs on the circle cut by a unit ball around a real point -/

/-- On the left half-circle, membership in the unit ball forces `θ ≤ π/ρ`. -/
lemma theta_le_pi_div_rho_of_sin_half_le {ρ θ : ℝ} (_hρ0 : 0 < ρ) (hθ0 : 0 ≤ θ)
    (hθp : θ ≤ Real.pi) (h : Real.sin (θ / 2) ≤ 1 / ρ) : θ ≤ Real.pi / ρ := by
  have hJ := Real.mul_le_sin (by positivity : 0 ≤ θ / 2) (by linarith : θ / 2 ≤ Real.pi / 2)
  have hA : (2 / Real.pi) * (θ / 2) ≤ 1 / ρ := le_trans hJ h
  have hB : θ / Real.pi ≤ 1 / ρ := by
    convert hA using 1
    ring
  -- multiply by π > 0
  have hC : θ ≤ (1 / ρ) * Real.pi := by
    exact (div_le_iff₀ Real.pi_pos).mp hB
  -- π * (1/ρ) = π/ρ
  calc
    θ ≤ (1 / ρ) * Real.pi := hC
    _ = Real.pi / ρ := by ring

/-- Left middle: `ρ sin(θ/2) ≥ 1` for `π/ρ ≤ θ ≤ π`. -/
lemma one_le_rho_mul_sin_half_left {ρ θ : ℝ} (hρ0 : 0 < ρ) (hθ0 : Real.pi / ρ ≤ θ)
    (hθp : θ ≤ Real.pi) : 1 ≤ ρ * Real.sin (θ / 2) := by
  have hθ'0 : 0 ≤ θ / 2 := by
    have hπρ : 0 < Real.pi / ρ := by positivity
    linarith
  have hJ := Real.mul_le_sin hθ'0 (by linarith : θ / 2 ≤ Real.pi / 2)
  have hρθ : Real.pi ≤ ρ * θ := by
    simpa [mul_comm] using (div_le_iff₀ hρ0).mp hθ0
  have hB' : 1 ≤ (ρ * θ) / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by simpa using hρθ)
  have hB : 1 ≤ ρ * ((2 / Real.pi) * (θ / 2)) := by
    have hE : ρ * ((2 / Real.pi) * (θ / 2)) = (ρ * θ) / Real.pi := by
      field_simp [Real.pi_ne_zero]
    rw [hE]
    exact hB'
  have hA : ρ * ((2 / Real.pi) * (θ / 2)) ≤ ρ * Real.sin (θ / 2) :=
    mul_le_mul_of_nonneg_left hJ (le_of_lt hρ0)
  exact le_trans hB hA


/-- On the right half-circle, membership in the unit ball forces `2π−θ ≤ π/ρ`. -/
lemma two_pi_sub_theta_le_of_sin_half_le {ρ θ : ℝ} (hρ0 : 0 < ρ) (hθp : Real.pi ≤ θ)
    (hθ2 : θ ≤ 2 * Real.pi) (h : Real.sin (θ / 2) ≤ 1 / ρ) :
    2 * Real.pi - θ ≤ Real.pi / ρ := by
  let θ' : ℝ := 2 * Real.pi - θ
  have hθ'0 : 0 ≤ θ' := by dsimp [θ']; linarith
  have hθ'p : θ' ≤ Real.pi := by dsimp [θ']; linarith
  have hs : Real.sin (θ' / 2) = Real.sin (θ / 2) := by
    dsimp [θ']
    have hx : (2 * Real.pi - θ) / 2 = Real.pi - θ / 2 := by ring
    rw [hx, Real.sin_pi_sub]
  have h' : Real.sin (θ' / 2) ≤ 1 / ρ := by simpa [hs] using h
  have hle := theta_le_pi_div_rho_of_sin_half_le hρ0 hθ'0 hθ'p h'
  simpa [θ'] using hle

/-- Right middle: `ρ sin(θ/2) ≥ 1` for `π ≤ θ ≤ 2π − π/ρ`. -/
lemma one_le_rho_mul_sin_half_right {ρ θ : ℝ} (hρ0 : 0 < ρ) (hθp : Real.pi ≤ θ)
    (hθ2 : θ ≤ 2 * Real.pi - Real.pi / ρ) : 1 ≤ ρ * Real.sin (θ / 2) := by
  let θ' : ℝ := 2 * Real.pi - θ
  have hθ'0 : Real.pi / ρ ≤ θ' := by dsimp [θ']; linarith
  have hθ'p : θ' ≤ Real.pi := by dsimp [θ']; linarith
  have hleft := one_le_rho_mul_sin_half_left hρ0 hθ'0 hθ'p
  have hs : Real.sin (θ' / 2) = Real.sin (θ / 2) := by
    dsimp [θ']
    have hx : (2 * Real.pi - θ) / 2 = Real.pi - θ / 2 := by ring
    rw [hx, Real.sin_pi_sub]
  simpa [hs] using hleft

/-- Membership of the real point `r` in the unit ball forces `ρ·sin(θ/2) ≤ 1`
(on the whole period, since `θ ∈ [0, 2π]`). -/
lemma rho_mul_sin_half_le_of_mem {r ρ : ℝ} (hρ : 2 ≤ ρ) (hclose : |r - ρ| ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi))
    (hmem : ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ≤ 1) :
    ρ * Real.sin (θ / 2) ≤ 1 := by
  let s : ℝ := Real.sin (θ / 2)
  have hρ0 : 0 < ρ := by linarith
  have hρ0' : 0 ≤ ρ := by linarith
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by nlinarith [hθ.2])
  have hsq : ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hmem 2
    simpa using this
  have hid := normSq_sub_circleMap_sq (r := r) (ρ := ρ) θ
  have hid' : ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ^ 2 = (r - ρ)^2 + 4 * r * ρ * s ^ 2 := by
    simpa [s] using hid
  have h1 : 4 * r * ρ * s ^ 2 ≤ 1 := by
    have hsq0 : 0 ≤ (r - ρ) ^ 2 := sq_nonneg _
    nlinarith
  have hle2 : ρ - r ≤ 1 := (abs_sub_le_iff.1 hclose).2
  have hrsub : ρ - 1 ≤ r := by nlinarith
  have hr1 : 1 ≤ r := by nlinarith [hρ]
  have hρle : ρ ≤ r + 1 := by nlinarith
  have hρle4r : ρ ≤ 4 * r := by nlinarith
  have hρ2 : ρ ^ 2 ≤ 4 * r * ρ := by
    have hm := mul_le_mul_of_nonneg_left hρle4r hρ0'
    -- ρ·ρ ≤ ρ·(4r)
    nlinarith
  have h2 : ρ ^ 2 * s ^ 2 ≤ 1 := by
    have hstep := mul_le_mul_of_nonneg_right hρ2 (sq_nonneg s)
    exact le_trans hstep h1
  have hρs2 : (ρ * s) ^ 2 ≤ 1 := by
    rw [show (ρ * s) ^ 2 = ρ ^ 2 * s ^ 2 by ring]
    exact h2
  have hρs0 : 0 ≤ ρ * s := mul_nonneg hρ0' hs0
  have hρs : ρ * s ≤ 1 := by
    have habs : |ρ * s| ≤ 1 := by
      have hρs2' : (ρ * s) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using hρs2
      simpa using (sq_le_sq.mp hρs2')
    calc
      ρ * s ≤ |ρ * s| := le_abs_self _
      _ ≤ 1 := habs
  simpa [s] using hρs

/-- `circleTheta` is zero in the middle band `[π/ρ, 2π−π/ρ]`. -/
lemma circleTheta_eq_zero_of_middle {r ρ : ℝ} (hρ : 2 ≤ ρ) (hclose : |r - ρ| ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / ρ) (2 * Real.pi - Real.pi / ρ)) :
    circleTheta (r : ℂ) ρ θ = 0 := by
  unfold circleTheta
  by_cases hmem : ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ≤ 1
  · exfalso
    have hρ0 : 0 < ρ := by linarith
    let s : ℝ := Real.sin (θ / 2)
    have hs1 : 1 ≤ ρ * s := by
      dsimp [s]
      rcases le_total θ Real.pi with hθp | hθp
      · exact one_le_rho_mul_sin_half_left hρ0 (by linarith [hθ.1]) hθp
      · exact one_le_rho_mul_sin_half_right hρ0 hθp (by linarith [hθ.2])
    have hs0 : 0 ≤ s := by
      have h1ρ : 1 / ρ ≤ s := (div_le_iff₀ hρ0).mpr (by simpa [mul_comm] using hs1)
      have h1ρ0 : 0 < 1 / ρ := by positivity
      linarith
    have hρm1 : 0 ≤ ρ - 1 := by linarith
    have hle2 : ρ - r ≤ 1 := (abs_sub_le_iff.1 hclose).2
    have hrsub : ρ - 1 ≤ r := by nlinarith
    have hd2 : 2 ≤ ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ^ 2 := by
      have hid := normSq_sub_circleMap_sq (r := r) (ρ := ρ) θ
      have hid' : ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ^ 2 = (r - ρ)^2 + 4 * r * ρ * s ^ 2 := by
        simpa [s] using hid
      have hsq0 : 0 ≤ (r - ρ) ^ 2 := sq_nonneg _
      have hbig1 : 4 * (ρ - 1) * ρ * s ^ 2 ≤ 4 * r * ρ * s ^ 2 := by
        have h1m := mul_le_mul_of_nonneg_left hrsub (by positivity : 0 ≤ 4 * ρ * s ^ 2)
        nlinarith
      have hcc : 0 ≤ 4 * (ρ - 1) * s := by positivity
      have hbig2 : 4 * (ρ - 1) * s ≤ 4 * (ρ - 1) * ρ * s ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left hs1 hcc
        nlinarith
      have h1ρ : 1 / ρ ≤ s := (div_le_iff₀ hρ0).mpr (by simpa [mul_comm] using hs1)
      have hbig3 : 4 * (ρ - 1) / ρ ≤ 4 * (ρ - 1) * s := by
        have hm := mul_le_mul_of_nonneg_left h1ρ (by positivity : 0 ≤ 4 * (ρ - 1))
        simpa [div_eq_mul_inv] using hm
      have hbig4 : 2 ≤ 4 * (ρ - 1) / ρ := by
        exact (le_div_iff₀ hρ0).2 (by nlinarith [hρ])
      have h4 : 4 * r * ρ * s ^ 2 ≤ ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ^ 2 := by nlinarith
      calc
        2 ≤ 4 * (ρ - 1) / ρ := hbig4
        _ ≤ 4 * (ρ - 1) * s := hbig3
        _ ≤ 4 * (ρ - 1) * ρ * s ^ 2 := hbig2
        _ ≤ 4 * r * ρ * s ^ 2 := hbig1
        _ ≤ ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ^ 2 := h4
    have hd1 : ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hmem 2
      simpa using this
    nlinarith
  · rw [if_neg hmem]


/-! ## interval integrability machinery -/

/-- pointwise upper bound on the norm of the integrand, no positivity hypothesis needed -/
lemma norm_circleTheta_le {u : ℂ} {ρ η : ℝ} (hη : 0 < η)
    (hu : ∀ θ, η ≤ ‖u - _root_.circleMap 0 ρ θ‖) (θ : ℝ) : ‖circleTheta u ρ θ‖ ≤ η⁻¹ := by
  have hle : circleTheta u ρ θ ≤ η⁻¹ := by
    unfold circleTheta
    by_cases h : ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1
    · rw [if_pos h]
      exact inv_anti₀ hη (hu θ)
    · rw [if_neg h]
      exact inv_nonneg.mpr (le_of_lt hη)
  have hn0 : 0 ≤ circleTheta u ρ θ := circleTheta_nonneg u ρ θ
  rw [Real.norm_eq_abs, abs_of_nonneg hn0]
  exact hle

/-- Measurability of the integrand. -/
lemma measurable_circleTheta (u : ℂ) (ρ : ℝ) : Measurable (fun θ : ℝ => circleTheta u ρ θ) := by
  unfold circleTheta
  have hc : Continuous (fun θ : ℝ => ‖u - _root_.circleMap 0 ρ θ‖) := by
    fun_prop
  have hms : MeasurableSet {θ : ℝ | ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1} := by
    exact (isClosed_le hc continuous_const).measurableSet
  have hm1 : Measurable (fun θ : ℝ => (‖u - _root_.circleMap 0 ρ θ‖)⁻¹) := by
    exact Measurable.comp (MeasurableInv.measurable_inv (G := ℝ)) hc.measurable
  exact Measurable.ite hms hm1 measurable_const

/-- Interval integrability on any interval inside `[0, 2π]`, from boundedness + measurability. -/
lemma intervalIntegrable_circleTheta {u : ℂ} {ρ η : ℝ} (hη : 0 < η)
    (hu : ∀ θ, η ≤ ‖u - _root_.circleMap 0 ρ θ‖) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 2 * Real.pi)
    (hab : a ≤ b) : IntervalIntegrable (fun θ : ℝ => circleTheta u ρ θ) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hfull : IntegrableOn (fun θ : ℝ => circleTheta u ρ θ) (Ioc 0 (2 * Real.pi)) volume := by
    refine Measure.integrableOn_of_bounded (M := η⁻¹) ?sfinite ?mble ?bdd
    · rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    · exact Measurable.aestronglyMeasurable (measurable_circleTheta u ρ)
    · apply Filter.Eventually.of_forall
      intro x
      exact norm_circleTheta_le hη hu x
  refine hfull.mono_set ?subset
  intro x hx
  constructor
  · have hx0 : 0 < x := lt_of_le_of_lt ha hx.1
    exact hx0
  · exact le_trans hx.2 hb

/-! ## main estimate for real centres -/

/-! ## main estimate for real centres -/

lemma norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  rw [Complex.norm_real, Real.norm_of_nonneg hr]

/-- **Real case**: `r ≥ 0` with the circle at distance ≥ η; bound the θ-integral. -/
theorem circleTheta_integral_inv_le_of_real {ρ η r : ℝ} (hρ : 2 ≤ ρ) (hη : 0 < η)
    (hr : 0 ≤ r) (hu : η ≤ |r - ρ|) :
    (∫ θ in 0..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) ≤ (16 / ρ) / η := by
  have hρ0 : 0 < ρ := by linarith
  have huθ : ∀ θ, η ≤ ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ := by
    intro θ
    have hrn : ‖(r : ℂ)‖ = r := norm_ofReal_of_nonneg hr
    have hdist := dist_circle_ge (le_of_lt hρ0) (r : ℂ) θ
    rw [hrn] at hdist
    exact le_trans hu hdist
  by_cases hclose : |r - ρ| ≤ 1
  · let a₁ : ℝ := Real.pi / ρ
    let a₂ : ℝ := 2 * Real.pi - Real.pi / ρ
    have hπ0 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have hρ1 : 1 ≤ ρ := by linarith
    have hpr : Real.pi / ρ ≤ Real.pi := (div_le_iff₀ hρ0).2
      (by simpa using (mul_le_mul_of_nonneg_left hρ1 hπ0))
    have hpr0 : 0 ≤ Real.pi / ρ := by positivity
    have ha₁₀ : 0 ≤ a₁ := by dsimp [a₁]; exact hpr0
    have hb : 2 * (Real.pi / ρ) ≤ 2 * Real.pi :=
      mul_le_mul_of_nonneg_left hpr (by norm_num)
    have ha₁₂ : a₁ ≤ a₂ := by
      dsimp [a₁, a₂]
      nlinarith
    have ha₂π : a₂ ≤ 2 * Real.pi := by
      dsimp [a₂]
      nlinarith [hpr0]
    have ha₂₀ : 0 ≤ a₂ := by
      dsimp [a₂]
      nlinarith [hpr]
    have ha₁π : a₁ ≤ 2 * Real.pi := le_trans ha₁₂ ha₂π
    -- middle zero pointwise
    have hmid : ∀ θ, θ ∈ Icc a₁ a₂ → circleTheta (r : ℂ) ρ θ = 0 := by
      intro θ hθ
      have hmid' : θ ∈ Icc (Real.pi / ρ) (2 * Real.pi - Real.pi / ρ) := by
        simpa [a₁, a₂] using hθ
      exact circleTheta_eq_zero_of_middle hρ hclose hmid'
    -- integrability on each interval
    have hint : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 2 * Real.pi → a ≤ b →
        IntervalIntegrable (fun θ : ℝ => circleTheta (r : ℂ) ρ θ) volume a b :=
      fun {a b} ha hb hab => intervalIntegrable_circleTheta hη huθ ha hb hab
    have hint0a₁ : IntervalIntegrable (fun θ : ℝ => circleTheta (r : ℂ) ρ θ) volume 0 a₁ :=
      hint (le_rfl) ha₁π ha₁₀
    have hinta₁a₂ : IntervalIntegrable (fun θ : ℝ => circleTheta (r : ℂ) ρ θ) volume a₁ a₂ :=
      hint ha₁₀ ha₂π ha₁₂
    have hinta₂π : IntervalIntegrable (fun θ : ℝ => circleTheta (r : ℂ) ρ θ) volume a₂ (2 * Real.pi) :=
      hint ha₂₀ (le_rfl) ha₂π
    have hinta₁π : IntervalIntegrable (fun θ : ℝ => circleTheta (r : ℂ) ρ θ) volume a₁ (2 * Real.pi) :=
      hint ha₁₀ (le_rfl) ha₁π
    have hsplit1 : (∫ θ in 0..(2 * Real.pi), circleTheta (r : ℂ) ρ θ)
        = (∫ θ in 0..a₁, circleTheta (r : ℂ) ρ θ)
          + (∫ θ in a₁..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hint0a₁ hinta₁π]
    have hsplit2 : (∫ θ in a₁..(2 * Real.pi), circleTheta (r : ℂ) ρ θ)
        = (∫ θ in a₁..a₂, circleTheta (r : ℂ) ρ θ)
          + (∫ θ in a₂..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hinta₁a₂ hinta₂π]
    have hmidint : (∫ θ in a₁..a₂, circleTheta (r : ℂ) ρ θ) = 0 := by
      have hcongr : (∫ θ in a₁..a₂, circleTheta (r : ℂ) ρ θ) =
          (∫ θ in a₁..a₂, (0 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        exact hmid θ (by simpa [uIcc_of_le ha₁₂] using hθ)
      rw [hcongr, intervalIntegral.integral_zero]
    -- bounds of end integrals via pointwise domination by η⁻¹
    have hle : ∀ x, circleTheta (r : ℂ) ρ x ≤ η⁻¹ := circleTheta_le hη huθ
    have hηi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr (le_of_lt hη)
    have hb1 : (∫ θ in 0..a₁, circleTheta (r : ℂ) ρ θ) ≤ η⁻¹ * (a₁ - 0) :=
      Commons.Analysis.Integral.interval_le_const (f := fun θ => circleTheta (r : ℂ) ρ θ)
        (a := 0) (b := a₁) ha₁₀ hle hηi0
    have hb2 : (∫ θ in a₂..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) ≤ η⁻¹ * (2 * Real.pi - a₂) :=
      Commons.Analysis.Integral.interval_le_const (f := fun θ => circleTheta (r : ℂ) ρ θ)
        (a := a₂) (b := 2 * Real.pi) ha₂π hle hηi0
    have hbound : η⁻¹ * (a₁ - 0) + η⁻¹ * (2 * Real.pi - a₂) ≤ (16 / ρ) / η := by
      have hval : η⁻¹ * (a₁ - 0) + η⁻¹ * (2 * Real.pi - a₂) = 2 * Real.pi / (ρ * η) := by
        dsimp [a₁, a₂]
        field_simp [hρ0.ne', hη.ne']
        ring
      rw [hval]
      have hden : 0 < ρ * η := mul_pos hρ0 hη
      rw [div_le_iff₀ hden]
      have hrhs : (16 / ρ) / η * (ρ * η) = 16 := by
        field_simp [hρ0.ne', hη.ne']
      rw [hrhs]
      have h2p : 2 * Real.pi ≤ 16 := by nlinarith [Real.pi_lt_four]
      exact h2p
    calc
      (∫ θ in 0..(2 * Real.pi), circleTheta (r : ℂ) ρ θ)
          = (∫ θ in 0..a₁, circleTheta (r : ℂ) ρ θ)
            + (∫ θ in a₁..a₂, circleTheta (r : ℂ) ρ θ)
            + (∫ θ in a₂..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) := by
            rw [hsplit1, hsplit2]
            ring
      _ = (∫ θ in 0..a₁, circleTheta (r : ℂ) ρ θ)
            + (∫ θ in a₂..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) := by
            rw [hmidint]
            ring
      _ ≤ η⁻¹ * (a₁ - 0) + η⁻¹ * (2 * Real.pi - a₂) := by
            exact add_le_add hb1 hb2
      _ ≤ (16 / ρ) / η := hbound
  · have hfar : 1 < |r - ρ| := by
      exact lt_of_not_ge hclose
    have hfzero : ∀ θ, circleTheta (r : ℂ) ρ θ = 0 := by
      intro θ
      unfold circleTheta
      have hrn : ‖(r : ℂ)‖ = r := norm_ofReal_of_nonneg hr
      have hdist := dist_circle_ge (le_of_lt hρ0) (r : ℂ) θ
      rw [hrn] at hdist
      have hgt : 1 < ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ := lt_of_lt_of_le hfar hdist
      have hnot : ¬ ‖(r : ℂ) - _root_.circleMap 0 ρ θ‖ ≤ 1 := by
        intro hh
        exact (not_lt_of_ge hh) hgt
      rw [if_neg hnot]
    have hzero : (∫ θ in 0..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) = 0 := by
      have hcongr : (∫ θ in 0..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) =
          (∫ θ in 0..(2 * Real.pi), (0 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        exact hfzero θ
      rw [hcongr, intervalIntegral.integral_zero]
    rw [hzero]
    positivity

lemma norm_circleMap_rotate {ρ : ℝ} (u : ℂ) (θ : ℝ) :
    ‖u - _root_.circleMap 0 ρ θ‖ = ‖(‖u‖ : ℂ) - _root_.circleMap 0 ρ (θ - u.arg)‖ := by
  have hu : u = (‖u‖ : ℂ) * cexp (u.arg * I) := (norm_mul_exp_arg_mul_I u).symm
  have hC : cexp (u.arg * I) * cexp (((θ - u.arg : ℝ) : ℂ) * I) = cexp ((θ : ℂ) * I) := by
    rw [← Complex.exp_add]
    have harg : (u.arg : ℂ) * I + ((θ - u.arg : ℝ) : ℂ) * I = (θ : ℂ) * I := by
      push_cast
      ring
    rw [harg]
  have hz : u - _root_.circleMap 0 ρ θ =
      cexp (u.arg * I) * ((‖u‖ : ℂ) - (ρ : ℂ) * cexp (((θ - u.arg : ℝ) : ℂ) * I)) := by
    conv_lhs => rw [hu]
    rw [_root_.circleMap]
    rw [← hC]
    ring
  calc
    ‖u - _root_.circleMap 0 ρ θ‖ = ‖cexp (u.arg * I) * ((‖u‖ : ℂ) - (ρ : ℂ) * cexp (((θ - u.arg : ℝ) : ℂ) * I))‖ := by rw [hz]
    _ = ‖(‖u‖ : ℂ) - (ρ : ℂ) * cexp (((θ - u.arg : ℝ) : ℂ) * I)‖ := by
      rw [norm_mul]
      have h1 : ‖cexp (u.arg * I)‖ = 1 := by
        simpa [mul_comm] using (norm_exp_ofReal_mul_I u.arg)
      rw [h1, one_mul]
    _ = ‖(‖u‖ : ℂ) - _root_.circleMap 0 ρ (θ - u.arg)‖ := by simp [_root_.circleMap]

/-- `_root_.circleMap 0 ρ` is `2π`-periodic in `θ`. -/
lemma circleMap_add_two_pi (ρ : ℝ) (θ : ℝ) : _root_.circleMap 0 ρ (θ + 2 * Real.pi) = _root_.circleMap 0 ρ θ := by
  have htwo : cexp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
    have hcast : ((2 * Real.pi : ℝ) : ℂ) * I = (2 : ℂ) * ((Real.pi : ℂ) * I) := by
      push_cast
      ring
    rw [hcast]
    simpa [mul_assoc] using Complex.exp_two_pi_mul_I
  have hcexp : cexp (((θ + 2 * Real.pi : ℝ) : ℂ) * I) = cexp ((θ : ℂ) * I) := by
    have harg : ((θ + 2 * Real.pi : ℝ) : ℂ) * I = (θ : ℂ) * I + ((2 * Real.pi : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg, Complex.exp_add, htwo, mul_one]
  rw [_root_.circleMap, _root_.circleMap, hcexp]

/-- The integrand is `2π`-periodic in `θ`. -/
lemma circleTheta_periodic (u : ℂ) (ρ : ℝ) : Function.Periodic (circleTheta u ρ) (2 * Real.pi) := by
  intro θ
  unfold circleTheta
  rw [circleMap_add_two_pi]

/-- Pointwise: rotating `u` by the factor `cexp(u.arg * I)` shifts `θ` by `u.arg`. -/
lemma circleTheta_rotate_pt (ρ : ℝ) (u : ℂ) (θ : ℝ) :
    circleTheta u ρ θ = circleTheta (‖u‖ : ℂ) ρ (θ - u.arg) := by
  unfold circleTheta
  rw [norm_circleMap_rotate]

/-- A shift by `φ` does not change the integral of a `2π`-periodic function. -/
lemma shift_period {g : ℝ → ℝ} (hg : Function.Periodic g (2 * Real.pi)) (φ : ℝ) :
    (∫ θ in 0..(2 * Real.pi), g (θ - φ)) = (∫ x in 0..(2 * Real.pi), g x) := by
  calc
    (∫ θ in 0..(2 * Real.pi), g (θ - φ))
        = (∫ x in (0 + (-φ))..(2 * Real.pi + (-φ)), g x) := by
          rw [show (fun θ : ℝ => g (θ - φ)) = (fun x : ℝ => g (x + (-φ))) by ext x; rfl]
          rw [intervalIntegral.integral_comp_add_right (f := g) (a := 0) (b := 2 * Real.pi) (d := -φ)]
    _ = (∫ x in (-φ)..(2 * Real.pi - φ), g x) := by
          have h1 : 0 + (-φ) = -φ := by ring
          have h2 : 2 * Real.pi + (-φ) = 2 * Real.pi - φ := by ring
          rw [h1, h2]
    _ = (∫ x in 0..(2 * Real.pi), g x) := by
          rw [show 2 * Real.pi - φ = -φ + 2 * Real.pi by ring]
          have h := hg.intervalIntegral_add_eq (-φ) (0 : ℝ)
          simpa using h

/-- The integral is invariant under rotating `u` into its modulus. -/
lemma circleTheta_integral_rotate (ρ : ℝ) (u : ℂ) :
    (∫ θ in 0..(2 * Real.pi), circleTheta u ρ θ)
      = (∫ θ in 0..(2 * Real.pi), circleTheta (‖u‖ : ℂ) ρ θ) := by
  let g : ℝ → ℝ := fun θ => circleTheta (‖u‖ : ℂ) ρ θ
  have hpt : ∀ θ, circleTheta u ρ θ = g (θ - u.arg) := by
    intro θ
    exact circleTheta_rotate_pt ρ u θ
  have hper : Function.Periodic g (2 * Real.pi) := by
    intro θ
    exact circleTheta_periodic (‖u‖ : ℂ) ρ θ
  calc
    (∫ θ in 0..(2 * Real.pi), circleTheta u ρ θ)
        = (∫ θ in 0..(2 * Real.pi), g (θ - u.arg)) := by
          apply intervalIntegral.integral_congr
          intro θ hθ
          exact hpt θ
    _ = (∫ θ in 0..(2 * Real.pi), g θ) := shift_period hper u.arg
    _ = (∫ θ in 0..(2 * Real.pi), circleTheta (‖u‖ : ℂ) ρ θ) := by rfl

/-! ## arbitrary centre via rotation -/

/-- The main estimate for an arbitrary centre `u`. -/
theorem circleTheta_integral_inv_le_any {ρ η : ℝ} (hρ : 2 ≤ ρ) (hη : 0 < η) (u : ℂ)
    (hu : η ≤ |‖u‖ - ρ|) :
    (∫ θ in 0..(2 * Real.pi), circleTheta u ρ θ) ≤ (16 / ρ) / η := by
  let r : ℝ := ‖u‖
  have hr : 0 ≤ r := by dsimp [r]; exact norm_nonneg u
  have hrot : (∫ θ in 0..(2 * Real.pi), circleTheta u ρ θ)
      = (∫ θ in 0..(2 * Real.pi), circleTheta (r : ℂ) ρ θ) := by
    dsimp [r]
    exact circleTheta_integral_rotate ρ u
  have hu' : η ≤ |r - ρ| := by
    dsimp [r]
    simpa using hu
  rw [hrot]
  exact circleTheta_integral_inv_le_of_real hρ hη hr hu'

/-- **Circle-ball θ-integral bound.** -/
theorem circleBallTheta_integral_inv_le {ρ η : ℝ} (hρ : 2 ≤ ρ) (hη : 0 < η) {u : ℂ}
    (hu : η ≤ |‖u‖ - ρ|) :
    (∫ θ : ℝ in 0..(2 * Real.pi),
      (if ‖u - Complex.circleMap 0 ρ θ‖ ≤ 1 then ‖u - Complex.circleMap 0 ρ θ‖⁻¹ else 0)) ≤
        (16 / ρ) / η := by
  simpa [circleTheta] using circleTheta_integral_inv_le_any hρ hη u hu

end Commons.Analysis.Complex