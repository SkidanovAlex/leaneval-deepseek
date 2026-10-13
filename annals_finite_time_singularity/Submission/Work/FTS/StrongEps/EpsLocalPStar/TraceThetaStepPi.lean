import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceThetaStep
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

/-! ## Step: from the pointwise trace rate at `θ = (π/2)⁻` to the `L²` bound

This is the right-endpoint companion of `TraceThetaStep` (same directory).  The pointwise
hypothesis says that on `(π/4, π/2)` the slice `u` is close to `m` at the rate
`sin(2θ)^{(γ-1)/2}`.  On that interval `0 < sin(2θ) ≤ 1`, so the weight
`sin(2θ)^{-η}` is at least `1`; writing `m = u - (u - m)`, the elementary inequality
`m²/2 ≤ u² + (u - m)²` and the hypothesis give the pointwise bound

`(m²/2) sin^{-η} ≤ u² sin^{-η} + (100/(γ-1)) A sin^{γ-1-η}`

on `(π/4, π/2)`.  Integrating over that interval and comparing with the `Iθ`-integrals
(`∫_{(π/4,π/2)} u² sin^{-η} ≤ ∫_{Iθ} u² sin^{-η}` because the integrand is nonnegative,
and `∫_{(π/4,π/2)} sin^{γ-1-η} ≤ ∫_{(π/4,π/2)} sin^{-η}` because `sin^{γ-1} ≤ 1`) yields

`(m²/2) J ≤ K + (100/(γ-1)) A J`,  `J := ∫_{(π/4,π/2)} sin^{-η} ≥ π/4`,

and division by `J` gives the stated constants. -/

/-- Integrability of `θ ↦ sin(2θ)^p` on `(π/4, π/2)` for every `p > -1`. -/
private theorem tspIntegrableSinPow {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], le_of_lt hx.2⟩
  by_cases hp0 : p ≤ 0
  · exact ((Work.Spaces.sin_two_rpow p hp hp0).1).mono_set hsub
  · have hp0' : 0 < p := not_le.mp hp0
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) ?_ ?_ ?_
    · simp
    · exact ((Measurable.pow_const (Real.measurable_sin.comp
        (measurable_const.mul measurable_id)) p)).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hsin0 : 0 ≤ Real.sin (2 * θ) :=
        le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2]))
      have hnorm : ‖(Real.sin (2 * θ)) ^ p‖ ≤ (1 : ℝ) := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg hsin0 p)]
        exact Real.rpow_le_one hsin0 (Real.sin_le_one _) (le_of_lt hp0')
      simpa using hnorm

/-- On `(π/4, π/2)` the weight `sin(2θ)^{-η}` is at least `1`. -/
private theorem tspOneLe {θ : ℝ} (h0 : Real.pi / 4 < θ) (h1 : θ < Real.pi / 2) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [h0, Real.pi_pos]) (by linarith)
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hsin hle
    (show -(Work.Spaces.eta) ≤ 0 by linarith [Work.Spaces.eta_pos])
  rwa [Real.one_rpow] at h

/-- The weighted length of `(π/4, π/2)` is at least `π/4`. -/
private theorem tspPiDivFourLe :
    Real.pi / 4 ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hInt : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    tspIntegrableSinPow (p := -(Work.Spaces.eta)) (by linarith [Work.Spaces.eta_lt_one])
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    simp
  have hmono : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (1 : ℝ))
      ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    integral_mono_ae hInt1 hInt
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => tspOneLe hθ.1 hθ.2))
  have hconst : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (1 : ℝ)) = Real.pi / 4 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul, mul_one]
    ring
  linarith [hmono, hconst]

theorem TraceThetaStepPi {γ m A : ℝ} {u : ℝ → ℝ} (hγ : 1 < γ) (hA : 0 ≤ A)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) Work.Spaces.Iθ)
    (hpt : ∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
      (u θ - m)^2 ≤ 100/(γ-1) * (Real.sin (2*θ))^(γ-1) * A) :
    m^2 ≤ 200/(γ-1) * A + 8/Real.pi * (∫ θ in Work.Spaces.Iθ,
        (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) := by
  have hγ1 : 0 < γ - 1 := by linarith
  have hγ10 : (0 : ℝ) ≤ 100 / (γ - 1) := by positivity
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], le_of_lt hx.2⟩
  set K : ℝ := ∫ θ in Work.Spaces.Iθ,
    (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta) with hK
  set J0 : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
    (Real.sin (2*θ))^(-Work.Spaces.eta) with hJ
  have hIntU : IntegrableOn (fun θ : ℝ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hint.mono_set hsub
  have hIntS : IntegrableOn (fun θ : ℝ => (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    tspIntegrableSinPow (p := -(Work.Spaces.eta)) (by linarith [Work.Spaces.eta_lt_one])
  have hIntExp : IntegrableOn (fun θ : ℝ => (Real.sin (2*θ))^(γ-1-Work.Spaces.eta))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    tspIntegrableSinPow (p := γ - 1 - Work.Spaces.eta) (by linarith [Work.Spaces.eta_lt_one])
  -- the pointwise inequality `m²/2 · s ≤ u² · s + (100/(γ-1)) A sin^{γ-1-η}`
  have hpoint : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))),
      (m^2/2) * (Real.sin (2*θ))^(-Work.Spaces.eta)
        ≤ (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
          + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-(Work.Spaces.eta))) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
    have hsnn : 0 ≤ (Real.sin (2*θ))^(-Work.Spaces.eta) := Real.rpow_nonneg hsin.le _
    have hkey : m^2/2 ≤ (u θ)^2 + (100/(γ-1)) * (Real.sin (2*θ))^(γ-1) * A := by
      have hms : m^2 ≤ 2*(u θ)^2 + 2*(u θ - m)^2 := by nlinarith [sq_nonneg (2*u θ - m)]
      have hp := hpt θ hθ
      linarith
    have hrw : (Real.sin (2*θ))^(γ-1) * (Real.sin (2*θ))^(-Work.Spaces.eta)
        = (Real.sin (2*θ))^(γ-1-Work.Spaces.eta) := by
      rw [← Real.rpow_add hsin]
      ring_nf
    have h2 := mul_le_mul_of_nonneg_right hkey hsnn
    have heq : ((u θ)^2 + (100/(γ-1)) * (Real.sin (2*θ))^(γ-1) * A)
          * (Real.sin (2*θ))^(-Work.Spaces.eta)
        = (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
          + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-Work.Spaces.eta)) := by
      rw [add_mul, ← hrw]; ring
    rwa [heq] at h2
  have hF : IntegrableOn (fun θ : ℝ => (m^2/2) * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := MeasureTheory.Integrable.const_mul hIntS (m^2/2)
  have hG : IntegrableOn (fun θ : ℝ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
      + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-Work.Spaces.eta)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hIntU.add (MeasureTheory.Integrable.const_mul hIntExp ((100/(γ-1))*A))
  have hmono := integral_mono_ae hF hG hpoint
  rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hIntU (MeasureTheory.Integrable.const_mul hIntExp _),
      MeasureTheory.integral_const_mul, ← hJ] at hmono
  -- comparison of the two integrals with their `Iθ`-counterparts
  have hA1 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) ≤ K := by
    rw [hK]
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _)
    · exact Filter.Eventually.of_forall hsub
  have hA2 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (Real.sin (2*θ))^(γ-1-Work.Spaces.eta)) ≤ J0 := by
    rw [hJ]
    refine integral_mono_ae hIntExp hIntS ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
    have hle : (Real.sin (2*θ))^(γ-1-Work.Spaces.eta)
        ≤ (Real.sin (2*θ))^(-Work.Spaces.eta) := by
      rw [show γ - 1 - Work.Spaces.eta = (-Work.Spaces.eta) + (γ - 1) by ring,
        Real.rpow_add hsin]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hsin.le _)
        (Real.rpow_le_one hsin.le (Real.sin_le_one _) (by linarith))
    exact hle
  have hmain : (m^2/2) * J0 ≤ K + (100/(γ-1))*A*J0 := by
    have hcoef : 0 ≤ (100/(γ-1))*A := mul_nonneg hγ10 hA
    have h3 := mul_le_mul_of_nonneg_left hA2 hcoef
    linarith [hmono, hA1, h3]
  have hJge : Real.pi / 4 ≤ J0 := by rw [hJ]; exact tspPiDivFourLe
  have hJpos : 0 < J0 := by linarith [hJge, Real.pi_pos]
  have hKnn : 0 ≤ K := by
    rw [hK]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have hJne : J0 ≠ 0 := ne_of_gt hJpos
  have h1 : m^2/2 ≤ K/J0 + 100/(γ-1)*A := by
    have hdiv : (m^2/2)*J0/J0 ≤ (K + (100/(γ-1))*A*J0)/J0 :=
      div_le_div_of_nonneg_right hmain hJpos.le
    rw [mul_div_assoc, div_self hJne, mul_one] at hdiv
    have hrhs : (K + (100/(γ-1))*A*J0)/J0 = K/J0 + 100/(γ-1)*A := by
      field_simp
    linarith [hdiv, hrhs.le, hrhs.ge]
  have hbnd : K/J0 ≤ (4/Real.pi) * K := by
    have hpi4 : 0 < Real.pi/4 := by linarith [Real.pi_pos]
    have hinv : J0⁻¹ ≤ (Real.pi/4)⁻¹ := inv_anti₀ hpi4 hJge
    have h4 : K/J0 = K * J0⁻¹ := by rw [div_eq_mul_inv]
    rw [h4]
    calc K * J0⁻¹ ≤ K * (Real.pi/4)⁻¹ := mul_le_mul_of_nonneg_left hinv hKnn
      _ = (4/Real.pi) * K := by rw [inv_div]; ring
  have h5 : m^2/2 ≤ (4/Real.pi)*K + 100/(γ-1)*A := by linarith [h1, hbnd]
  have h6 : m^2 ≤ (8/Real.pi)*K + 200/(γ-1)*A := by
    calc m^2 = 2*(m^2/2) := by ring
      _ ≤ 2*((4/Real.pi)*K + 100/(γ-1)*A) := mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ = (8/Real.pi)*K + 200/(γ-1)*A := by ring
  have h7 : (8/Real.pi)*K + 200/(γ-1)*A = 200/(γ-1)*A + 8/Real.pi*K := by ring
  exact h6.trans h7.le

end Work.FTS.StrongEps.EpsLocalPStar
