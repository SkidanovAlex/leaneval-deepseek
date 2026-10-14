import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Numerical bounds for the angular weight `sin(2θ)^{-η}` -/

/-- On `Iθ`, `sin θ · cos²θ ≤ 1`. -/
theorem sin_mul_cos_sq_le_one {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
  have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
    simpa using h
  have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  nlinarith

/-- `(1/2)^{99/100} ≤ 3/5`. -/
theorem half_rpow_eta_le : ((1 : ℝ) / 2) ^ Spaces.eta ≤ 3 / 5 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have heq : ((1 : ℝ) / 2) ^ Spaces.eta = (2 : ℝ) ^ (-Spaces.eta) := by
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (x := 2) (le_of_lt h2) Spaces.eta,
      ← Real.rpow_neg (x := 2) (le_of_lt h2) Spaces.eta]
  rw [heq]
  have hstep : (2 : ℝ) ^ (-Spaces.eta) ≤ (2 : ℝ) ^ (-(4 / 5 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    rw [Spaces.eta]; norm_num
  refine hstep.trans ?_
  have hiff := Real.rpow_le_rpow_iff (x := (2 : ℝ) ^ (-(4 / 5 : ℝ))) (y := (3 : ℝ) / 5)
    (z := (5 : ℝ)) (by positivity) (by norm_num) (by norm_num)
  rw [← hiff]
  have hpow : ((2 : ℝ) ^ (-(4 / 5 : ℝ))) ^ (5 : ℝ) = 1 / 16 := by
    rw [(Real.rpow_mul (x := 2) (le_of_lt h2) (-(4 / 5 : ℝ)) (5 : ℝ)).symm,
      show (-(4 / 5 : ℝ)) * 5 = -4 by norm_num,
      Real.rpow_neg (x := 2) (le_of_lt h2)]
    norm_num
  rw [hpow]
  norm_num

/-- The angular weight estimate `∫_{Iθ} sin(2θ)^{-η} ≤ 189`, from the Jordan majorant
`sin(2θ)^{-η} ≤ (π/4)^η (θ^{-η} + (π/2 - θ)^{-η})` whose integral over `Iθ` is
`π (1/2)^η /(1-η) = 100 π (1/2)^η ≤ 100 · 3.15 · (3/5) = 189`. -/
theorem etaWeight_integral_le :
    ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta) ≤ 189 := by
  have hη0 : 0 < Spaces.eta := by rw [Spaces.eta]; norm_num
  have hη1 : Spaces.eta < 1 := by rw [Spaces.eta]; norm_num
  have hmaj : IntegrableOn (fun θ : ℝ => (Real.pi / 4) ^ Spaces.eta *
      (θ ^ (-Spaces.eta) + (Real.pi / 2 - θ) ^ (-Spaces.eta))) Spaces.Iθ :=
    Work.Spaces.integrableOn_majorant_rpow Spaces.eta hη0 hη1
  have hval : (∫ θ in Spaces.Iθ, (Real.pi / 4) ^ Spaces.eta *
      (θ ^ (-Spaces.eta) + (Real.pi / 2 - θ) ^ (-Spaces.eta)))
      = Real.pi * (1 / 2) ^ Spaces.eta / (1 - Spaces.eta) :=
    Work.Spaces.integral_majorant_rpow Spaces.eta hη0 hη1
  have hpt : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta))
      ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => (Real.pi / 4) ^ Spaces.eta *
        (θ ^ (-Spaces.eta) + (Real.pi / 2 - θ) ^ (-Spaces.eta))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Work.Spaces.sin_rpow_le_majorant_pi Spaces.eta θ hη0 hθ
  have hnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have h₁ : ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)
      ≤ Real.pi * (1 / 2) ^ Spaces.eta / (1 - Spaces.eta) := by
    calc ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ ∫ θ in Spaces.Iθ, (Real.pi / 4) ^ Spaces.eta *
            (θ ^ (-Spaces.eta) + (Real.pi / 2 - θ) ^ (-Spaces.eta)) :=
          integral_mono_of_nonneg hnn hmaj hpt
      _ = Real.pi * (1 / 2) ^ Spaces.eta / (1 - Spaces.eta) := hval
  have h2 : Real.pi * (1 / 2) ^ Spaces.eta / (1 - Spaces.eta) ≤ 189 := by
    have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
    have hhalf : (1 / 2 : ℝ) ^ Spaces.eta ≤ 3 / 5 := half_rpow_eta_le
    have hden : (1 : ℝ) - Spaces.eta = 1 / 100 := by rw [Spaces.eta]; norm_num
    rw [hden]
    have hmul : Real.pi * (1 / 2) ^ Spaces.eta ≤ 3.15 * (3 / 5) :=
      mul_le_mul hpi hhalf (by positivity) (by norm_num)
    have hdiv : Real.pi * (1 / 2) ^ Spaces.eta / (1 / 100)
        = 100 * (Real.pi * (1 / 2) ^ Spaces.eta) := by ring
    rw [hdiv]
    nlinarith [hmul]
  linarith



/-- The product of the restrictions of Lebesgue measure is the restriction to the product set. -/
theorem prod_restrict_eq (s t : Set ℝ) :
    (volume.restrict s).prod (volume.restrict t) = volume.restrict (s ×ˢ t) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]



/-- `L₁₂(f)` (a function of `z` alone) is a.e. strongly measurable on the domain when it is
continuous on `(0,∞)`. -/
theorem aesm_L12f {f : ℝ → ℝ → ℝ} (hL : ContinuousOn (fun z : ℝ => L12f f z) (Set.Ioi 0)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => L12f f p.1)
      (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := by
  have cont_L : ContinuousOn (fun p : ℝ × ℝ => L12f f p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) :=
    hL.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have h := Work.Spaces.aesm_of_continuousOn_Qd _ cont_L
  rwa [prod_restrict_eq] at h



/-- `2|ab| ≤ a² + b²`. -/
theorem two_mul_abs_mul_le (a b : ℝ) : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]




/-- Pointwise AM-GM estimate for the projector term: `|a b| ≤ (a² + b²)/2`. -/
theorem gPsi_pointwise (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h := two_mul_abs_mul_le a b
  rw [abs_mul]
  linarith




/-- `(s^{-η/2})² = s^{-η}` for `s ≥ 0`. -/
theorem rpow_half_sq (s : ℝ) (hs : 0 ≤ s) :
    (s ^ (-Spaces.eta / 2)) ^ 2 = s ^ (-Spaces.eta) := by
  rw [sq]
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (by norm_num [Spaces.eta] : (-Spaces.eta / 2) ≠ 0),
      Real.zero_rpow (by norm_num [Spaces.eta] : (-Spaces.eta) ≠ 0)]
    ring
  · rw [← Real.rpow_add h, show -Spaces.eta / 2 + -Spaces.eta / 2 = -Spaces.eta by ring]




/-- `wip` is additive in its first argument: the four-term linearity used to split the
`η`-weighted pairing of `𝓛_Γ^T` into its four pieces.  This is `wip_eq_integral_prod`
(the Fubini bridge) plus additivity of the Bochner integral on the product measure. -/
theorem wip_sub_add (ρ a₁ a₂ a₃ a₄ b : ℝ → ℝ → ℝ)
    (h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => a₁ z θ * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => a₂ z θ * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => a₃ z θ * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (h4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => a₄ z θ * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    wip ρ (fun z θ => a₁ z θ - a₂ z θ - a₃ z θ + a₄ z θ) b
      = wip ρ a₁ b - wip ρ a₂ b - wip ρ a₃ b + wip ρ a₄ b := by
  set m : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hm
  have e1 : Integrable (fun p : ℝ × ℝ => a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
    integrableOn_prod h1
  have e2 : Integrable (fun p : ℝ × ℝ => a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
    integrableOn_prod h2
  have e3 : Integrable (fun p : ℝ × ℝ => a₃ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
    integrableOn_prod h3
  have e4 : Integrable (fun p : ℝ × ℝ => a₄ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
    integrableOn_prod h4
  have eS : Integrable (fun p : ℝ × ℝ =>
      (a₁ p.1 p.2 - a₂ p.1 p.2 - a₃ p.1 p.2 + a₄ p.1 p.2) * b p.1 p.2 * ρ p.1 p.2) m := by
    refine (((e1.sub e2).sub e3).add e4).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (a₁ z θ - a₂ z θ - a₃ z θ + a₄ z θ) * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    show Integrable (Function.uncurry (fun z θ =>
      (a₁ z θ - a₂ z θ - a₃ z θ + a₄ z θ) * b z θ * ρ z θ))
      (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ))
    rw [volume_restrict_prod, ← hm]
    exact eS
  have key : (∫ p, ((a₁ p.1 p.2 - a₂ p.1 p.2 - a₃ p.1 p.2 + a₄ p.1 p.2)
        * b p.1 p.2 * ρ p.1 p.2) ∂m)
      = (∫ p, a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 ∂m)
        - (∫ p, a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 ∂m)
        - (∫ p, a₃ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 ∂m)
        + (∫ p, a₄ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 ∂m) := by
    have h12 : Integrable (fun p : ℝ × ℝ => a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2
        - a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m := e1.sub e2
    have h123 : Integrable (fun p : ℝ × ℝ => (a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2
        - a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) - a₃ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
      h12.sub e3
    rw [show (fun p : ℝ × ℝ => (a₁ p.1 p.2 - a₂ p.1 p.2 - a₃ p.1 p.2 + a₄ p.1 p.2)
          * b p.1 p.2 * ρ p.1 p.2)
        = fun p => ((a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 - a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2)
          - a₃ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) + a₄ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 from by
      funext p; ring]
    rw [integral_add h123 e4, integral_sub h12 e3, integral_sub e1 e2]
  rw [wip_eq_integral_prod _ _ _ hS, wip_eq_integral_prod _ _ _ h1, wip_eq_integral_prod _ _ _ h2,
    wip_eq_integral_prod _ _ _ h3, wip_eq_integral_prod _ _ _ h4]
  rw [hm] at key
  exact key





/-- On `[π/6,π/3]` the product `ΓK` is at least `1/4`.  There
`u = sinθ cos²θ = (sinθ cosθ)·cosθ ≥ (√3/4)·(1/2) = √3/8 ≥ 1/6`
(`sinθcosθ = sin(2θ)/2` with `sin(2θ) ≥ √3/2` on `2θ ∈ [π/3,2π/3]`, and
`cosθ ≥ cos(π/3) = 1/2`), while `ΓK = 3u^{1+α/3} ≥ 3u^{4/3} ≥ 3(1/6)^{4/3} ≥ 1/4`. -/
theorem gamK_lower_third (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (π / 6) (π / 3)) : (1 : ℝ) / 4 ≤ Spaces.Gam α θ * Spaces.K θ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hsin2 : Real.sqrt 3 / 2 ≤ Real.sin (2 * θ) := by
    have h1 : π / 3 ≤ 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ ≤ 2 * π / 3 := by linarith [hθ.2]
    have h3 : Real.sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    by_cases h : θ ≤ π / 4
    · have hle : Real.sin (π / 3) ≤ Real.sin (2 * θ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) h1
      rwa [h3] at hle
    · have hx1 : π / 3 ≤ π - 2 * θ := by linarith
      have hx2 : π - 2 * θ ≤ π / 2 := by linarith
      have hle : Real.sin (π / 3) ≤ Real.sin (π - 2 * θ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx2 hx1
      rw [Real.sin_pi_sub] at hle
      rwa [h3] at hle
  have hsincos : Real.sqrt 3 / 4 ≤ Real.sin θ * Real.cos θ := by
    have h2m : Real.sin (2 * θ) = 2 * (Real.sin θ * Real.cos θ) := by
      rw [Real.sin_two_mul]; ring
    rw [h2m] at hsin2
    linarith
  have hcos : (1 : ℝ) / 2 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith) hθ.2
    rwa [Real.cos_pi_div_three] at h
  have hcos0 : 0 ≤ Real.cos θ := le_trans (by norm_num) hcos
  have hu : (1 : ℝ) / 6 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : Real.sqrt 3 / 4 * (1 / 2) ≤ (Real.sin θ * Real.cos θ) * Real.cos θ :=
      mul_le_mul hsincos hcos (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (le_trans (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 4) hsincos)
    have h2 : (1 : ℝ) / 6 ≤ Real.sqrt 3 / 4 * (1 / 2) := by
      have h3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    have h3 : (Real.sin θ * Real.cos θ) * Real.cos θ = Real.sin θ * Real.cos θ ^ 2 := by ring
    linarith
  have hu0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := le_trans (by norm_num) hu
  have hu1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 :=
    sin_mul_cos_sq_le_one ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hGK : Spaces.Gam α θ * Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) := by
    rw [Spaces.Gam, Spaces.K, Real.rpow_add' hu0 (by positivity : α / 3 + 1 ≠ 0), Real.rpow_one]
    ring
  have hrpow : (1 : ℝ) / 12 ≤ ((1 : ℝ) / 6) ^ ((4 : ℝ) / 3) := by
    rw [show ((1 : ℝ) / 6) ^ ((4 : ℝ) / 3) = (((1 : ℝ) / 6) ^ (4 : ℕ)) ^ ((1 : ℝ) / 3) by
      rw [← Real.rpow_natCast ((1 : ℝ) / 6) 4, ← Real.rpow_mul (by norm_num)]; norm_num]
    have h : ((1 : ℝ) / 12) ^ (3 : ℕ) ≤ ((1 : ℝ) / 6) ^ (4 : ℕ) := by norm_num
    have h2 : (((1 : ℝ) / 12) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = (1 : ℝ) / 12 := by
      rw [← Real.rpow_natCast ((1 : ℝ) / 12) 3, ← Real.rpow_mul (by norm_num)]; norm_num
    calc (1 : ℝ) / 12 = (((1 : ℝ) / 12) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := h2.symm
      _ ≤ (((1 : ℝ) / 6) ^ (4 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) h (by norm_num)
  calc (1 : ℝ) / 4 ≤ 3 * ((1 : ℝ) / 6) ^ ((4 : ℝ) / 3) := by linarith [hrpow]
    _ ≤ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ ((4 : ℝ) / 3) := by
        refine mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by norm_num) hu (by norm_num)) (by norm_num)
    _ ≤ Spaces.Gam α θ * Spaces.K θ := by
        rw [hGK]
        have h := Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 (by positivity : (0 : ℝ) ≤ α / 3 + 1)
          (by linarith : α / 3 + 1 ≤ (4 : ℝ) / 3)
        linarith

/-- `1/8 ≤ c(α)`: on `[π/6,π/3]` we have `ΓK ≥ 1/4`, so
`c ≥ (1/4)·volume.real (Icc (π/6) (π/3)) = (1/4)·(π/6) = π/24 ≥ 1/8`. -/
theorem c_lower_bound_one_eighth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) / 8 ≤ Spaces.c α := by
  have h_int : MeasureTheory.IntegrableOn (fun θ : ℝ => Spaces.Gam α θ * Spaces.K θ)
      Spaces.Iθ := Spaces.CAux.integrableOn_GamK α hα
  have hfin : volume (Set.Icc (π / 6) (π / 3)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hsub : Set.Icc (π / 6) (π / 3) ⊆ Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : (1 / 4 : ℝ) * volume.real (Set.Icc (π / 6) (π / 3))
      ≤ ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ :=
    MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc hfin
      (fun θ hθ => gamK_lower_third α hα hα1 hθ) (h_int.mono_set hsub)
  have hmono : ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ ≤ Spaces.c α := by
    have hnn : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), (0 : ℝ) ≤ Spaces.Gam α θ * Spaces.K θ := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact (Spaces.gamK_bounds α θ hα hθ).1
    have hst : Set.Icc (π / 6) (π / 3) ≤ᵐ[volume] Spaces.Iθ := by
      filter_upwards with θ hθ
      exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    exact MeasureTheory.setIntegral_mono_set h_int hnn hst
  have hvol : volume.real (Set.Icc (π / 6) (π / 3)) = π / 6 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hnum : (1 : ℝ) / 8 ≤ (1 / 4) * (π / 6) := by
    nlinarith [Real.pi_gt_three]
  calc (1 : ℝ) / 8 ≤ (1 / 4) * (π / 6) := hnum
    _ = (1 / 4) * volume.real (Set.Icc (π / 6) (π / 3)) := by rw [hvol]
    _ ≤ ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ := h1
    _ ≤ Spaces.c α := hmono

/-- `∫_θ (Γ/c)² sin(2θ)^{-η} ≤ 12100` (with `12100 = 64·189`): pointwise `Γ ≤ 1` and
`c ≥ 1/8` give `(Γ/c)² ≤ 64`, and the angular integral is `≤ 189`. -/
theorem Gam_div_c_sq_eta_integral_le_12100 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) ≤ 12100 := by
  have hc : (1 : ℝ) / 8 ≤ Spaces.c α := c_lower_bound_one_eighth α hα hα1
  have hη0 : 0 < Spaces.eta := by rw [Spaces.eta]; norm_num
  have hη1 : Spaces.eta < 1 := by rw [Spaces.eta]; norm_num
  have hsinle : ∀ θ ∈ Spaces.Iθ, (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    intro θ hθ
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hpt : ∀ θ ∈ Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ 64 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    intro θ hθ
    have hG1 : Spaces.Gam α θ ≤ 1 := by
      rw [Spaces.Gam]
      exact Real.rpow_le_one
        (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _))
        (sin_mul_cos_sq_le_one hθ) (le_of_lt (by positivity : (0:ℝ) < α / 3))
    have hG0 : 0 ≤ Spaces.Gam α θ := by
      rw [Spaces.Gam]
      exact Real.rpow_nonneg (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)) _
    have hsq : (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 64 := by
      rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (Spaces.c α) ^ 2)]
      have h1 : Spaces.Gam α θ ^ 2 ≤ 1 := by
        have := mul_self_le_mul_self hG0 hG1
        nlinarith [this]
      have h2 : (1:ℝ) ≤ 64 * (Spaces.c α) ^ 2 := by
        have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/8) hc
        nlinarith [this]
      linarith
    exact mul_le_mul_of_nonneg_right hsq (hsinle θ hθ)
  have hInt2 : IntegrableOn (fun θ : ℝ => 64 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ :=
    ((Work.Spaces.sin_two_rpow (-Spaces.eta) (by linarith) (by linarith)).1).const_mul 64
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (volume.restrict Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    unfold Spaces.Gam
    fun_prop
  have hIntL : IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ := by
    refine Integrable.mono' hInt2 hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hsinle θ hθ))]
    exact hpt θ hθ
  have hmono : ∫ θ in Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      ≤ ∫ θ in Spaces.Iθ, 64 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    refine integral_mono_of_nonneg ?_ hInt2 ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (hsinle θ hθ)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpt θ hθ
  calc ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      ≤ ∫ θ in Spaces.Iθ, 64 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := hmono
    _ = 64 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta) := integral_const_mul _ _
    _ ≤ 64 * 189 := by
        have := etaWeight_integral_le; linarith
    _ ≤ 12100 := by norm_num




/-- Young's inequality in the form `Kuv ≤ δu² + K²v²/(4δ)`. -/
theorem young_abs (K δ u v : ℝ) (hδ : 0 < δ) :
    K * u * v ≤ δ * u ^ 2 + K ^ 2 / (4 * δ) * v ^ 2 := by
  have h1 : 0 ≤ (2 * δ * u - K * v) ^ 2 := sq_nonneg _
  have h2 : 0 < 4 * δ := by linarith
  have h3 : δ * u ^ 2 + K ^ 2 / (4 * δ) * v ^ 2
      = (4 * δ ^ 2 * u ^ 2 + K ^ 2 * v ^ 2) / (4 * δ) := by
    field_simp
  rw [h3, le_div_iff₀ h2]
  nlinarith [h1]


end Work.Coercivity
