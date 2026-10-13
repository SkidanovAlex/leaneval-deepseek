import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AngAWeak.sliceFluxDefs
import Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen
import Submission.Work.FTS.EllipticEst.H2W.tendsto_subinterval_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Derivative facts for the angular weight `wS η θ = sin(2θ)^{-η}` -/

/-- `σ = wS η` is differentiable on the open angular interval, with derivative
`wS1 η θ = -2η cos(2θ) sin(2θ)^{-(1+η)}`. -/
theorem wS_hasDerivAt (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (wS η) (wS1 η θ) θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have h := hsin.rpow_const (p := -η) (Or.inl hs.ne')
  have hfun : (fun t : ℝ => (Real.sin (2 * t)) ^ (-η)) = wS η := rfl
  rw [hfun] at h
  refine h.congr_deriv ?_
  rw [show (-η - 1 : ℝ) = -(1 + η) by ring, wS1]
  ring

/-- Value form of the previous statement. -/
theorem deriv_wS_eq (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (wS η) θ = wS1 η θ := (wS_hasDerivAt η hθ).deriv

/-- The derivative of `θ ↦ deriv (wS η) θ` on the open interval is `wS2`. -/
theorem deriv_wS_hasDerivAt (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (deriv (wS η)) (wS2 η θ) θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-2 * Real.sin (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm, mul_neg] using
      (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-(1 + η)))
      ((2 * Real.cos (2 * θ)) * (-(1 + η)) * (Real.sin (2 * θ)) ^ (-(1 + η) - 1)) θ :=
    hsin.rpow_const (Or.inl hs.ne')
  have htarget : HasDerivAt (fun t : ℝ => -(2 * η) * (Real.cos (2 * t)
        * (Real.sin (2 * t)) ^ (-(1 + η)))) (wS2 η θ) θ := by
    refine (hcos.mul hpow).const_mul (-(2 * η)) |>.congr_deriv ?_
    have hsA : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))
        = (Real.sin (2 * θ)) ^ (-η) := by
      have h := Real.rpow_add hs (1 : ℝ) (-(1 + η))
      rw [Real.rpow_one, show (1 : ℝ) + -(1 + η) = -η by ring] at h
      exact h.symm
    rw [show (-(1 + η) - 1 : ℝ) = -(2 + η) by ring, wS2]
    linear_combination (4 * η) * hsA
  have heq : (fun t : ℝ => deriv (wS η) t) =ᶠ[𝓝 θ]
      (fun t : ℝ => -(2 * η) * (Real.cos (2 * t) * (Real.sin (2 * t)) ^ (-(1 + η)))) := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
    rw [deriv_wS_eq η ht, wS1]
    ring
  exact htarget.congr_of_eventuallyEq heq

/-- Value form of the second derivative of the weight. -/
theorem deriv_deriv_wS_eq (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (wS η)) θ = wS2 η θ := (deriv_wS_hasDerivAt η hθ).deriv

/-- **The derivative of the flux.**  On the open angular interval, `fluxG η f` has derivative
`fluxGD η f`, i.e. `σ (f')² + σ f f'' - (1/2) σ'' f²` with `(1/2) σ''` written out as
`2ησ + 2η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}`. -/
theorem fluxG_hasDerivAt (η : ℝ) {f : ℝ → ℝ}
    (hcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (fluxG η f) (fluxGD η f θ) θ := by
  intro θ hθ
  have hnh : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := Ioo_mem_nhds hθ.1 hθ.2
  have hdf : HasDerivAt f (deriv f θ) θ :=
    ((hcd.differentiableOn (by norm_num)).differentiableAt hnh).hasDerivAt
  have hder : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hcd.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdf' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    ((hder.differentiableOn_one).differentiableAt hnh).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => wS η t * f t) (wS1 η θ * f θ + wS η θ * deriv f θ) θ :=
    (wS_hasDerivAt η hθ).mul hdf
  have h2 : HasDerivAt (fun t : ℝ => (wS η t * f t) * deriv f t)
      ((wS1 η θ * f θ + wS η θ * deriv f θ) * deriv f θ
        + (wS η θ * f θ) * deriv (deriv f) θ) θ := h1.mul hdf'
  have h3 : HasDerivAt (fun t : ℝ => (f t) ^ 2) (2 * f θ * deriv f θ) θ := by
    have hm : HasDerivAt (fun t : ℝ => f t * f t)
        (deriv f θ * f θ + f θ * deriv f θ) θ := hdf.mul hdf
    have hval : deriv f θ * f θ + f θ * deriv f θ = 2 * f θ * deriv f θ := by ring
    rw [hval] at hm
    have hfun : (fun t : ℝ => f t * f t) = fun t : ℝ => (f t) ^ 2 := by
      funext t; ring
    rw [hfun] at hm
    exact hm
  have h4 : HasDerivAt (fun t : ℝ => ((1 : ℝ) / 2) * deriv (wS η) t)
      (((1 : ℝ) / 2) * wS2 η θ) θ :=
    (deriv_wS_hasDerivAt η hθ).const_mul ((1 : ℝ) / 2)
  have h5 : HasDerivAt (fun t : ℝ => (((1 : ℝ) / 2) * deriv (wS η) t) * (f t) ^ 2)
      (((1 : ℝ) / 2) * wS2 η θ * (f θ) ^ 2
        + (((1 : ℝ) / 2) * deriv (wS η) θ) * (2 * f θ * deriv f θ)) θ := h4.mul h3
  have h6 : HasDerivAt
      (fun t : ℝ => (wS η t * f t) * deriv f t - (((1 : ℝ) / 2) * deriv (wS η) t) * (f t) ^ 2)
      (((wS1 η θ * f θ + wS η θ * deriv f θ) * deriv f θ
          + (wS η θ * f θ) * deriv (deriv f) θ)
        - (((1 : ℝ) / 2) * wS2 η θ * (f θ) ^ 2
          + (((1 : ℝ) / 2) * deriv (wS η) θ) * (2 * f θ * deriv f θ))) θ := h2.sub h5
  refine h6.congr_deriv ?_
  simp only [fluxGD, wS, wS1, wS2, deriv_wS_eq η hθ]
  ring

/-! ## The integration by parts, the sign of the flux boundary term, and the limit -/

/-- **The flux estimate.**  If the flux `fluxG η f` does not increase from `ε` to `π/2 - ε`
(`hflux`), then the two sides of the integration by parts are ordered as
`∫ (σ (f')² + σ f f'') ≤ ∫ (2ησ f² + 2η(1+η) cos²(2θ) sin(2θ)^{-(2+η)} f²)`.

The proof integrates `(fluxG η f)' = fluxGD η f` over the truncated interval
`[gapDelta n, π/2 - gapDelta n]`, where the boundary term is exactly
`fluxG (π/2 - gapDelta n) - fluxG (gapDelta n) ≤ 0`, and then passes to the limit with
`H2W.tendsto_subinterval_integral`. -/
theorem fluxIntegralIneq (η : ℝ) (hη : 0 < η) (f : ℝ → ℝ)
    (hcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hflux : ∀ ε ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      fluxG η f (Real.pi / 2 - ε) - fluxG η f ε ≤ 0)
    (hIntGD : IntegrableOn (fluxGD η f) (Set.Ioo 0 (Real.pi / 2)))
    (hIntL : IntegrableOn (fun θ => wS η θ * (deriv f θ) ^ 2
      + wS η θ * (f θ * deriv (deriv f) θ)) (Set.Ioo 0 (Real.pi / 2)))
    (hIntR : IntegrableOn (fun θ => 2 * η * wS η θ * (f θ) ^ 2
      + 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (wS η θ * (deriv f θ) ^ 2 + wS η θ * (f θ * deriv (deriv f) θ)))
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (2 * η * wS η θ * (f θ) ^ 2
            + 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2) := by
  have hIθ : IntegrableOn (fluxGD η f) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact hIntGD.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  have htrunc : ∀ n : ℕ,
      (∫ x in (Honest.gapDelta n)..(Real.pi / 2 - Honest.gapDelta n), fluxGD η f x) ≤ 0 := by
    intro n
    have hδpos : 0 < Honest.gapDelta n := Honest.gapDelta_pos n
    have hδ4 : Honest.gapDelta n < Real.pi / 4 :=
      lt_of_le_of_lt (Honest.gapDelta_le_half' n) (by linarith [Real.pi_gt_three])
    have hfluxn : fluxG η f (Real.pi / 2 - Honest.gapDelta n)
        - fluxG η f (Honest.gapDelta n) ≤ 0 := hflux _ ⟨hδpos, hδ4⟩
    have hle : Honest.gapDelta n ≤ Real.pi / 2 - Honest.gapDelta n := by
      linarith [hδ4, Real.pi_pos]
    have hftc : (∫ x in (Honest.gapDelta n)..(Real.pi / 2 - Honest.gapDelta n), fluxGD η f x)
        = fluxG η f (Real.pi / 2 - Honest.gapDelta n) - fluxG η f (Honest.gapDelta n) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [Set.uIcc_of_le hle] at hx
        exact fluxG_hasDerivAt η hcd x
          ⟨by linarith [hδpos, hx.1], by linarith [hx.2, Real.pi_pos, hδpos]⟩
      · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr ?_
        refine hIθ.mono_set (fun x hx => ?_)
        exact ⟨le_of_lt (by linarith [hδpos, hx.1]),
          le_of_lt (by linarith [hx.2, Real.pi_pos, hδpos])⟩
    rw [hftc]
    exact hfluxn
  have htend := Work.FTS.EllipticEst.H2W.tendsto_subinterval_integral hIθ
  have hlimIθ : (∫ x in Work.Spaces.Iθ, fluxGD η f x) ≤ 0 := le_of_tendsto' htend htrunc
  have hlim : (∫ x in Set.Ioo 0 (Real.pi / 2), fluxGD η f x) ≤ 0 := by
    have heq : (∫ x in Set.Ioo 0 (Real.pi / 2), fluxGD η f x)
        = ∫ x in Work.Spaces.Iθ, fluxGD η f x := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))
    linarith
  set L : ℝ → ℝ := fun θ => wS η θ * (deriv f θ) ^ 2 + wS η θ * (f θ * deriv (deriv f) θ)
    with hL
  set R : ℝ → ℝ := fun θ => 2 * η * wS η θ * (f θ) ^ 2
      + 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2
    with hRdef
  have hEq : (∫ x in Set.Ioo 0 (Real.pi / 2), fluxGD η f x)
      = (∫ x in Set.Ioo 0 (Real.pi / 2), L x) - (∫ x in Set.Ioo 0 (Real.pi / 2), R x) := by
    rw [show fluxGD η f = fun θ => L θ - R θ from
      funext (fun θ => by simp only [hL, hRdef, fluxGD]; ring_nf)]
    exact MeasureTheory.integral_sub hIntL hIntR
  have hLR : (∫ x in Set.Ioo 0 (Real.pi / 2), L x)
      ≤ (∫ x in Set.Ioo 0 (Real.pi / 2), R x) := by linarith
  exact hLR

/-! ## The cross term of the sharp Hardy inequality -/

/-- **The cross term is integrable.**  From `(f')² sin(2θ)^{-η} ∈ L¹` and
`f² cos²(2θ) sin(2θ)^{-(2+η)} ∈ L¹` it follows that
`f f' cos(2θ) sin(2θ)^{-(1+η)} ∈ L¹`.  The two given integrands are the squares of
`|f'| sin(2θ)^{-η/2}` and `|f| |cos(2θ)| sin(2θ)^{-(1+η/2)}`, whose product is `|f f' cos(2θ)|
sin(2θ)^{-(1+η)}`, and `2|ab| ≤ a² + b²` applies on the open interval (where `sin(2θ) > 0`). -/
theorem crossTermIntegrable (η : ℝ) (hη : 0 < η) {f : ℝ → ℝ}
    (hcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hR : IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)))
    (hN : IntegrableOn
      (fun θ => (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn
      (fun θ => f θ * deriv f θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η))
      (Set.Ioo 0 (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs
  set T : ℝ → ℝ := fun θ => f θ * deriv f θ * Real.cos (2 * θ)
    * (Real.sin (2 * θ)) ^ (-1 - η) with hT
  have hspos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set A : ℝ → ℝ := fun θ => |deriv f θ| * (Real.sin (2 * θ)) ^ (-(η / 2)) with hA
  set B : ℝ → ℝ := fun θ => |f θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η / 2))
    with hB
  have hA2 : Integrable (fun θ => A θ ^ 2) (volume.restrict s) := by
    refine hR.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    have h2 : (Real.sin (2 * θ) ^ (-(η / 2))) ^ 2 = Real.sin (2 * θ) ^ (-η) := by
      rw [sq, ← Real.rpow_add (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))]
      congr 1
      ring
    rw [hA, mul_pow, sq_abs, h2]
  have hB2 : Integrable (fun θ => B θ ^ 2) (volume.restrict s) := by
    refine hN.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    have h2 : (Real.sin (2 * θ) ^ (-(1 + η / 2))) ^ 2 = Real.sin (2 * θ) ^ (-(2 + η)) := by
      rw [sq, ← Real.rpow_add (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))]
      congr 1
      ring
    rw [hB, mul_pow, mul_pow, sq_abs, sq_abs, h2]
  have hA_m : AEStronglyMeasurable A (volume.restrict s) := by
    have h1 : AEStronglyMeasurable (fun θ => Real.sqrt (A θ ^ 2)) (volume.restrict s) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hA2.aestronglyMeasurable
    refine h1.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    have hAnn : 0 ≤ A θ := by
      rw [hA]
      exact mul_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])).le _)
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hAnn]
  have hB_m : AEStronglyMeasurable B (volume.restrict s) := by
    have h1 : AEStronglyMeasurable (fun θ => Real.sqrt (B θ ^ 2)) (volume.restrict s) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hB2.aestronglyMeasurable
    refine h1.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    have hBnn : 0 ≤ B θ := by
      rw [hB]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])).le _)
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hBnn]
  have hABint : Integrable (fun θ => A θ * B θ) (volume.restrict s) := by
    refine MeasureTheory.Integrable.mono' ((hA2.add hB2).const_mul (1 / 2)) (hA_m.mul hB_m) ?_
    refine Filter.Eventually.of_forall fun θ => ?_
    have h3 : 2 * |A θ| * |B θ| ≤ A θ ^ 2 + B θ ^ 2 := by
      have hsq : 0 ≤ (|A θ| - |B θ|) ^ 2 := sq_nonneg _
      rw [sub_sq, sq_abs, sq_abs] at hsq
      nlinarith [hsq]
    calc ‖A θ * B θ‖ = (1 / 2) * (2 * |A θ| * |B θ|) := by
          rw [Real.norm_eq_abs, abs_mul]; ring
      _ ≤ (1 / 2) * (A θ ^ 2 + B θ ^ 2) := by linarith
  have hTabs : (fun θ => |T θ|) =ᵐ[volume.restrict s] (fun θ => A θ * B θ) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    have hs0 : 0 < Real.sin (2 * θ) := hspos θ hθ
    have hkey : Real.sin (2 * θ) ^ (-1 - η)
        = Real.sin (2 * θ) ^ (-(η / 2)) * Real.sin (2 * θ) ^ (-(1 + η / 2)) := by
      rw [← Real.rpow_add hs0]
      congr 1
      ring
    rw [hT, hA, hB, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), hkey]
    ring
  have hTn : Integrable (fun θ => |T θ|) (volume.restrict s) := hABint.congr hTabs.symm
  have hf_m : AEStronglyMeasurable f (volume.restrict s) :=
    hcd.continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hdf_m : AEStronglyMeasurable (deriv f) (volume.restrict s) :=
    (measurable_deriv f).aestronglyMeasurable
  have hsig_m : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-1 - η))
      (volume.restrict s) :=
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hspos θ hθ)))).aestronglyMeasurable measurableSet_Ioo
  have hT_m : AEStronglyMeasurable T (volume.restrict s) := by
    rw [hT]
    exact (((hf_m.mul hdf_m).mul
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)).mul
        hsig_m)
  have hTint : Integrable T (volume.restrict s) :=
    (MeasureTheory.integrable_norm_iff hT_m).mp (by simpa only [Real.norm_eq_abs] using hTn)
  exact hTint

/-! ## The target -/

theorem slicePairIneqFluxFree (η : ℝ) (hη : 0 < η) (hη1 : η < 1) (f : ℝ → ℝ)
    (hcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hflux : ∀ ε ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ((Real.sin (2 * (Real.pi / 2 - ε))) ^ (-η) * f (Real.pi / 2 - ε) * deriv f (Real.pi / 2 - ε)
          - (1 / 2) * deriv (fun t : ℝ => (Real.sin (2 * t)) ^ (-η)) (Real.pi / 2 - ε)
              * (f (Real.pi / 2 - ε)) ^ 2)
        - ((Real.sin (2 * ε)) ^ (-η) * f ε * deriv f ε
            - (1 / 2) * deriv (fun t : ℝ => (Real.sin (2 * t)) ^ (-η)) ε * (f ε) ^ 2) ≤ 0)
    (hR : MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)))
    (hN : MeasureTheory.IntegrableOn
      (fun θ => (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 2)))
    (hP : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-η) * (f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)))
    (hQ : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-η) * (f θ * deriv (deriv f) θ)) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (-η) * (f θ * deriv (deriv f) θ))
      ≤ 2 * η * ∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (-η) * (f θ) ^ 2 := by
  -- the flux hypothesis in the form used by `fluxIntegralIneq`
  have hflux' : ∀ ε ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      fluxG η f (Real.pi / 2 - ε) - fluxG η f ε ≤ 0 := fun ε hε => hflux ε hε
  -- integrability of the four pieces of the two sides
  have hAint : IntegrableOn (fun θ => wS η θ * (deriv f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine hR.congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [wS]
    ring
  have hBint : IntegrableOn (fun θ => wS η θ * (f θ * deriv (deriv f) θ))
      (Set.Ioo 0 (Real.pi / 2)) := hQ
  have hCint : IntegrableOn (fun θ => 2 * η * wS η θ * (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hP.const_mul (2 * η)).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [wS]
    ring
  have hDint : IntegrableOn (fun θ => 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hN.const_mul (2 * η * (1 + η))).congr (Filter.Eventually.of_forall (fun θ => ?_))
    ring_nf
  have hLint : IntegrableOn (fun θ => wS η θ * (deriv f θ) ^ 2
      + wS η θ * (f θ * deriv (deriv f) θ)) (Set.Ioo 0 (Real.pi / 2)) := hAint.add hBint
  have hRint : IntegrableOn (fun θ => 2 * η * wS η θ * (f θ) ^ 2
      + 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    hCint.add hDint
  have hGDint : IntegrableOn (fluxGD η f) (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hLint.sub hRint).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Pi.sub_apply, fluxGD]
    ring_nf
  have hfluxIneq := fluxIntegralIneq η hη f hcd hflux' hGDint hLint hRint
  -- the sharp Hardy inequality
  have hv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt f (deriv f θ) θ := fun θ hθ =>
    ((hcd.differentiableOn (by norm_num)).differentiableAt (Ioo_mem_nhds hθ.1 hθ.2)).hasDerivAt
  have hintA : IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine hP.congr (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  have hintN : IntegrableOn (fun θ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-2 - η)) (Set.Ioo 0 (Real.pi / 2)) := by
    refine hN.congr (Filter.Eventually.of_forall (fun θ => ?_))
    rw [show -(2 + η) = -2 - η by ring]
  have hcross : IntegrableOn
      (fun θ => f θ * deriv f θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η))
      (Set.Ioo 0 (Real.pi / 2)) := crossTermIntegrable η hη hcd hR hN
  have hhardy := Work.FTS.EllipticEst.H2W.SlotA.sharpHardyCosWeight_open η hη hη1 f hv
    hintA hcross hintN hR
  -- arithmetic: `r + q ≤ 2ηp + 2η(1+η)s`, `s ≤ (1+η)^{-2} r`, `r ≥ 0`, `η < 1`
  set p : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (-η) * (f θ) ^ 2 with hp
  set q : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2),
    (Real.sin (2 * θ)) ^ (-η) * (f θ * deriv (deriv f) θ) with hq
  set r : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2),
    (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) with hr
  set s0 : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2),
    (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η) with hs0
  have hAeq : (∫ θ in Set.Ioo 0 (Real.pi / 2), wS η θ * (deriv f θ) ^ 2) = r := by
    rw [hr]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
      simp only [wS]; ring)
  have hBeq : (∫ θ in Set.Ioo 0 (Real.pi / 2), wS η θ * (f θ * deriv (deriv f) θ)) = q := by
    rw [hq]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by simp only [wS])
  have hCeq : (∫ θ in Set.Ioo 0 (Real.pi / 2), 2 * η * wS η θ * (f θ) ^ 2) = 2 * η * p := by
    have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), 2 * η * wS η θ * (f θ) ^ 2)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (2 * η) * (wS η θ * (f θ) ^ 2) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (2 * η) * (wS η θ * (f θ) ^ 2))
        = 2 * η * ∫ θ in Set.Ioo 0 (Real.pi / 2), wS η θ * (f θ) ^ 2 :=
      MeasureTheory.integral_const_mul _ _
    have h3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), wS η θ * (f θ) ^ 2) = p := by
      rw [hp]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by simp only [wS])
    rw [h1, h2, h3]
  have hDeq : (∫ θ in Set.Ioo 0 (Real.pi / 2), 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2) = 2 * η * (1 + η) * s0 := by
    have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (2 * η * (1 + η)) * ((Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (2 * η * (1 + η)) * ((Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2))
        = (2 * η * (1 + η)) * ∫ θ in Set.Ioo 0 (Real.pi / 2), ((Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2) :=
      MeasureTheory.integral_const_mul _ _
    have h3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), ((Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2)) = s0 := by
      rw [hs0]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
        rw [show -(2 + η) = -2 - η by ring]; ring_nf)
    rw [h1, h2, h3]
  have hLval : (∫ θ in Set.Ioo 0 (Real.pi / 2), (wS η θ * (deriv f θ) ^ 2
      + wS η θ * (f θ * deriv (deriv f) θ))) = r + q := by
    rw [MeasureTheory.integral_add hAint hBint, hAeq, hBeq]
  have hRval : (∫ θ in Set.Ioo 0 (Real.pi / 2), (2 * η * wS η θ * (f θ) ^ 2
      + 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2)) = 2 * η * p + 2 * η * (1 + η) * s0 := by
    rw [MeasureTheory.integral_add hCint hDint, hCeq, hDeq]
  have hstep : r + q ≤ 2 * η * p + 2 * η * (1 + η) * s0 := by
    have h := hfluxIneq
    rwa [hLval, hRval] at h
  have hrnn : 0 ≤ r := by
    rw [hr]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le _))
  have hkey : 2 * η * (1 + η) * s0 ≤ (2 * η / (1 + η)) * r := by
    have h2 := mul_le_mul_of_nonneg_left hhardy (by positivity : (0 : ℝ) ≤ 2 * η * (1 + η))
    refine le_trans h2 (le_of_eq ?_)
    field_simp
  have hcoef : 2 * η / (1 + η) - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one (by linarith : (0 : ℝ) < 1 + η)]
    linarith
  have h3 : (2 * η / (1 + η) - 1) * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcoef hrnn
  linarith [hstep, hkey, h3]

end Work.FTS.EllipticEst.AngAWeak
