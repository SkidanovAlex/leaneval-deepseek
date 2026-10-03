import Mathlib
import Submission.Work.KMTAreas.SupNorm.fourier_decay_inv_sq
import Submission.Work.KMTAreas.SupNorm.scaledBump_norm_integrals
import Submission.Work.KMTAreas.SupNorm.arith_bound

set_option autoImplicit false
open scoped FourierTransform ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas.SupNorm

open Work.KMTContract

/-- The support of the second iterated derivative of `f` is contained in the (topological)
support of `f`. -/
private lemma support_iteratedDeriv_two_subset {f : ℝ → ℂ} :
    Function.support (iteratedDeriv 2 f) ⊆ tsupport f := by
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  exact support_deriv_subset.trans tsupport_deriv_subset

/-- `iteratedDeriv 2 f ξ = 0` at a point of the complement of the (topological) support of `f`. -/
private lemma iteratedDeriv_two_eq_zero_of_notMem_tsupport {f : ℝ → ℂ} {ξ : ℝ}
    (hξ : ξ ∉ tsupport f) : iteratedDeriv 2 f ξ = 0 := by
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  exact deriv_of_notMem_tsupport (fun hx => hξ (tsupport_deriv_subset hx))

/-- Subtracting a constant does not change the second iterated derivative. -/
private lemma iteratedDeriv_two_sub_const {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (c : ℂ) (ξ : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => f y - c) ξ = iteratedDeriv 2 f ξ := by
  have hderiv : deriv (fun y : ℝ => f y - c) = deriv f := by
    funext y
    have hfun : (fun y : ℝ => f y - c) = f - fun _ : ℝ => c := rfl
    rw [hfun, deriv_sub (hf.differentiable (by norm_num)).differentiableAt
      (differentiableAt_const c), deriv_const, sub_zero]
  rw [show iteratedDeriv 2 (fun y : ℝ => f y - c) = deriv (deriv (fun y : ℝ => f y - c)) from by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one],
    hderiv,
    show iteratedDeriv 2 f = deriv (deriv f) from by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]

/-- Pointwise norm bounds for the product of a `C²` function with the rescaled cutoff, its first
and its second derivative. -/
private lemma norm_product_derivs_aux {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ)
    {x₀ δ ν C₁ C₂ : ℝ} (hδ : 0 < δ) (hν0 : 0 ≤ ν) (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hν : ∀ y ∈ Metric.closedBall x₀ δ, ‖θ y - θ x₀‖ ≤ ν)
    (hC₁ : ∀ y ∈ Metric.closedBall x₀ δ, ‖deriv θ y‖ ≤ C₁)
    (hC₂ : ∀ y ∈ Metric.closedBall x₀ δ, ‖iteratedDeriv 2 θ y‖ ≤ C₂) :
    ∀ ξ : ℝ,
      (‖(θ ξ - θ x₀) * scaledBump x₀ δ ξ‖ ≤ ν * ‖scaledBump x₀ δ ξ‖)
      ∧ (‖deriv (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖
          ≤ C₁ * ‖scaledBump x₀ δ ξ‖ + ν * ‖deriv (scaledBump x₀ δ) ξ‖)
      ∧ (‖iteratedDeriv 2 (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖
          ≤ C₂ * ‖scaledBump x₀ δ ξ‖ + 2 * C₁ * ‖deriv (scaledBump x₀ δ) ξ‖
            + ν * ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖) := by
  intro ξ
  by_cases hξ : ξ ∈ Metric.closedBall x₀ δ
  · have hg2 : ContDiff ℝ 2 (scaledBump x₀ δ) :=
      (scaledBump_contDiff x₀ δ).of_le (WithTop.coe_le_coe.mpr le_top)
    have hφ : ContDiff ℝ 2 (fun y : ℝ => θ y - θ x₀) := hθ.sub contDiff_const
    have hφd : DifferentiableAt ℝ (fun y : ℝ => θ y - θ x₀) ξ :=
      (hφ.differentiable (by norm_num)).differentiableAt
    have hgd : DifferentiableAt ℝ (scaledBump x₀ δ) ξ :=
      (hg2.differentiable (by norm_num)).differentiableAt
    have hderivφ : deriv (fun y : ℝ => θ y - θ x₀) ξ = deriv θ ξ := by
      have hfun : (fun y : ℝ => θ y - θ x₀) = θ - fun _ : ℝ => θ x₀ := rfl
      rw [hfun, deriv_sub (hθ.differentiable (by norm_num)).differentiableAt
        (differentiableAt_const (θ x₀)), deriv_const, sub_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hν ξ hξ) (norm_nonneg _)
    · have hderiv : deriv (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ
          = deriv θ ξ * scaledBump x₀ δ ξ + (θ ξ - θ x₀) * deriv (scaledBump x₀ δ) ξ := by
        have hfun : (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y)
            = (fun y : ℝ => θ y - θ x₀) * scaledBump x₀ δ := rfl
        rw [hfun, deriv_mul hφd hgd, hderivφ]
      rw [hderiv]
      calc ‖deriv θ ξ * scaledBump x₀ δ ξ + (θ ξ - θ x₀) * deriv (scaledBump x₀ δ) ξ‖
          ≤ ‖deriv θ ξ * scaledBump x₀ δ ξ‖ + ‖(θ ξ - θ x₀) * deriv (scaledBump x₀ δ) ξ‖ :=
            norm_add_le _ _
        _ = ‖deriv θ ξ‖ * ‖scaledBump x₀ δ ξ‖ + ‖θ ξ - θ x₀‖ * ‖deriv (scaledBump x₀ δ) ξ‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ C₁ * ‖scaledBump x₀ δ ξ‖ + ν * ‖deriv (scaledBump x₀ δ) ξ‖ :=
            add_le_add (mul_le_mul_of_nonneg_right (hC₁ ξ hξ) (norm_nonneg _))
              (mul_le_mul_of_nonneg_right (hν ξ hξ) (norm_nonneg _))
    · have h2F : iteratedDeriv 2 (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ
          = iteratedDeriv 2 (fun y : ℝ => θ y - θ x₀) ξ * scaledBump x₀ δ ξ
            + 2 * deriv (fun y : ℝ => θ y - θ x₀) ξ * deriv (scaledBump x₀ δ) ξ
            + (θ ξ - θ x₀) * iteratedDeriv 2 (scaledBump x₀ δ) ξ := by
        have hfun : (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y)
            = (fun y : ℝ => θ y - θ x₀) * scaledBump x₀ δ := rfl
        rw [hfun, iteratedDeriv_mul (n := 2) hφ.contDiffAt hg2.contDiffAt]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        rw [show (2 - 0 : ℕ) = 2 from rfl, show (2 - 1 : ℕ) = 1 from rfl,
          show (2 - 2 : ℕ) = 0 from rfl]
        simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.choose_zero_right,
          Nat.choose_one_right, Nat.choose_self]
        ring
      have h2φ : iteratedDeriv 2 (fun y : ℝ => θ y - θ x₀) ξ = iteratedDeriv 2 θ ξ :=
        iteratedDeriv_two_sub_const hθ (θ x₀) ξ
      rw [h2F, h2φ, hderivφ]
      calc ‖iteratedDeriv 2 θ ξ * scaledBump x₀ δ ξ + 2 * deriv θ ξ * deriv (scaledBump x₀ δ) ξ
            + (θ ξ - θ x₀) * iteratedDeriv 2 (scaledBump x₀ δ) ξ‖
          ≤ ‖iteratedDeriv 2 θ ξ * scaledBump x₀ δ ξ + 2 * deriv θ ξ * deriv (scaledBump x₀ δ) ξ‖
              + ‖(θ ξ - θ x₀) * iteratedDeriv 2 (scaledBump x₀ δ) ξ‖ := norm_add_le _ _
        _ ≤ (‖iteratedDeriv 2 θ ξ * scaledBump x₀ δ ξ‖
                + ‖2 * deriv θ ξ * deriv (scaledBump x₀ δ) ξ‖)
              + ‖(θ ξ - θ x₀) * iteratedDeriv 2 (scaledBump x₀ δ) ξ‖ :=
            add_le_add (norm_add_le _ _) (le_refl _)
        _ = (‖iteratedDeriv 2 θ ξ‖ * ‖scaledBump x₀ δ ξ‖
                + 2 * ‖deriv θ ξ‖ * ‖deriv (scaledBump x₀ δ) ξ‖)
              + ‖θ ξ - θ x₀‖ * ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖ := by
            simp only [norm_mul, Complex.norm_two]
        _ ≤ (C₂ * ‖scaledBump x₀ δ ξ‖ + 2 * C₁ * ‖deriv (scaledBump x₀ δ) ξ‖)
              + ν * ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖ := by
            have h1 : ‖iteratedDeriv 2 θ ξ‖ * ‖scaledBump x₀ δ ξ‖ ≤ C₂ * ‖scaledBump x₀ δ ξ‖ :=
              mul_le_mul_of_nonneg_right (hC₂ ξ hξ) (norm_nonneg _)
            have h2 : 2 * ‖deriv θ ξ‖ * ‖deriv (scaledBump x₀ δ) ξ‖
                ≤ 2 * C₁ * ‖deriv (scaledBump x₀ δ) ξ‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC₁ ξ hξ)
                (by norm_num : (0 : ℝ) ≤ 2)) (norm_nonneg _)
            have h3 : ‖θ ξ - θ x₀‖ * ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖
                ≤ ν * ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖ :=
              mul_le_mul_of_nonneg_right (hν ξ hξ) (norm_nonneg _)
            linarith
  · -- outside the closed ball: the rescaled cutoff vanishes in a neighbourhood
    have htsupp : tsupport (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y)
        ⊆ Metric.closedBall x₀ δ := by
      refine (tsupport_mul_subset_right (f := fun y : ℝ => θ y - θ x₀)
        (g := scaledBump x₀ δ)).trans ?_
      change closure (Function.support (scaledBump x₀ δ)) ⊆ Metric.closedBall x₀ δ
      calc closure (Function.support (scaledBump x₀ δ)) ⊆ closure (Metric.closedBall x₀ δ) :=
            closure_mono (scaledBump_support hδ)
        _ = Metric.closedBall x₀ δ := IsClosed.closure_eq Metric.isClosed_closedBall
    have hout : ξ ∉ tsupport (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) :=
      fun hc => hξ (htsupp hc)
    have hg0 : scaledBump x₀ δ ξ = 0 := by
      rw [scaledBump_apply]
      apply kmtEta_zero
      rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] at hξ
      have hgt : δ < |ξ - x₀| := lt_of_not_ge hξ
      rw [abs_div, abs_of_pos hδ, one_le_div hδ]
      exact le_of_lt hgt
    refine ⟨?_, ?_, ?_⟩
    · rw [hg0]; simp
    · rw [deriv_of_notMem_tsupport hout, norm_zero]
      exact add_nonneg (mul_nonneg hC₁0 (norm_nonneg _)) (mul_nonneg hν0 (norm_nonneg _))
    · rw [iteratedDeriv_two_eq_zero_of_notMem_tsupport hout, norm_zero]
      exact add_nonneg (add_nonneg (mul_nonneg hC₂0 (norm_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC₁0) (norm_nonneg _)))
        (mul_nonneg hν0 (norm_nonneg _))

theorem norm_fourierInv_error_le {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) {x₀ : ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ν C₁ C₂ : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hν : ∀ y ∈ Metric.closedBall x₀ δ, ‖θ y - θ x₀‖ ≤ ν)
    (hC₁ : ∀ y ∈ Metric.closedBall x₀ δ, ‖deriv θ y‖ ≤ C₁)
    (hC₂ : ∀ y ∈ Metric.closedBall x₀ δ, ‖iteratedDeriv 2 θ y‖ ≤ C₂) :
    ∀ x : ℝ, x ≠ 0 →
      ‖FourierTransformInv.fourierInv (fun ξ => (θ ξ - θ x₀) * Work.KMTAreas.SupNorm.scaledBump x₀ δ ξ) x‖
        ≤ min (ν * δ * Work.KMTAreas.SupNorm.etaI0)
            (4 * (Work.KMTAreas.SupNorm.etaI0 + Work.KMTAreas.SupNorm.etaI1 + Work.KMTAreas.SupNorm.etaI2
                  + C₁ * Work.KMTAreas.SupNorm.etaI0 + C₂ * Work.KMTAreas.SupNorm.etaI0 + 2 * C₁ * Work.KMTAreas.SupNorm.etaI1)
                * (ν / δ + 1) / x ^ 2) := by
  intro x hx
  have hg2 : ContDiff ℝ 2 (scaledBump x₀ δ) :=
    (scaledBump_contDiff x₀ δ).of_le (WithTop.coe_le_coe.mpr le_top)
  have hF_contDiff : ContDiff ℝ 2 (fun ξ : ℝ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) :=
    (hθ.sub contDiff_const).mul hg2
  have hg_supp : Function.support (scaledBump x₀ δ) ⊆ Metric.closedBall x₀ δ :=
    scaledBump_support hδ
  have hg_hasCompact : HasCompactSupport (scaledBump x₀ δ) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ δ) hg_supp
  have hg_int : Integrable (scaledBump x₀ δ) :=
    hg2.continuous.integrable_of_hasCompactSupport hg_hasCompact
  have hg_deriv_int : Integrable (deriv (scaledBump x₀ δ)) :=
    (hg2.deriv' (n := 1)).continuous.integrable_of_hasCompactSupport hg_hasCompact.deriv
  have hg_tsupp : tsupport (scaledBump x₀ δ) ⊆ Metric.closedBall x₀ δ := by
    change closure (Function.support (scaledBump x₀ δ)) ⊆ Metric.closedBall x₀ δ
    calc closure (Function.support (scaledBump x₀ δ))
        ⊆ closure (Metric.closedBall x₀ δ) := closure_mono hg_supp
      _ = Metric.closedBall x₀ δ := IsClosed.closure_eq Metric.isClosed_closedBall
  have hg_iter2_int : Integrable (iteratedDeriv 2 (scaledBump x₀ δ)) :=
    (hg2.continuous_iteratedDeriv' 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ δ)
        (support_iteratedDeriv_two_subset.trans hg_tsupp))
  have hF_hasCompact : HasCompactSupport (fun ξ : ℝ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ δ)
      ((Function.support_mul_subset_right _ _).trans hg_supp)
  have hpb := norm_product_derivs_aux (θ := θ) hθ (x₀ := x₀) (δ := δ) (ν := ν) (C₁ := C₁)
    (C₂ := C₂) hδ hν0 hC₁0 hC₂0 hν hC₁ hC₂
  have hgI := scaledBump_norm_integrals (x₀ := x₀) (δ := δ) hδ
  have hgI0 : (∫ ξ : ℝ, ‖scaledBump x₀ δ ξ‖) = δ * etaI0 := hgI.1
  have hgI1 : (∫ ξ : ℝ, ‖deriv (scaledBump x₀ δ) ξ‖) = etaI1 := hgI.2.1
  have hgI2 : (∫ ξ : ℝ, ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖) = etaI2 / δ := hgI.2.2
  have hA1 : (∫ ξ : ℝ, ‖(θ ξ - θ x₀) * scaledBump x₀ δ ξ‖) ≤ ν * δ * etaI0 := by
    have hmono : (∫ ξ : ℝ, ‖(θ ξ - θ x₀) * scaledBump x₀ δ ξ‖)
        ≤ ∫ ξ : ℝ, ν * ‖scaledBump x₀ δ ξ‖ := by
      apply integral_mono_of_nonneg
      · filter_upwards with ξ; exact norm_nonneg _
      · exact hg_int.norm.const_mul ν
      · filter_upwards with ξ; exact (hpb ξ).1
    calc (∫ ξ : ℝ, ‖(θ ξ - θ x₀) * scaledBump x₀ δ ξ‖)
        ≤ ∫ ξ : ℝ, ν * ‖scaledBump x₀ δ ξ‖ := hmono
      _ = ν * (∫ ξ : ℝ, ‖scaledBump x₀ δ ξ‖) := by rw [integral_const_mul]
      _ = ν * (δ * etaI0) := by rw [hgI0]
      _ = ν * δ * etaI0 := by ring
  have hA2 : (∫ ξ : ℝ, ‖deriv (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
      ≤ C₁ * δ * etaI0 + ν * etaI1 := by
    have hmono : (∫ ξ : ℝ, ‖deriv (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
        ≤ ∫ ξ : ℝ, (C₁ * ‖scaledBump x₀ δ ξ‖ + ν * ‖deriv (scaledBump x₀ δ) ξ‖) := by
      apply integral_mono_of_nonneg
      · filter_upwards with ξ; exact norm_nonneg _
      · exact (hg_int.norm.const_mul C₁).add (hg_deriv_int.norm.const_mul ν)
      · filter_upwards with ξ; exact (hpb ξ).2.1
    calc (∫ ξ : ℝ, ‖deriv (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
        ≤ ∫ ξ : ℝ, (C₁ * ‖scaledBump x₀ δ ξ‖ + ν * ‖deriv (scaledBump x₀ δ) ξ‖) := hmono
      _ = C₁ * (∫ ξ : ℝ, ‖scaledBump x₀ δ ξ‖) + ν * (∫ ξ : ℝ, ‖deriv (scaledBump x₀ δ) ξ‖) := by
          rw [integral_add (hg_int.norm.const_mul C₁) (hg_deriv_int.norm.const_mul ν),
            integral_const_mul, integral_const_mul]
      _ = C₁ * (δ * etaI0) + ν * etaI1 := by rw [hgI0, hgI1]
      _ = C₁ * δ * etaI0 + ν * etaI1 := by ring
  have hA3 : (∫ ξ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
      ≤ C₂ * δ * etaI0 + 2 * C₁ * etaI1 + ν * etaI2 / δ := by
    have hmono : (∫ ξ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
        ≤ ∫ ξ : ℝ, (C₂ * ‖scaledBump x₀ δ ξ‖ + 2 * C₁ * ‖deriv (scaledBump x₀ δ) ξ‖
            + ν * ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖) := by
      apply integral_mono_of_nonneg
      · filter_upwards with ξ; exact norm_nonneg _
      · exact ((hg_int.norm.const_mul C₂).add (hg_deriv_int.norm.const_mul (2 * C₁))).add
          (hg_iter2_int.norm.const_mul ν)
      · filter_upwards with ξ; exact (hpb ξ).2.2
    calc (∫ ξ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
        ≤ ∫ ξ : ℝ, (C₂ * ‖scaledBump x₀ δ ξ‖ + 2 * C₁ * ‖deriv (scaledBump x₀ δ) ξ‖
            + ν * ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖) := hmono
      _ = C₂ * (∫ ξ : ℝ, ‖scaledBump x₀ δ ξ‖) + (2 * C₁) * (∫ ξ : ℝ, ‖deriv (scaledBump x₀ δ) ξ‖)
            + ν * (∫ ξ : ℝ, ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖) := by
          have h2a : Integrable (fun ξ : ℝ => C₂ * ‖scaledBump x₀ δ ξ‖
              + 2 * C₁ * ‖deriv (scaledBump x₀ δ) ξ‖) :=
            (hg_int.norm.const_mul C₂).add (hg_deriv_int.norm.const_mul (2 * C₁))
          have h2b : Integrable (fun ξ : ℝ => ν * ‖iteratedDeriv 2 (scaledBump x₀ δ) ξ‖) :=
            hg_iter2_int.norm.const_mul ν
          have h2c : Integrable (fun ξ : ℝ => C₂ * ‖scaledBump x₀ δ ξ‖) :=
            hg_int.norm.const_mul C₂
          have h2d : Integrable (fun ξ : ℝ => 2 * C₁ * ‖deriv (scaledBump x₀ δ) ξ‖) :=
            hg_deriv_int.norm.const_mul (2 * C₁)
          rw [integral_add h2a h2b, integral_add h2c h2d,
            integral_const_mul, integral_const_mul, integral_const_mul]
      _ = C₂ * (δ * etaI0) + (2 * C₁) * etaI1 + ν * (etaI2 / δ) := by rw [hgI0, hgI1, hgI2]
      _ = C₂ * δ * etaI0 + 2 * C₁ * etaI1 + ν * etaI2 / δ := by ring
  refine le_min ?_ ?_
  · rw [Real.fourierInv_eq]
    calc ‖∫ v : ℝ, Real.fourierChar (inner ℝ v x) • ((θ v - θ x₀) * scaledBump x₀ δ v)‖
        ≤ ∫ v : ℝ, ‖Real.fourierChar (inner ℝ v x) • ((θ v - θ x₀) * scaledBump x₀ δ v)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ v : ℝ, ‖(θ v - θ x₀) * scaledBump x₀ δ v‖ := by
          apply integral_congr_ae
          filter_upwards with v
          simp [Circle.smul_def, Circle.norm_coe]
      _ ≤ ν * δ * etaI0 := hA1
  · rw [Real.fourierInv_eq_fourier_neg]
    have hS : (∫ ξ : ℝ, ‖(θ ξ - θ x₀) * scaledBump x₀ δ ξ‖)
          + (∫ ξ : ℝ, ‖deriv (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
          + (∫ ξ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
        ≤ (etaI0 + etaI1 + etaI2 + C₁ * etaI0 + C₂ * etaI0 + 2 * C₁ * etaI1) * (ν / δ + 1) := by
      have har := arith_bound (ν := ν) (δ := δ) (C₁ := C₁) (C₂ := C₂)
        (η0 := etaI0) (η1 := etaI1) (η2 := etaI2)
        hν0 hC₁0 hC₂0 hδ hδ1 etaI0_nonneg etaI1_nonneg etaI2_nonneg
      linarith [hA1, hA2, hA3, har]
    have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hdec := fourier_decay_inv_sq (fun ξ : ℝ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ)
      hF_contDiff hF_hasCompact (-x)
    have hmain : x ^ 2 * ‖FourierTransform.fourier
          (fun ξ : ℝ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) (-x)‖
        ≤ 4 * ((etaI0 + etaI1 + etaI2 + C₁ * etaI0 + C₂ * etaI0 + 2 * C₁ * etaI1)
            * (ν / δ + 1)) := by
      calc x ^ 2 * ‖FourierTransform.fourier (fun ξ : ℝ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) (-x)‖
          = (-x) ^ 2 * ‖FourierTransform.fourier
              (fun ξ : ℝ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) (-x)‖ := by ring
        _ ≤ 4 * ((∫ ξ : ℝ, ‖(θ ξ - θ x₀) * scaledBump x₀ δ ξ‖)
              + (∫ ξ : ℝ, ‖deriv (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)
              + (∫ ξ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => (θ y - θ x₀) * scaledBump x₀ δ y) ξ‖)) :=
            hdec
        _ ≤ 4 * ((etaI0 + etaI1 + etaI2 + C₁ * etaI0 + C₂ * etaI0 + 2 * C₁ * etaI1)
              * (ν / δ + 1)) := by linarith [hS]
    rw [le_div_iff₀ hx2]
    calc ‖FourierTransform.fourier (fun ξ : ℝ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) (-x)‖ * x ^ 2
        = x ^ 2 * ‖FourierTransform.fourier
            (fun ξ : ℝ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) (-x)‖ := by ring
      _ ≤ 4 * ((etaI0 + etaI1 + etaI2 + C₁ * etaI0 + C₂ * etaI0 + 2 * C₁ * etaI1)
            * (ν / δ + 1)) := hmain
      _ = 4 * (etaI0 + etaI1 + etaI2 + C₁ * etaI0 + C₂ * etaI0 + 2 * C₁ * etaI1)
            * (ν / δ + 1) := by ring

end Work.KMTAreas.SupNorm
