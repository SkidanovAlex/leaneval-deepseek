import Mathlib
import Submission.Work.MRMT.Cauchy.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Beltrami

/-! ## Decay at infinity of the Cauchy transform of a compactly supported function

This file proves `Work.MRMT.Beltrami.cauchyTransform_decay`:  for a smooth compactly supported
`ψ`, both `cauchyTransform ψ` and its real Fréchet derivative decay like `1/‖z‖` and `1/‖z‖²`
at infinity.

The proof is a direct dominated-convergence computation.  Fix a radius `M` with `ψ = 0` off
`Metric.closedBall 0 M` and a point `z` with `2 * M ≤ ‖z‖`.  On the support of `ψ` one has
`‖ζ - z‖ ≥ ‖z‖ / 2`, which gives the `1/‖z‖` bound.  For the derivative, differentiate under the
integral sign on the neighbourhood `Metric.ball z (‖z‖ / 4)` of `z`, where `‖ζ - x‖ ≥ ‖z‖ / 4`
uniformly for `ζ` in the support: use `hasFDerivAt_integral_of_dominated_of_fderiv_le` with the
integrable domination `‖ψ ζ‖ * (16 / ‖z‖ ^ 2)`. -/

/-- `‖cauchyConst‖ = π⁻¹`. -/
lemma decay_norm_cauchyConst : ‖Work.MRMT.cauchyConst‖ = Real.pi⁻¹ := by
  rw [Work.MRMT.cauchyConst, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]

/-- A compactly supported function vanishes outside a closed ball centred at the origin. -/
lemma decay_exists_support_radius (ψ : ℂ → ℂ) (hs : HasCompactSupport ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hs.isCompact.isBounded
  refine ⟨max r 0, le_max_right _ _, fun ζ hζ => ?_⟩
  have hmem : ζ ∈ tsupport ψ := subset_closure (Function.mem_support.mpr hζ)
  have h : dist ζ (0 : ℂ) ≤ r := Metric.mem_closedBall.mp (hr hmem)
  rw [dist_zero_right] at h
  exact le_trans h (le_max_left _ _)

/-! ### Pointwise kernel estimates -/

/-- If `ψ` is supported in the ball of radius `M` around the origin and `2 * M ≤ ‖z‖`, then the
kernel `ψ ζ / (ζ - z)` is bounded by `‖ψ ζ‖ * (2 / ‖z‖)` for every `ζ`. -/
lemma decay_norm_div_sub_le {ψ : ℂ → ℂ} {M : ℝ} (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M)
    {z : ℂ} (hz1 : 1 ≤ ‖z‖) (hz2 : 2 * M ≤ ‖z‖) :
    ∀ ζ : ℂ, ‖ψ ζ / (ζ - z)‖ ≤ ‖ψ ζ‖ * (2 / ‖z‖) := by
  intro ζ
  by_cases h : ψ ζ = 0
  · simp [h]
  · have hζ : ‖ζ‖ ≤ M := hM ζ h
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
    have hhalf : ‖z‖ / 2 ≤ ‖ζ - z‖ := by
      have h1 : ‖z‖ - ‖ζ‖ ≤ ‖ζ - z‖ := by
        have h2 := norm_sub_norm_le z ζ
        rwa [norm_sub_rev] at h2
      have h3 : ‖z‖ / 2 ≤ ‖z‖ - ‖ζ‖ := by linarith
      linarith
    have hnon : 0 ≤ ‖ψ ζ‖ := norm_nonneg _
    rw [norm_div]
    calc ‖ψ ζ‖ / ‖ζ - z‖ ≤ ‖ψ ζ‖ / (‖z‖ / 2) :=
          div_le_div_of_nonneg_left hnon (by linarith) hhalf
      _ = ‖ψ ζ‖ * (2 / ‖z‖) := by field_simp

/-- If `ψ` is supported in the ball of radius `M` around the origin, `2 * M ≤ ‖z‖` and
`‖x - z‖ < ‖z‖ / 4`, then `‖ψ ζ / (ζ - x)²‖ ≤ ‖ψ ζ‖ * (16 / ‖z‖²)` for every `ζ`. -/
lemma decay_norm_div_sq_le {ψ : ℂ → ℂ} {M : ℝ} (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M)
    {z x : ℂ} (hz1 : 1 ≤ ‖z‖) (hz2 : 2 * M ≤ ‖z‖) (hx : ‖x - z‖ < ‖z‖ / 4) :
    ∀ ζ : ℂ, ‖ψ ζ / (ζ - x) ^ 2‖ ≤ ‖ψ ζ‖ * (16 / ‖z‖ ^ 2) := by
  intro ζ
  by_cases h : ψ ζ = 0
  · simp [h]
  · have hζ : ‖ζ‖ ≤ M := hM ζ h
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
    have hxnorm : 3 * ‖z‖ / 4 < ‖x‖ := by
      have h1 : ‖z‖ - ‖x‖ ≤ ‖x - z‖ := by
        have h2 := norm_sub_norm_le z x
        rwa [norm_sub_rev] at h2
      linarith
    have hquarter : ‖z‖ / 4 ≤ ‖ζ - x‖ := by
      have h1 : ‖x‖ - ‖ζ‖ ≤ ‖ζ - x‖ := by
        have h2 := norm_sub_norm_le x ζ
        rwa [norm_sub_rev] at h2
      linarith
    have hnon : 0 ≤ ‖ψ ζ‖ := norm_nonneg _
    rw [norm_div, norm_pow]
    calc ‖ψ ζ‖ / ‖ζ - x‖ ^ 2 ≤ ‖ψ ζ‖ / (‖z‖ / 4) ^ 2 :=
          div_le_div_of_nonneg_left hnon (by positivity)
            (pow_le_pow_left₀ (by positivity) hquarter 2)
      _ = ‖ψ ζ‖ * (16 / ‖z‖ ^ 2) := by field_simp; norm_num

/-- `M < ‖x‖` for `x` in the ball `Metric.ball z (‖z‖ / 4)` when `2 * M ≤ ‖z‖` and `1 ≤ ‖z‖`. -/
lemma decay_M_lt_norm {z x : ℂ} {M : ℝ} (hz1 : 1 ≤ ‖z‖) (hz2 : 2 * M ≤ ‖z‖)
    (hx : ‖x - z‖ < ‖z‖ / 4) : M < ‖x‖ := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
  have h2 : 3 * ‖z‖ / 4 < ‖x‖ := by
    have h1 : ‖z‖ - ‖x‖ ≤ ‖x - z‖ := by
      have h2 := norm_sub_norm_le z x
      rwa [norm_sub_rev] at h2
    linarith
  rcases le_or_gt 0 M with hM | hM
  · linarith
  · exact lt_of_lt_of_le hM (norm_nonneg x)

/-- If `‖ζ‖ ≤ M < ‖x‖` then `ζ - x ≠ 0`. -/
lemma decay_sub_ne_zero {M : ℝ} {x ζ : ℂ} (hx : M < ‖x‖) (hζ : ‖ζ‖ ≤ M) : ζ - x ≠ 0 := by
  intro h
  have h' : ζ = x := sub_eq_zero.mp h
  rw [h'] at hζ
  linarith

/-- The bound for the derivative kernel: on the support of `ψ` the map
`ζ ↦ cauchyConst * ψ ζ * (ζ - x)⁻¹ * (ζ - x)⁻¹` is bounded by `‖ψ ζ‖ * (16 / ‖z‖²)`. -/
lemma decay_norm_kernel_deriv_le {ψ : ℂ → ℂ} {M : ℝ} (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M)
    {z x : ℂ} (hz1 : 1 ≤ ‖z‖) (hz2 : 2 * M ≤ ‖z‖) (hx : ‖x - z‖ < ‖z‖ / 4) (ζ : ℂ) :
    ‖Work.MRMT.cauchyConst * ψ ζ * ((ζ - x)⁻¹ * (ζ - x)⁻¹)‖ ≤ ‖ψ ζ‖ * (16 / ‖z‖ ^ 2) := by
  have hd := decay_norm_div_sq_le hM hz1 hz2 hx ζ
  have heq : Work.MRMT.cauchyConst * ψ ζ * ((ζ - x)⁻¹ * (ζ - x)⁻¹)
      = Work.MRMT.cauchyConst * (ψ ζ / (ζ - x) ^ 2) := by
    rw [div_eq_mul_inv, ← inv_pow, pow_two]
    ring
  rw [heq, norm_mul, decay_norm_cauchyConst]
  have h1 : (Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi)
  calc (Real.pi)⁻¹ * ‖ψ ζ / (ζ - x) ^ 2‖ ≤ 1 * (‖ψ ζ‖ * (16 / ‖z‖ ^ 2)) :=
        mul_le_mul h1 hd (norm_nonneg _) zero_le_one
    _ = ‖ψ ζ‖ * (16 / ‖z‖ ^ 2) := one_mul _

/-! ### The auxiliary functions and the differentiation under the integral sign -/

/-- The integrand of the Cauchy transform. -/
def decay_F (ψ : ℂ → ℂ) (x ζ : ℂ) : ℂ := Work.MRMT.cauchyConst * ψ ζ * (ζ - x)⁻¹

/-- The candidate derivative of the integrand. -/
def decay_F' (ψ : ℂ → ℂ) (x ζ : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.mul ℝ ℂ (Work.MRMT.cauchyConst * ψ ζ * ((ζ - x)⁻¹ * (ζ - x)⁻¹))

/-- Multiplication by `d` as a real-linear map is `restrictScalars ℝ` of `toSpanSingleton`. -/
lemma decay_mul_eq_restrictScalars_toSpanSingleton (d : ℂ) :
    ContinuousLinearMap.mul ℝ ℂ d
      = ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ d) := by
  ext v
  simp [ContinuousLinearMap.coe_restrictScalars']
  exact mul_comm d v

/-- Derivative of the kernel `x ↦ c * (ζ - x)⁻¹`. -/
lemma decay_hasFDerivAt_kernel (c ζ z : ℂ) (hz : ζ - z ≠ 0) :
    HasFDerivAt (fun x : ℂ => c * (ζ - x)⁻¹)
      (ContinuousLinearMap.mul ℝ ℂ (c * ((ζ - z)⁻¹ * (ζ - z)⁻¹))) z := by
  have h1 := (hasDerivAt_const (𝕜 := ℂ) z ζ).sub (hasDerivAt_id (𝕜 := ℂ) z)
  have h2 := h1.inv hz
  have h3 := h2.const_mul c
  have h4 := h3.hasFDerivAt.restrictScalars ℝ
  simp only [Pi.sub_apply, id_eq] at h4
  have hD : c * (-(0 - 1) / (ζ - z) ^ 2) = c * ((ζ - z)⁻¹ * (ζ - z)⁻¹) := by
    have h0 : -(0 - 1 : ℂ) = 1 := by ring
    rw [h0, one_div, ← inv_pow, pow_two]
  rw [hD] at h4
  rw [← decay_mul_eq_restrictScalars_toSpanSingleton] at h4
  exact h4

/-- Continuity of the integrand on the support ball, away from the singularity. -/
lemma decay_continuousOn_F (ψ : ℂ → ℂ) (hψc : Continuous ψ) {M : ℝ} {x : ℂ} (hx : M < ‖x‖) :
    ContinuousOn (decay_F ψ x) (Metric.closedBall (0 : ℂ) M) := by
  have h1 : ContinuousOn (fun ζ : ℂ => Work.MRMT.cauchyConst * ψ ζ)
      (Metric.closedBall (0 : ℂ) M) := hψc.continuousOn.const_mul _
  have h2 : ContinuousOn (fun ζ : ℂ => (ζ - x)⁻¹) (Metric.closedBall (0 : ℂ) M) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro ζ hζ
    exact decay_sub_ne_zero hx (by simpa using hζ)
  exact h1.mul h2

/-- Continuity of the candidate derivative on the support ball. -/
lemma decay_continuousOn_F' (ψ : ℂ → ℂ) (hψc : Continuous ψ) {M : ℝ} {x : ℂ} (hx : M < ‖x‖) :
    ContinuousOn (decay_F' ψ x) (Metric.closedBall (0 : ℂ) M) := by
  have hg : ContinuousOn
      (fun ζ : ℂ => Work.MRMT.cauchyConst * ψ ζ * ((ζ - x)⁻¹ * (ζ - x)⁻¹))
      (Metric.closedBall (0 : ℂ) M) := by
    refine ((hψc.continuousOn.const_mul _).mul ?_)
    refine ((continuousOn_id.sub continuousOn_const).inv₀ ?_).mul
      ((continuousOn_id.sub continuousOn_const).inv₀ ?_)
    · intro ζ hζ
      exact decay_sub_ne_zero hx (by simpa using hζ)
    · intro ζ hζ
      exact decay_sub_ne_zero hx (by simpa using hζ)
  exact (Continuous.continuousOn (ContinuousLinearMap.mul ℝ ℂ).continuous).comp hg
    (t := Set.univ) (fun ζ _ => Set.mem_univ ζ)

/-- The integral of the integrand against the restricted measure is the Cauchy transform. -/
lemma decay_integral_eq (ψ : ℂ → ℂ) {M : ℝ} (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M) (x : ℂ) :
    (∫ ζ, decay_F ψ x ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M)))
      = Work.MRMT.cauchyTransform ψ x := by
  have hA : (∫ ζ, decay_F ψ x ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M)))
      = ∫ ζ, Work.MRMT.cauchyConst * (ψ ζ / (ζ - x)) := by
    rw [show (∫ ζ, decay_F ψ x ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M)))
        = ∫ ζ in Metric.closedBall (0 : ℂ) M, decay_F ψ x ζ from rfl,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      simp [decay_F, div_eq_mul_inv, mul_assoc]
    · intro ζ hζ
      have h0 : ψ ζ = 0 := by
        by_contra h
        exact hζ (by simpa [Metric.mem_closedBall, dist_zero_right] using hM ζ h)
      simp [decay_F, h0]
  rw [hA, Work.MRMT.cauchyTransform]
  exact integral_const_mul _ _

/-- Differentiation under the integral sign for the Cauchy transform. -/
lemma decay_hasFDerivAt_integral (ψ : ℂ → ℂ) (hψc : Continuous ψ)
    {M : ℝ} (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M)
    {z : ℂ} (hz1 : 1 ≤ ‖z‖) (hz2 : 2 * M ≤ ‖z‖) :
    HasFDerivAt (fun x => ∫ ζ, decay_F ψ x ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M)))
      (∫ ζ, decay_F' ψ z ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M))) z := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
  have hball : Metric.ball z (‖z‖ / 4) ∈ 𝓝 z := Metric.ball_mem_nhds z (by positivity)
  have hmem : ∀ x ∈ Metric.ball z (‖z‖ / 4), ‖x - z‖ < ‖z‖ / 4 := by
    intro x hx
    simpa [dist_eq_norm] using hx
  have hxM : ∀ x ∈ Metric.ball z (‖z‖ / 4), M < ‖x‖ := by
    intro x hx
    exact decay_M_lt_norm hz1 hz2 (hmem x hx)
  have hzM : M < ‖z‖ := by
    refine decay_M_lt_norm hz1 hz2 ?_
    simp [hzpos]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := decay_F ψ) (F' := decay_F' ψ)
    (bound := fun ζ => ‖ψ ζ‖ * (16 / ‖z‖ ^ 2)) (s := Metric.ball z (‖z‖ / 4)) hball ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hball] with x hx
    exact (decay_continuousOn_F ψ hψc (hxM x hx)).aestronglyMeasurable measurableSet_closedBall
  · exact (decay_continuousOn_F ψ hψc hzM).integrableOn_compact (isCompact_closedBall 0 M)
  · exact (decay_continuousOn_F' ψ hψc hzM).aestronglyMeasurable measurableSet_closedBall
  · filter_upwards with ζ x hx
    rw [decay_F', ContinuousLinearMap.opNorm_mul_apply]
    exact decay_norm_kernel_deriv_le hM hz1 hz2 (hmem x hx) ζ
  · exact ((hψc.continuousOn.norm.mul continuousOn_const)).integrableOn_compact (isCompact_closedBall 0 M)
  · filter_upwards with ζ x hx
    by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) M
    · have hζM : ‖ζ‖ ≤ M := by simpa [Metric.mem_closedBall, dist_zero_right] using hζ
      have hne : ζ - x ≠ 0 := decay_sub_ne_zero (hxM x hx) hζM
      exact decay_hasFDerivAt_kernel _ ζ x hne
    · have h0 : ψ ζ = 0 := by
        by_contra h
        exact hζ (by simpa [Metric.mem_closedBall, dist_zero_right] using hM ζ h)
      have hF : (fun y : ℂ => decay_F ψ y ζ) = fun _ => 0 := by
        funext y; simp [decay_F, h0]
      have hF' : decay_F' ψ x ζ = 0 := by simp [decay_F', h0]
      rw [hF, hF']
      exact hasFDerivAt_const (0 : ℂ) x

/-! ### The two decay estimates -/

/-- The `1/‖z‖` decay of the Cauchy transform. -/
lemma decay_cauchyTransform_le (ψ : ℂ → ℂ) (hψint : Integrable (fun ζ => ‖ψ ζ‖) volume)
    {M : ℝ} (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M)
    {z : ℂ} (hz1 : 1 ≤ ‖z‖) (hz2 : 2 * M ≤ ‖z‖) :
    ‖Work.MRMT.cauchyTransform ψ z‖ ≤ (2 * (∫ ζ, ‖ψ ζ‖)) / Real.pi / ‖z‖ := by
  have hpt := decay_norm_div_sub_le hM hz1 hz2
  have hb : ‖∫ ζ, ψ ζ / (ζ - z)‖ ≤ ∫ ζ, ‖ψ ζ‖ * (2 / ‖z‖) :=
    norm_integral_le_of_norm_le (hψint.mul_const _) (ae_of_all _ hpt)
  have h1 : ‖Work.MRMT.cauchyTransform ψ z‖
      = ‖Work.MRMT.cauchyConst‖ * ‖∫ ζ, ψ ζ / (ζ - z)‖ := by
    rw [Work.MRMT.cauchyTransform, norm_mul]
  rw [h1, decay_norm_cauchyConst]
  calc Real.pi⁻¹ * ‖∫ ζ, ψ ζ / (ζ - z)‖ ≤ Real.pi⁻¹ * (∫ ζ, ‖ψ ζ‖ * (2 / ‖z‖)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Real.pi⁻¹ * ((∫ ζ, ‖ψ ζ‖) * (2 / ‖z‖)) := by rw [integral_mul_const]
    _ = (2 * (∫ ζ, ‖ψ ζ‖)) / Real.pi / ‖z‖ := by ring

/-- The `1/‖z‖²` decay of the derivative of the Cauchy transform. -/
lemma decay_fderiv_le (ψ : ℂ → ℂ) (hψc : Continuous ψ)
    (hψint : Integrable (fun ζ => ‖ψ ζ‖) volume)
    {M : ℝ} (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M)
    {z : ℂ} (hz1 : 1 ≤ ‖z‖) (hz2 : 2 * M ≤ ‖z‖) :
    ‖fderiv ℝ (Work.MRMT.cauchyTransform ψ) z‖ ≤ (16 * (∫ ζ, ‖ψ ζ‖)) / ‖z‖ ^ 2 := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
  have hzM : M < ‖z‖ := by
    refine decay_M_lt_norm hz1 hz2 ?_
    simp [hzpos]
  have hderiv := decay_hasFDerivAt_integral ψ hψc hM hz1 hz2
  have hcongr : Work.MRMT.cauchyTransform ψ
      =ᶠ[𝓝 z] (fun x => ∫ ζ, decay_F ψ x ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M))) :=
    Filter.Eventually.of_forall fun x => (decay_integral_eq ψ hM x).symm
  have hfinal : HasFDerivAt (Work.MRMT.cauchyTransform ψ)
      (∫ ζ, decay_F' ψ z ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M))) z :=
    hderiv.congr_of_eventuallyEq hcongr
  rw [hfinal.fderiv]
  have hbd : ‖∫ ζ, decay_F' ψ z ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M))‖
      ≤ ∫ ζ, ‖ψ ζ‖ * (16 / ‖z‖ ^ 2) ∂(volume.restrict (Metric.closedBall (0 : ℂ) M)) := by
    refine norm_integral_le_of_norm_le ?_ (ae_of_all _ fun ζ => ?_)
    · exact ((hψc.continuousOn.norm.mul continuousOn_const)).integrableOn_compact
        (isCompact_closedBall 0 M)
    · rw [decay_F', ContinuousLinearMap.opNorm_mul_apply]
      exact decay_norm_kernel_deriv_le hM hz1 hz2 (by simp [hzpos]) ζ
  calc ‖∫ ζ, decay_F' ψ z ζ ∂(volume.restrict (Metric.closedBall (0 : ℂ) M))‖
      ≤ ∫ ζ, ‖ψ ζ‖ * (16 / ‖z‖ ^ 2) ∂(volume.restrict (Metric.closedBall (0 : ℂ) M)) := hbd
    _ = (∫ ζ in Metric.closedBall (0 : ℂ) M, ‖ψ ζ‖) * (16 / ‖z‖ ^ 2) := integral_mul_const _ _
    _ ≤ (∫ ζ, ‖ψ ζ‖) * (16 / ‖z‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact setIntegral_le_integral hψint (ae_of_all _ fun ζ => norm_nonneg _)
    _ = (16 * (∫ ζ, ‖ψ ζ‖)) / ‖z‖ ^ 2 := by ring

/-! ### The theorem -/

/-- **Decay at infinity of the Cauchy transform of a compactly supported function, and of its
derivative.**

Route.  For `z` bounded away from the compact support of `ψ`, differentiate under the integral
sign (legitimate there: the integrand is smooth in `ζ` and `z` and the `ζ`-integral is over the
fixed compact support of `ψ`): `cauchyTransform ψ z = π⁻¹ * ∫ ζ, ψ ζ / (z - ζ)` and
`fderiv ℝ (cauchyTransform ψ) z = (fun v => -π⁻¹ * ∫ ζ, ψ ζ / (z-ζ)^2 * v)`, whence the `1/‖z‖`
and `1/‖z‖^2` bounds for `‖z‖ ≥ 2 * R₀`, `R₀` a bound for the support. -/
theorem cauchyTransform_decay (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖Work.MRMT.cauchyTransform ψ z‖ ≤ C / ‖z‖ ∧
      ‖fderiv ℝ (Work.MRMT.cauchyTransform ψ) z‖ ≤ C / ‖z‖ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := decay_exists_support_radius ψ hs
  have hψc : Continuous ψ := hψ.continuous
  have hψint : Integrable (fun ζ => ‖ψ ζ‖) volume :=
    (hψc.integrable_of_hasCompactSupport hs).norm
  refine ⟨max (2 * (∫ ζ, ‖ψ ζ‖) / Real.pi) (16 * (∫ ζ, ‖ψ ζ‖)), max 1 (2 * M), ?_⟩
  intro z hz
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hz2 : 2 * M ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
  constructor
  · calc ‖Work.MRMT.cauchyTransform ψ z‖ ≤ (2 * (∫ ζ, ‖ψ ζ‖)) / Real.pi / ‖z‖ :=
        decay_cauchyTransform_le ψ hψint hM hz1 hz2
      _ ≤ max (2 * (∫ ζ, ‖ψ ζ‖) / Real.pi) (16 * (∫ ζ, ‖ψ ζ‖)) / ‖z‖ :=
        div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · calc ‖fderiv ℝ (Work.MRMT.cauchyTransform ψ) z‖ ≤ (16 * (∫ ζ, ‖ψ ζ‖)) / ‖z‖ ^ 2 :=
        decay_fderiv_le ψ hψc hψint hM hz1 hz2
      _ ≤ max (2 * (∫ ζ, ‖ψ ζ‖) / Real.pi) (16 * (∫ ζ, ‖ψ ζ‖)) / ‖z‖ ^ 2 :=
        div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

end Work.MRMT.Beltrami
