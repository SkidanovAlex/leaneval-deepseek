import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

namespace Work.NN.Core

/-! ## The fibrewise Beurling transform as an integral of the fibre shift

The fibrewise Beurling transform is `fiberBeurling R j u z = beurlingTransform (2R)
(fiberSlice j u z) (z j)`.  Since `Function.update z j (z j + s) = z + s e_j`, the Beurling
integral appearing here is `∫_{‖s‖<2R} (u (z + s e_j) - u z)/s²`, and the whole content of the
present file is that its `z`-derivative can be computed by differentiating under the integral
sign (which is legitimate because `u ∈ C²`, so `fderiv u` is locally Lipschitz and the derivative
integrand is `O(1/‖s‖)`). -/

/-- Replacing the `j`-th coordinate of `z` by `z j + s` is adding `s` times the `j`-th
standard basis vector. -/
lemma update_add_eq_add_smul_single {n : ℕ} (z : Cn n) (j : Fin n) (s : ℂ) :
    Function.update z j (z j + s) = z + s • (Pi.single j (1 : ℂ) : Cn n) := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

/-- The `j`-th slice at `z j + s` is the shift of `u` by `s e_j`. -/
lemma fiberSlice_eq_of_add {n : ℕ} (j : Fin n) (u : Cn n → ℂ) (z : Cn n) (s : ℂ) :
    fiberSlice j u z (z j + s) = u (z + s • (Pi.single j (1 : ℂ) : Cn n)) := by
  rw [fiberSlice_apply, update_add_eq_add_smul_single]

/-- The `j`-th slice at `z j` is the value of `u` at `z`. -/
lemma fiberSlice_eq_self {n : ℕ} (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    fiberSlice j u z (z j) = u z := by
  rw [fiberSlice_apply, Function.update_eq_self]

/-- The fibrewise Beurling transform written as an integral of the shifted difference. -/
lemma fiberBeurling_eq_shiftIntegral {n : ℕ} (R : ℝ) (j : Fin n) (u : Cn n → ℂ)
    (z : Cn n) :
    fiberBeurling R j u z
      = -((Real.pi : ℂ))⁻¹ *
        ∫ s in Metric.ball (0 : ℂ) (2 * R),
          (u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - u z) / s ^ 2 := by
  have h : (fun s : ℂ => (fiberSlice j u z (z j + s) - fiberSlice j u z (z j)) / s ^ 2)
      = fun s : ℂ => (u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - u z) / s ^ 2 := by
    funext s
    rw [fiberSlice_eq_of_add, fiberSlice_eq_self]
  rw [fiberBeurling_apply, Work.CR.Flat.beurlingTransform, h]

/-! ## The analytic core: differentiation under the Beurling integral -/

/-- `‖s‖ · (‖s‖²)⁻¹ = ‖s‖⁻¹`, written in the `Real.rpow` normalisation used for the dominating
functions. -/
lemma norm_mul_sq_inv (s : ℂ) : ‖s‖ * (‖s‖ ^ 2)⁻¹ = ‖s‖ ^ (-1 : ℝ) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [norm_zero, Real.zero_rpow (by norm_num : (-1 : ℝ) ≠ 0), zero_mul]
  · have hs' : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr hs
    rw [Real.rpow_neg_one, pow_two, mul_inv]
    field_simp

private lemma aeStronglyMeasurable_div_sq {μ : Measure ℂ} {φ : ℂ → ℂ} (hφ : Continuous φ) :
    AEStronglyMeasurable (fun s : ℂ => φ s / s ^ 2) μ := by
  have h : (fun s : ℂ => φ s / s ^ 2) = fun s : ℂ => φ s * (s ^ 2)⁻¹ := by
    funext s; rw [div_eq_mul_inv]
  rw [h]
  exact (hφ.measurable.mul ((measurable_id.pow_const 2).inv)).aestronglyMeasurable

/-- Integrability of the `s`-derivative of the Beurling integrand: `fderiv u` is locally
Lipschitz because `u ∈ C²`, so the integrand is dominated by `M ‖s‖⁻¹`, which is integrable in
the plane. -/
lemma integrable_fiberDerivIntegrand {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (j : Fin n)
    {u : Cn n → ℂ} (hu : ContDiff ℝ 2 u) (z : Cn n) :
    Integrable
      (fun s : ℂ => (s ^ 2)⁻¹ • (fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u z))
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) := by
  have hshift_norm : ∀ s : ℂ, ‖s • (Pi.single j (1 : ℂ) : Cn n)‖ = ‖s‖ := by
    intro s; rw [norm_smul, Pi.norm_single, norm_one, mul_one]
  obtain ⟨M, hM⟩ :=
    ((hu.fderiv_right (m := 1) (by norm_num)).contDiffOn
      (s := Metric.closedBall z ρ)).exists_lipschitzOnWith
      (by norm_num) (convex_closedBall z ρ) (isCompact_closedBall z ρ)
  refine ((Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := ρ) (s := -1)
    (by norm_num)).const_mul (M : ℝ)).mono' ?_ ?_
  · have hcont : Continuous fun s : ℂ => fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) :=
      (hu.continuous_fderiv (by norm_num)).comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact (((measurable_id.pow_const 2).inv).smul
      (hcont.measurable.sub measurable_const)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with s hs
    have hs' : ‖s‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hs
    have hzmem : z ∈ Metric.closedBall z ρ := by
      rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hρ
    have hzsmem : z + s • (Pi.single j (1 : ℂ) : Cn n) ∈ Metric.closedBall z ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hshift_norm s]
      exact le_of_lt hs'
    have hD : ‖fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u z‖ ≤ (M : ℝ) * ‖s‖ := by
      have h := hM.dist_le_mul (z + s • (Pi.single j (1 : ℂ) : Cn n)) hzsmem z hzmem
      rw [dist_eq_norm, dist_eq_norm,
        show z + s • (Pi.single j (1 : ℂ) : Cn n) - z = s • (Pi.single j (1 : ℂ) : Cn n) by abel,
        hshift_norm s] at h
      exact h
    calc ‖(s ^ 2)⁻¹ • (fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u z)‖
        = ‖(s ^ 2)⁻¹‖ * ‖fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u z‖ :=
          norm_smul _ _
      _ = (‖s‖ ^ 2)⁻¹ * ‖fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u z‖ := by
          rw [norm_inv, norm_pow]
      _ ≤ (‖s‖ ^ 2)⁻¹ * ((M : ℝ) * ‖s‖) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = (M : ℝ) * (‖s‖ * (‖s‖ ^ 2)⁻¹) := by ring
      _ = (M : ℝ) * ‖s‖ ^ (-1 : ℝ) := by rw [norm_mul_sq_inv s]

/-- **Differentiation under the Beurling integral.** For `u ∈ C²`, the map
`z ↦ ∫_{‖s‖<ρ} (u (z + s e_j) - u z)/s²` is differentiable with derivative
`∫_{‖s‖<ρ} (fderiv u (z + s e_j) - fderiv u z)/s²`. -/
theorem hasFDerivAt_fiberIntegral {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (j : Fin n)
    {u : Cn n → ℂ} (hu : ContDiff ℝ 2 u) (z : Cn n) :
    HasFDerivAt
      (fun y : Cn n => ∫ s in Metric.ball (0 : ℂ) ρ,
        (u (y + s • (Pi.single j (1 : ℂ) : Cn n)) - u y) / s ^ 2)
      (∫ s in Metric.ball (0 : ℂ) ρ,
        (s ^ 2)⁻¹ • (fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u z)) z := by
  have hshift_norm : ∀ s : ℂ, ‖s • (Pi.single j (1 : ℂ) : Cn n)‖ = ‖s‖ := by
    intro s; rw [norm_smul, Pi.norm_single, norm_one, mul_one]
  have hfd_cont : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  obtain ⟨K, hK⟩ := (hu.contDiffOn (s := Metric.closedBall z ρ)).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall z ρ) (isCompact_closedBall z ρ)
  obtain ⟨M, hM⟩ :=
    ((hu.fderiv_right (m := 1) (by norm_num)).contDiffOn
      (s := Metric.closedBall z (1 + ρ))).exists_lipschitzOnWith
      (by norm_num) (convex_closedBall z (1 + ρ)) (isCompact_closedBall z (1 + ρ))
  -- integrability of the integrand at the base point
  have hF_int : Integrable (fun s : ℂ => (u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - u z) / s ^ 2)
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) := by
    have hcont : Continuous fun s : ℂ => u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - u z :=
      (hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
        continuous_const
    refine ((Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := ρ) (s := -1)
      (by norm_num)).const_mul (K : ℝ)).mono'
      (aeStronglyMeasurable_div_sq hcont) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with s hs
    have hs' : ‖s‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hs
    have hzmem : z ∈ Metric.closedBall z ρ := by
      rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hρ
    have hzsmem : z + s • (Pi.single j (1 : ℂ) : Cn n) ∈ Metric.closedBall z ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hshift_norm s]
      exact le_of_lt hs'
    have hD : ‖u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - u z‖ ≤ (K : ℝ) * ‖s‖ := by
      have h := hK.dist_le_mul z hzmem (z + s • (Pi.single j (1 : ℂ) : Cn n)) hzsmem
      rw [dist_eq_norm, dist_eq_norm,
        show z - (z + s • (Pi.single j (1 : ℂ) : Cn n)) = -(s • (Pi.single j (1 : ℂ) : Cn n)) by abel,
        norm_neg, hshift_norm s] at h
      calc ‖u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - u z‖
          = ‖u z - u (z + s • (Pi.single j (1 : ℂ) : Cn n))‖ := norm_sub_rev _ _
        _ ≤ (K : ℝ) * ‖s‖ := h
    calc ‖(u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - u z) / s ^ 2‖
        = ‖u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - u z‖ * (‖s‖ ^ 2)⁻¹ := by
          rw [div_eq_mul_inv, norm_mul, norm_inv, norm_pow]
      _ ≤ ((K : ℝ) * ‖s‖) * (‖s‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hD (by positivity)
      _ = (K : ℝ) * (‖s‖ * (‖s‖ ^ 2)⁻¹) := by ring
      _ = (K : ℝ) * ‖s‖ ^ (-1 : ℝ) := by rw [norm_mul_sq_inv s]
  -- measurability of the derivative integrand at the base point
  have hF'_meas : AEStronglyMeasurable
      (fun s : ℂ => (s ^ 2)⁻¹ • (fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u z))
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) := by
    have hcont : Continuous fun s : ℂ => fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) :=
      hfd_cont.comp (continuous_const.add (continuous_id.smul continuous_const))
    exact (((measurable_id.pow_const 2).inv).smul
      (hcont.measurable.sub measurable_const)).aestronglyMeasurable
  have hbound_int : Integrable (fun s : ℂ => (M : ℝ) * ‖s‖ ^ (-1 : ℝ))
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) :=
    (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := ρ) (s := -1)
      (by norm_num)).const_mul (M : ℝ)
  have h_bound : ∀ᵐ a ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)), ∀ x ∈ Metric.ball z 1,
      ‖(a ^ 2)⁻¹ • (fderiv ℝ u (x + a • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u x)‖
        ≤ (M : ℝ) * ‖a‖ ^ (-1 : ℝ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with a ha x hx
    have ha' : ‖a‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp ha
    have hx' : ‖x - z‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hx
    have hxmem : x ∈ Metric.closedBall z (1 + ρ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have hxamem : x + a • (Pi.single j (1 : ℂ) : Cn n) ∈ Metric.closedBall z (1 + ρ) := by
      rw [Metric.mem_closedBall, dist_eq_norm,
        show x + a • (Pi.single j (1 : ℂ) : Cn n) - z = (x - z) + a • (Pi.single j (1 : ℂ) : Cn n) by abel]
      calc ‖(x - z) + a • (Pi.single j (1 : ℂ) : Cn n)‖
          ≤ ‖x - z‖ + ‖a • (Pi.single j (1 : ℂ) : Cn n)‖ := norm_add_le _ _
        _ = ‖x - z‖ + ‖a‖ := by rw [hshift_norm a]
        _ ≤ 1 + ρ := by linarith
    have hD : ‖fderiv ℝ u (x + a • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u x‖ ≤ (M : ℝ) * ‖a‖ := by
      have h := hM.dist_le_mul (x + a • (Pi.single j (1 : ℂ) : Cn n)) hxamem x hxmem
      rw [dist_eq_norm, dist_eq_norm,
        show x + a • (Pi.single j (1 : ℂ) : Cn n) - x = a • (Pi.single j (1 : ℂ) : Cn n) by abel,
        hshift_norm a] at h
      exact h
    calc ‖(a ^ 2)⁻¹ • (fderiv ℝ u (x + a • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u x)‖
        = ‖(a ^ 2)⁻¹‖ * ‖fderiv ℝ u (x + a • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u x‖ :=
          norm_smul _ _
      _ = (‖a‖ ^ 2)⁻¹ * ‖fderiv ℝ u (x + a • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u x‖ := by
          rw [norm_inv, norm_pow]
      _ ≤ (‖a‖ ^ 2)⁻¹ * ((M : ℝ) * ‖a‖) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = (M : ℝ) * (‖a‖ * (‖a‖ ^ 2)⁻¹) := by ring
      _ = (M : ℝ) * ‖a‖ ^ (-1 : ℝ) := by rw [norm_mul_sq_inv a]
  have hmeasF : ∀ᶠ x : Cn n in 𝓝 z, AEStronglyMeasurable
      (fun s : ℂ => (u (x + s • (Pi.single j (1 : ℂ) : Cn n)) - u x) / s ^ 2)
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact aeStronglyMeasurable_div_sq
      ((hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
        continuous_const)
  have h_diff : ∀ᵐ a ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)), ∀ x ∈ Metric.ball z 1,
      HasFDerivAt (fun y : Cn n => (u (y + a • (Pi.single j (1 : ℂ) : Cn n)) - u y) / a ^ 2)
        ((a ^ 2)⁻¹ • (fderiv ℝ u (x + a • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u x)) x := by
    refine Filter.Eventually.of_forall (fun a x _ => ?_)
    have hshift : HasFDerivAt (fun y : Cn n => y + a • (Pi.single j (1 : ℂ) : Cn n))
        (ContinuousLinearMap.id ℝ (Cn n)) x := (hasFDerivAt_id x).add_const _
    have h1 : HasFDerivAt (fun y : Cn n => u (y + a • (Pi.single j (1 : ℂ) : Cn n)))
        (fderiv ℝ u (x + a • (Pi.single j (1 : ℂ) : Cn n))) x := by
      have h := ((hu.differentiable (by norm_num)).differentiableAt
        (x := x + a • (Pi.single j (1 : ℂ) : Cn n))).hasFDerivAt.comp x hshift
      rwa [ContinuousLinearMap.comp_id] at h
    have h2 : HasFDerivAt u (fderiv ℝ u x) x :=
      (hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have h3 := h1.sub h2
    have h4 := h3.mul_const ((a ^ 2)⁻¹)
    simp only [div_eq_mul_inv]
    exact h4
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (α := ℂ) (E := ℂ) (H := Cn n)
    (μ := volume.restrict (Metric.ball (0 : ℂ) ρ))
    (F := fun y s => (u (y + s • (Pi.single j (1 : ℂ) : Cn n)) - u y) / s ^ 2)
    (F' := fun y s => (s ^ 2)⁻¹ • (fderiv ℝ u (y + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u y))
    (bound := fun s => (M : ℝ) * ‖s‖ ^ (-1 : ℝ))
    (s := Metric.ball z 1) (x₀ := z) (Metric.ball_mem_nhds z one_pos)
    hmeasF hF_int hF'_meas h_bound hbound_int h_diff

/-- The applied form of `hasFDerivAt_fiberIntegral`. -/
theorem fiberIntegral_fderiv_apply {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (j : Fin n)
    {u : Cn n → ℂ} (hu : ContDiff ℝ 2 u) (z h : Cn n) :
    fderiv ℝ (fun y : Cn n => ∫ s in Metric.ball (0 : ℂ) ρ,
        (u (y + s • (Pi.single j (1 : ℂ) : Cn n)) - u y) / s ^ 2) z h
      = ∫ s in Metric.ball (0 : ℂ) ρ,
          (fderiv ℝ u (z + s • Pi.single j (1 : ℂ)) h - fderiv ℝ u z h) / s ^ 2 := by
  have hA := hasFDerivAt_fiberIntegral hρ j hu z
  have hInt := integrable_fiberDerivIntegrand hρ j hu z
  rw [hA.fderiv, ContinuousLinearMap.integral_apply hInt h]
  apply integral_congr_ae
  filter_upwards with s
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.sub_apply, div_eq_mul_inv]
  ring

/-! ## The target -/

theorem fiberBeurling_fderiv_apply {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiff ℝ 2 u) (z h : Work.NN.Core.Cn n) :
    fderiv ℝ (Work.NN.Core.fiberBeurling R j u) z h
      = -((Real.pi : ℂ))⁻¹ * ∫ s in Metric.ball (0 : ℂ) (2 * R),
          (fderiv ℝ u (z + s • Pi.single j (1 : ℂ)) h - fderiv ℝ u z h) / s ^ 2 := by
  have hρ : (0 : ℝ) < 2 * R := by linarith
  have hdiff : HasFDerivAt
      (fun y : Cn n => ∫ s in Metric.ball (0 : ℂ) (2 * R),
        (u (y + s • (Pi.single j (1 : ℂ) : Cn n)) - u y) / s ^ 2)
      (∫ s in Metric.ball (0 : ℂ) (2 * R),
        (s ^ 2)⁻¹ • (fderiv ℝ u (z + s • (Pi.single j (1 : ℂ) : Cn n)) - fderiv ℝ u z)) z :=
    hasFDerivAt_fiberIntegral hρ j hu z
  have hbeur : fiberBeurling R j u
      = fun y : Cn n => -((Real.pi : ℂ))⁻¹ *
          (∫ s in Metric.ball (0 : ℂ) (2 * R),
            (u (y + s • (Pi.single j (1 : ℂ) : Cn n)) - u y) / s ^ 2) := by
    funext y
    exact fiberBeurling_eq_shiftIntegral R j u y
  rw [hbeur, fderiv_const_mul hdiff.differentiableAt (-((Real.pi : ℂ))⁻¹), smul_apply,
    fiberIntegral_fderiv_apply hρ j hu z h, smul_eq_mul]

end Work.NN.Core
