import Mathlib
import Submission.Work.NN.Core.fiberPot

/-!
# `∂̄_k` commutes with the fixed-disc potential in the fibre `j` for `k ≠ j`

This file proves `Work.NN.Core.fiberPot_dbarCoord`: for `k ≠ j` and `u` of class `C¹`, the
`k`-th `∂̄`-operator commutes with the fixed-disc Cauchy potential in the `j`-th fibre
(`Work.NN.Core.fiberPot`).  The point is that for `k ≠ j` the kernel `1/(w - z j)` does not depend
on `z k` and the domain of integration is the fixed disc `‖w‖ < R`, so differentiation under the
integral sign applies.

The proof is organized as follows.

* `fiberPot_hasDerivAt_direction`: for a direction `v` with `v j = 0`, the map
  `t ↦ fiberPot R j u (z + t • v)` has derivative
  `-(1/π) ∫_{‖w‖<R} (fderiv ℝ u (z with z j replaced by w)) v / (w - z j)` at `0`
  (differentiation under the integral sign, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
* `fiberPot_fderiv_apply`: consequently, at a point where `fiberPot R j u` is differentiable,
  `fderiv ℝ (fiberPot R j u) z v` is given by that same integral.
* `integrableOn_fderiv_apply_fiber`: the integrand is absolutely integrable on the disc.
* The theorem itself combines the two directional derivatives `Pi.single k 1` and
  `Pi.single k I` according to the definition of `dbarCoord`, using linearity of the integral.
-/

open MeasureTheory Set

namespace Work.NN.Core

/-- **Directional derivative of the fixed-disc potential.**

Let `v : ℂⁿ` be a direction with `v j = 0` (so that varying `z` in the direction `v` does not move
the pole `z j`).  Then, for every `C¹` function `u` and every base point `z`, the function
`t ↦ fiberPot R j u (z + t • v)` is differentiable at `0` with derivative the integral of the
directional derivative of the integrand:

`d/dt |₀ fiberPot R j u (z + t • v) = -(1/π) ∫_{‖w‖<R} (fderiv ℝ u (z with z j ↦ w)) v / (w - z j) dw`.

This is differentiation under the integral sign; the derivative of the integrand is dominated by
`M ‖(w - z j)⁻¹‖`, which is integrable on the disc. -/
lemma fiberPot_hasDerivAt_direction {n : ℕ} (R : ℝ) (j : Fin n)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) (z v : Fin n → ℂ) (hv : v j = 0) :
    HasDerivAt (fun t : ℝ => fiberPot R j u (z + t • v))
      (-(Real.pi : ℂ)⁻¹ * ∫ w in Metric.ball (0 : ℂ) R,
        (fderiv ℝ u (Function.update z j w)) v / (w - z j)) 0 := by
  have hfdc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hcont_par : Continuous fun p : ℝ × ℂ => Function.update (z + p.1 • v) j p.2 :=
    (continuous_const.add (continuous_fst.smul continuous_const)).update j continuous_snd
  set K : Set (Fin n → ℂ) :=
    (fun p : ℝ × ℂ => Function.update (z + p.1 • v) j p.2) ''
      (Metric.closedBall (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℂ) R) with hKdef
  have hKc : IsCompact K :=
    ((isCompact_closedBall (0 : ℝ) 1).prod (isCompact_closedBall (0 : ℂ) R)).image hcont_par
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn hfdc.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hMb : ∀ y ∈ K, ‖fderiv ℝ u y‖ ≤ M := fun y hy => le_trans (hM₀ y hy) (le_max_left _ _)
  have hwv : Function.update v j 0 = v := Function.update_eq_iff.2 ⟨hv.symm, fun _ _ => rfl⟩
  set μ : Measure ℂ := volume.restrict (Metric.ball (0 : ℂ) R) with hμ
  set s : Set ℝ := Metric.ball (0 : ℝ) 1 with hs
  set F : ℝ → ℂ → ℂ := fun t w => u (Function.update (z + t • v) j w) / (w - z j) with hF
  set F' : ℝ → ℂ → ℂ :=
    fun x w => (fderiv ℝ u (Function.update (z + x • v) j w)) v / (w - z j) with hF'
  set bound : ℂ → ℝ := fun w => M * ‖v‖ * ‖(w - z j)⁻¹‖ with hbounddef
  have hsm : s ∈ nhds (0 : ℝ) := by rw [hs]; exact Metric.ball_mem_nhds 0 zero_lt_one
  have hmeas_F : ∀ᶠ x : ℝ in nhds 0, AEStronglyMeasurable (F x) μ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hF]
    have h1 : Continuous fun w : ℂ => u (Function.update (z + x • v) j w) :=
      hu.continuous.comp (continuous_update (z + x • v) j)
    have h2 : Measurable fun w : ℂ => (w - z j)⁻¹ := (measurable_id.sub measurable_const).inv
    exact (h1.measurable.mul h2).aestronglyMeasurable
  have hint_F0 : Integrable (F 0) μ := by
    have hFeq : F 0 = fun w : ℂ => u (Function.update z j w) / (w - z j) := by
      rw [hF]; funext w; simp
    rw [hFeq, hμ]
    exact integrableOn_fiberIntegrand R j hu.continuous z
  have hmeas_F'0 : AEStronglyMeasurable (F' 0) μ := by
    have hF'eq : F' 0 = fun w : ℂ => (fderiv ℝ u (Function.update z j w)) v / (w - z j) := by
      rw [hF']; funext w; simp
    rw [hF'eq]
    have h1 : Continuous fun w : ℂ => (fderiv ℝ u (Function.update z j w)) v :=
      (hfdc.comp (continuous_update z j)).clm_apply continuous_const
    have h2 : Measurable fun w : ℂ => (w - z j)⁻¹ := (measurable_id.sub measurable_const).inv
    exact (h1.measurable.mul h2).aestronglyMeasurable
  have hbound : ∀ᵐ w ∂μ, ∀ x ∈ s, ‖F' x w‖ ≤ bound w := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with w hw x hx
    have hpt : Function.update (z + x • v) j w ∈ K := by
      rw [hKdef]
      exact ⟨(x, w), ⟨Metric.ball_subset_closedBall hx, Metric.ball_subset_closedBall hw⟩, rfl⟩
    have hF'w : F' x w = (fderiv ℝ u (Function.update (z + x • v) j w)) v / (w - z j) := by
      rw [hF']
    rw [hF'w, hbounddef]
    have hle : ‖(fderiv ℝ u (Function.update (z + x • v) j w)) v‖ ≤ M * ‖v‖ := by
      calc ‖(fderiv ℝ u (Function.update (z + x • v) j w)) v‖
          ≤ ‖fderiv ℝ u (Function.update (z + x • v) j w)‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right (hMb _ hpt) (norm_nonneg v)
    calc ‖(fderiv ℝ u (Function.update (z + x • v) j w)) v / (w - z j)‖
        = ‖(fderiv ℝ u (Function.update (z + x • v) j w)) v‖ * ‖(w - z j)⁻¹‖ := by
          rw [norm_div, norm_inv, div_eq_mul_inv]
      _ ≤ (M * ‖v‖) * ‖(w - z j)⁻¹‖ := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = M * ‖v‖ * ‖(w - z j)⁻¹‖ := by ring
  have hint_bound : Integrable bound μ := by
    rw [hbounddef, hμ]
    exact (integrableOn_sub_inv_ball R (z j)).norm.const_mul (M * ‖v‖)
  have hderiv_F : ∀ᵐ w ∂μ, ∀ x ∈ s, HasDerivAt (fun x : ℝ => F x w) (F' x w) x := by
    refine Filter.Eventually.of_forall (fun w x _ => ?_)
    have hFeq : (fun x : ℝ => F x w)
        = fun x : ℝ => u (Function.update (z + x • v) j w) / (w - z j) := by
      rw [hF]
    have hF'eq : F' x w = (fderiv ℝ u (Function.update (z + x • v) j w)) v / (w - z j) := by
      rw [hF']
    rw [hFeq, hF'eq]
    have hlin : HasDerivAt (fun t : ℝ => Function.update (z + t • v) j w)
        (Function.update v j 0) x := by
      have hfun : (fun t : ℝ => Function.update (z + t • v) j w)
          = fun t : ℝ => Function.update z j w + t • Function.update v j 0 := by
        funext t l
        simp only [Pi.add_apply, Pi.smul_apply, Function.update_apply]
        by_cases hl : l = j <;> simp [hl]
      rw [hfun]
      simpa using
        ((hasDerivAt_id x).smul_const (Function.update v j 0)).const_add (Function.update z j w)
    have hpt : HasFDerivAt u (fderiv ℝ u (Function.update (z + x • v) j w))
        (Function.update (z + x • v) j w) := (hud.differentiableAt).hasFDerivAt
    have hcomp := hpt.comp_hasDerivAt x hlin
    rw [hwv] at hcomp
    exact hcomp.div_const (w - z j)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (𝕜 := ℝ) (E := ℂ) (bound := bound) (F := F) (x₀ := 0) (s := s)
    hsm hmeas_F hint_F0 hmeas_F'0 hbound hint_bound hderiv_F
  have hfun : (fun t : ℝ => fiberPot R j u (z + t • v))
      = fun t : ℝ => -(Real.pi : ℂ)⁻¹ * ∫ w, F t w ∂μ := by
    funext t
    rw [fiberPot_apply]
    simp only [hF, hμ, Pi.add_apply, Pi.smul_apply, hv, smul_zero, add_zero]
  rw [hfun]
  have h2 := hmain.2.const_mul (-(Real.pi : ℂ)⁻¹)
  simpa [hμ, hF'] using h2

/-- **The `fderiv` of the fixed-disc potential along a direction with `v j = 0`.**

At a point `z` where `fiberPot R j u` is (real) differentiable, its `fderiv` applied to a direction
`v` with `v j = 0` is the integral of the directional derivative of the integrand:
`fderiv ℝ (fiberPot R j u) z v = -(1/π) ∫_{‖w‖<R} (fderiv ℝ u (z with z j ↦ w)) v / (w - z j) dw`. -/
lemma fiberPot_fderiv_apply {n : ℕ} (R : ℝ) (j : Fin n)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) (z v : Fin n → ℂ) (hv : v j = 0)
    (hdiff : DifferentiableAt ℝ (fiberPot R j u) z) :
    fderiv ℝ (fiberPot R j u) z v
      = -(Real.pi : ℂ)⁻¹ * ∫ w in Metric.ball (0 : ℂ) R,
          (fderiv ℝ u (Function.update z j w)) v / (w - z j) := by
  have hc : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h1 : HasDerivAt (fun t : ℝ => fiberPot R j u (z + t • v))
      ((fderiv ℝ (fiberPot R j u) z) v) 0 := by
    have h0 : HasFDerivAt (fiberPot R j u) (fderiv ℝ (fiberPot R j u) z)
        (z + (0 : ℝ) • v) := by
      simpa using hdiff.hasFDerivAt
    exact h0.comp_hasDerivAt 0 hc
  exact h1.unique (fiberPot_hasDerivAt_direction R j hu z v hv)

/-- The integrand `w ↦ (fderiv ℝ u (z with z j ↦ w)) c / (w - z j)` is absolutely integrable on
the fixed disc `‖w‖ < R`, for `u` of class `C¹` and any fixed direction `c`. -/
lemma integrableOn_fderiv_apply_fiber {n : ℕ} (R : ℝ) (j : Fin n)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) (z c : Fin n → ℂ) :
    IntegrableOn (fun w : ℂ => (fderiv ℝ u (Function.update z j w)) c / (w - z j))
      (Metric.ball (0 : ℂ) R) := by
  have hfdc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hcont : Continuous fun w : ℂ => Function.update z j w := continuous_update z j
  set K : Set (Fin n → ℂ) :=
    (fun w : ℂ => Function.update z j w) '' Metric.closedBall (0 : ℂ) R with hKdef
  have hKc : IsCompact K := (isCompact_closedBall (0 : ℂ) R).image hcont
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn hfdc.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hMb : ∀ y ∈ K, ‖fderiv ℝ u y‖ ≤ M := fun y hy => le_trans (hM₀ y hy) (le_max_left _ _)
  refine ((integrableOn_sub_inv_ball R (z j)).norm.const_mul (M * ‖c‖)).mono' ?_ ?_
  · have h1 : Continuous fun w : ℂ => (fderiv ℝ u (Function.update z j w)) c :=
      (hfdc.comp hcont).clm_apply continuous_const
    have h2 : Measurable fun w : ℂ => (w - z j)⁻¹ := (measurable_id.sub measurable_const).inv
    exact (h1.measurable.mul h2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with w hw
    have hpt : Function.update z j w ∈ K := by
      rw [hKdef]; exact ⟨w, Metric.ball_subset_closedBall hw, rfl⟩
    calc ‖(fderiv ℝ u (Function.update z j w)) c / (w - z j)‖
        = ‖(fderiv ℝ u (Function.update z j w)) c‖ * ‖(w - z j)⁻¹‖ := by
          rw [norm_div, norm_inv, div_eq_mul_inv]
      _ ≤ (M * ‖c‖) * ‖(w - z j)⁻¹‖ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc ‖(fderiv ℝ u (Function.update z j w)) c‖
              ≤ ‖fderiv ℝ u (Function.update z j w)‖ * ‖c‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ M * ‖c‖ := mul_le_mul_of_nonneg_right (hMb _ hpt) (norm_nonneg c)

/-- **The fixed-disc potential commutes with the `∂̄`-derivatives in the other coordinates.**

For `k ≠ j`, `u : ℂⁿ → ℂ` of class `C¹` and every `z : ℂⁿ`,
`∂̄_k (fiberPot R j u) z = fiberPot R j (∂̄_k u) z`.

Indeed the kernel `1/(w - z j)` is independent of `z k` for `k ≠ j`, and the domain of integration
`‖w‖ < R` is fixed, so `∂̄_k` may be moved inside the integral (differentiation under the integral
sign, the derivative of the integrand being `∂̄_k u (z with z j replaced by w) / (w - z j)`, which is
dominated by `C ‖(w - z j)⁻¹‖`, integrable on the disc).  The hypothesis
`DifferentiableAt ℝ (fiberPot R j u) z` is the differentiability needed for `dbarCoord` to be
meaningful (`dbarCoord` is built from `fderiv ℝ`, which is `0` at non-differentiable points); it is
supplied by the companion smoothness statement for the potential. -/
theorem fiberPot_dbarCoord {n : ℕ} (R : ℝ) (j : Fin n) {k : Fin n} (hkj : k ≠ j)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) (z : Fin n → ℂ)
    (hdiff : DifferentiableAt ℝ (Work.NN.Core.fiberPot R j u) z) :
    Work.CR.Flat.dbarCoord k (Work.NN.Core.fiberPot R j u) z
      = Work.NN.Core.fiberPot R j (Work.CR.Flat.dbarCoord k u) z := by
  have hv1 : (Pi.single k (1 : ℂ) : Fin n → ℂ) j = 0 :=
    Pi.single_eq_of_ne (Ne.symm hkj) 1
  have hv2 : (Pi.single k (Complex.I : ℂ) : Fin n → ℂ) j = 0 := by
    rw [Pi.single_eq_of_ne (Ne.symm hkj)]
  have h1 := fiberPot_fderiv_apply R j hu z (Pi.single k 1) hv1 hdiff
  have h2 := fiberPot_fderiv_apply R j hu z (Pi.single k Complex.I) hv2 hdiff
  have hL : Work.CR.Flat.dbarCoord k (Work.NN.Core.fiberPot R j u) z
      = (1 / 2) * ((-(Real.pi : ℂ)⁻¹ *
            ∫ w in Metric.ball (0 : ℂ) R,
              (fderiv ℝ u (Function.update z j w)) (Pi.single k 1) / (w - z j))
          + Complex.I * (-(Real.pi : ℂ)⁻¹ *
            ∫ w in Metric.ball (0 : ℂ) R,
              (fderiv ℝ u (Function.update z j w)) (Pi.single k Complex.I) / (w - z j))) := by
    rw [Work.CR.Flat.dbarCoord, h1, h2]
  have hA1 := integrableOn_fderiv_apply_fiber R j hu z (Pi.single k 1)
  have hA2 := integrableOn_fderiv_apply_fiber R j hu z (Pi.single k Complex.I)
  have hB : (∫ w in Metric.ball (0 : ℂ) R,
        Work.CR.Flat.dbarCoord k u (Function.update z j w) / (w - z j))
      = (1 / 2) * ((∫ w in Metric.ball (0 : ℂ) R,
              (fderiv ℝ u (Function.update z j w)) (Pi.single k 1) / (w - z j))
          + Complex.I * (∫ w in Metric.ball (0 : ℂ) R,
              (fderiv ℝ u (Function.update z j w)) (Pi.single k Complex.I) / (w - z j))) := by
    have hgt : (fun w : ℂ => Work.CR.Flat.dbarCoord k u (Function.update z j w) / (w - z j))
        = fun w : ℂ =>
            (1 / 2) * ((fderiv ℝ u (Function.update z j w)) (Pi.single k 1) / (w - z j))
            + (1 / 2) * (Complex.I *
                ((fderiv ℝ u (Function.update z j w)) (Pi.single k Complex.I) / (w - z j))) := by
      funext w
      rw [Work.CR.Flat.dbarCoord]
      ring
    rw [hgt]
    rw [integral_add (hA1.const_mul (1 / 2)) ((hA2.const_mul Complex.I).const_mul (1 / 2))]
    simp only [MeasureTheory.integral_const_mul]
    ring
  rw [hL, fiberPot_apply, hB]
  ring

end Work.NN.Core
