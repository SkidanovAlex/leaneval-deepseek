import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter
open scoped Topology

namespace Work.Diff.EXT

/-- If `x₀` is not in the closure of `B`, the filter `𝓝[B] x₀` forces membership in the empty
intersection `B ∩ ball x₀ ε`, so `HasFDerivWithinAt` holds for every function and every
candidate derivative. -/
private theorem hasFDerivWithinAt_of_notMem_closure {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {B : Set P} {x₀ : P} (h : x₀ ∉ closure B) (f : P → W) (f' : P →L[ℝ] W) :
    HasFDerivWithinAt f f' B x₀ := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨ε, hε, hε'⟩ : ∃ ε > 0, ∀ y ∈ B, ε ≤ dist x₀ y := by
    by_contra hcontra
    push_neg at hcontra
    exact h (Metric.mem_closure_iff.mpr fun δ hδ => hcontra δ hδ)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds x₀ hε] with y hy hyB
  rw [Metric.mem_ball, dist_comm] at hy
  exact absurd hyB fun hyB => not_lt.mpr (hε' y hyB) hy

/-- If `x₀` lies in the closure of `B`, the pointwise Lipschitz-type bound with integrable
`bound` forces `F x₀` to be a.e. strongly measurable (it is an a.e. limit of the `F x`, `x ∈ B`)
and dominated by an integrable function, hence integrable. -/
private theorem integrable_at_closure_of_lipschitz
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ν : Measure ℝ} {B : Set P} {x₀ : P} {F : P → ℝ → W} {bound : ℝ → ℝ}
    (hF_int : ∀ x ∈ B, Integrable (F x) ν)
    (h_lip : ∀ᵐ a ∂ν, ∀ x ∈ B, ‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖)
    (hb_int : Integrable bound ν)
    (hx₀ : x₀ ∈ closure B) :
    Integrable (F x₀) ν := by
  have hseq : ∀ n : ℕ, ∃ x ∈ B, ‖x - x₀‖ < ((n : ℝ) + 1)⁻¹ := fun n => by
    obtain ⟨x, hxB, hx⟩ := Metric.mem_closure_iff.mp hx₀ ((n : ℝ) + 1)⁻¹ (by positivity)
    exact ⟨x, hxB, by rw [dist_eq_norm, norm_sub_rev] at hx; exact hx⟩
  choose xs hxsB hxs using hseq
  have hxs_tendsto : Tendsto xs atTop (𝓝 x₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hxs n))
      (by simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdiff_tendsto : Tendsto (fun n => ‖xs n - x₀‖) atTop (𝓝 0) := by
    have h := (hxs_tendsto.sub (tendsto_const_nhds (x := x₀))).norm
    simpa using h
  have haesm : AEStronglyMeasurable (F x₀) ν := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hF_int _ (hxsB n)).aestronglyMeasurable) ?_
    filter_upwards [h_lip] with a ha
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => ha _ (hxsB n))
      (by simpa using hdiff_tendsto.const_mul (bound a))
  refine integrable_of_norm_sub_le (f₀ := F (xs 0)) (f₁ := F x₀)
    (g := fun a => |bound a| * ‖xs 0 - x₀‖) haesm (hF_int _ (hxsB 0)) ?_ ?_
  · simpa only [Real.norm_eq_abs] using hb_int.norm.mul_const ‖xs 0 - x₀‖
  · filter_upwards [h_lip] with a ha
    calc ‖F (xs 0) a - F x₀ a‖ ≤ bound a * ‖xs 0 - x₀‖ := ha _ (hxsB 0)
      _ ≤ |bound a| * ‖xs 0 - x₀‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)

/-- Differentiation under the integral sign, Fréchet form, on a set: the core dominated
convergence argument. -/
private theorem hasFDerivWithinAt_integral_of_dominated
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {ν : Measure ℝ} {B : Set P} {x₀ : P} {F : P → ℝ → W}
    {F' : ℝ → P →L[ℝ] W} {bound : ℝ → ℝ}
    (hF_int : ∀ x ∈ B, Integrable (F x) ν)
    (hF₀_int : Integrable (F x₀) ν)
    (hF'_int : Integrable F' ν)
    (h_lip : ∀ᵐ a ∂ν, ∀ x ∈ B, ‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖)
    (hb_int : Integrable bound ν)
    (h_diff : ∀ᵐ a ∂ν, HasFDerivWithinAt (fun x => F x a) (F' a) B x₀) :
    HasFDerivWithinAt (fun x => ∫ a, F x a ∂ν) (∫ a, F' a ∂ν) B x₀ := by
  have hlim : Tendsto
      (fun x : P => ∫ a, ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀)) ∂ν)
      (𝓝[B] x₀) (𝓝 0) := by
    rw [show (0 : W) = ∫ a, (0 : W) ∂ν by simp]
    refine tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝[B] x₀)
      (F := fun x a => ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))) (f := fun _ => 0)
      (fun a => ‖bound a‖ + ‖F' a‖) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (((hF_int x hx).aestronglyMeasurable.sub hF₀_int.aestronglyMeasurable).sub
        (hF'_int.aestronglyMeasurable.apply_continuousLinearMap (x - x₀))).const_smul _
    · filter_upwards [self_mem_nhdsWithin] with x hx
      filter_upwards [h_lip] with a ha
      have hb := ha x hx
      have key : ‖F x a - F x₀ a - F' a (x - x₀)‖ ≤ (‖bound a‖ + ‖F' a‖) * ‖x - x₀‖ := by
        calc ‖F x a - F x₀ a - F' a (x - x₀)‖
            ≤ ‖F x a - F x₀ a‖ + ‖F' a (x - x₀)‖ := norm_sub_le _ _
          _ ≤ bound a * ‖x - x₀‖ + ‖F' a‖ * ‖x - x₀‖ :=
              add_le_add hb ((F' a).le_opNorm _)
          _ = (bound a + ‖F' a‖) * ‖x - x₀‖ := by ring
          _ ≤ (‖bound a‖ + ‖F' a‖) * ‖x - x₀‖ :=
              mul_le_mul_of_nonneg_right
                (add_le_add (Real.le_norm_self (bound a)) le_rfl) (norm_nonneg _)
      calc ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖
          = ‖x - x₀‖⁻¹ * ‖F x a - F x₀ a - F' a (x - x₀)‖ :=
            norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg (x - x₀))) _
        _ ≤ ‖x - x₀‖⁻¹ * ((‖bound a‖ + ‖F' a‖) * ‖x - x₀‖) :=
            mul_le_mul_of_nonneg_left key (inv_nonneg.mpr (norm_nonneg (x - x₀)))
        _ = (‖bound a‖ + ‖F' a‖) * (‖x - x₀‖⁻¹ * ‖x - x₀‖) := by ring
        _ ≤ (‖bound a‖ + ‖F' a‖) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rcases eq_or_ne ‖x - x₀‖ 0 with h | h
            · simp [h]
            · rw [inv_mul_cancel₀ h]
        _ = ‖bound a‖ + ‖F' a‖ := mul_one _
    · exact hb_int.norm.add hF'_int.norm
    · filter_upwards [h_diff] with a ha
      rw [hasFDerivWithinAt_iff_tendsto] at ha
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hfun : (fun x' : P => ‖‖x' - x₀‖⁻¹ • (F x' a - F x₀ a - F' a (x' - x₀))‖)
          = fun x' : P => ‖x' - x₀‖⁻¹ * ‖F x' a - F x₀ a - F' a (x' - x₀)‖ := by
        funext x'
        rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg (x' - x₀)))]
      rw [hfun]
      exact ha
  rw [hasFDerivWithinAt_iff_tendsto]
  have hlim' : Tendsto
      (fun x : P => ‖∫ a, ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀)) ∂ν‖)
      (𝓝[B] x₀) (𝓝 0) := by simpa using hlim.norm
  refine Tendsto.congr' ?_ hlim'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h1 : ∫ a, F x a - F x₀ a ∂ν = (∫ a, F x a ∂ν) - ∫ a, F x₀ a ∂ν :=
    integral_sub (hF_int x hx) hF₀_int
  have h2 : ∫ a, F x a - F x₀ a - F' a (x - x₀) ∂ν
      = (∫ a, F x a - F x₀ a ∂ν) - ∫ a, F' a (x - x₀) ∂ν :=
    integral_sub ((hF_int x hx).sub hF₀_int) (hF'_int.apply_continuousLinearMap (x - x₀))
  have hInt : ∫ a, ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀)) ∂ν
      = ‖x - x₀‖⁻¹ • ((∫ a, F x a ∂ν) - (∫ a, F x₀ a ∂ν)
          - (∫ a, F' a ∂ν) (x - x₀)) := by
    rw [integral_smul, h2, h1, ← ContinuousLinearMap.integral_apply hF'_int (x - x₀)]
  rw [hInt, norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg (x - x₀)))]

theorem hasFDerivWithinAt_intervalIntegral_of_lipschitz
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {B : Set P} {x₀ : P} {F : P → ℝ → W} {F' : ℝ → P →L[ℝ] W} {bound : ℝ → ℝ}
    (hF_int : ∀ x ∈ B, IntervalIntegrable (F x) MeasureTheory.volume (0 : ℝ) 1)
    (hF'_int : IntervalIntegrable F' MeasureTheory.volume (0 : ℝ) 1)
    (hF'_meas : MeasureTheory.AEStronglyMeasurable F'
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)))
    (h_lip : Filter.Eventually (fun a : ℝ => ∀ x ∈ B, ‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖)
      (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1))))
    (bound_int : IntervalIntegrable bound MeasureTheory.volume (0 : ℝ) 1)
    (h_diff : Filter.Eventually (fun a : ℝ => HasFDerivWithinAt (fun x => F x a) (F' a) B x₀)
      (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)))) :
    HasFDerivWithinAt (fun x => intervalIntegral (fun a => F x a) (0 : ℝ) 1 MeasureTheory.volume)
      (intervalIntegral F' (0 : ℝ) 1 MeasureTheory.volume) B x₀ := by
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  rw [Set.uIoc_of_le hle] at hF'_meas h_lip h_diff
  have hF_int' : ∀ x ∈ B, Integrable (F x) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    fun x hx => (hF_int x hx).1
  have hF'_int' : Integrable F' (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := hF'_int.1
  have hb_int' : Integrable bound (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    bound_int.1
  simp only [intervalIntegral.integral_of_le hle]
  by_cases hx₀ : x₀ ∈ closure B
  · exact hasFDerivWithinAt_integral_of_dominated hF_int'
      (integrable_at_closure_of_lipschitz hF_int' h_lip hb_int' hx₀) hF'_int' h_lip hb_int' h_diff
  · exact hasFDerivWithinAt_of_notMem_closure hx₀ _ _

end Work.Diff.EXT
