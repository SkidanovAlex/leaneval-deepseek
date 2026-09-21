import Mathlib
import Submission.Work.OddExistence.Manifest.hasDerivAt_G2M_apply

/-!
# Differentiation under the Abel average, with an extra weight `(1 - τ)`

`Work.OddExistence.Manifest.hasDerivAt_abelAvg_scalar` differentiates the Abel average
`u ↦ ∫₀¹ (√(τ(1-τ)))⁻¹ K (u + τ(σ-u)) dτ`.  Iterating it to get the *second* `u`-derivative of
`G2M` requires the same statement for the integrand `(1-τ)·K`, which is what this file provides:
the derivative of `u ↦ ∫₀¹ (√(τ(1-τ)))⁻¹ ((1-τ) K (u+τ(σ-u))) dτ` is the Abel average of
`(1-τ)² ∂K`.  The proof is the proof of the unweighted version with `1 - τ` carried through; at
`τ = 1` both the value and the derivative integrands vanish.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

noncomputable section

set_option maxHeartbeats 800000

/-- **Differentiation under the Abel average, weighted version.**  If `K : ℝ → ℝ` is measurable,
bounded along the moving point `x + τ(σ-x)`, differentiable there, and its derivative weighted by
`1 - τ` is bounded by `C`, then the Abel average of `(1-τ)K` is differentiable at `s`, with
derivative the Abel-weighted average of `(1-τ)² ∂K`. -/
theorem hasDerivAt_abelAvg_scalar_weight {K : ℝ → ℝ} (hK : Measurable K) {s σ : ℝ}
    {δ C : ℝ} (hδ : 0 < δ)
    (hbdK : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖K (x + τ * (σ - x))‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ K (x + τ * (σ - x)))
    (hbound : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) * deriv K (x + τ * (σ - x))‖ ≤ C) :
    HasDerivAt (fun u : ℝ =>
        ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * K (u + τ * (σ - u))))
      (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) ^ 2 * deriv K (s + τ * (σ - s)))) s := by
  have hC0 : 0 ≤ C := by
    have h := hbound s ⟨by linarith, by linarith⟩ 1 ⟨zero_le_one, le_rfl⟩
    simpa using h
  have hw_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0 : ℝ) 1 :=
    Commons.Geometry.Ulam.intervalIntegrable_abel_weight
  have hw_norm : ∀ τ : ℝ, ‖(Real.sqrt (τ * (1 - τ)))⁻¹‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ := by
    intro τ
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hw_meas : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
    (Work.OddVolterra.measurable_sqrt_real.comp
      (measurable_id.mul (measurable_const.sub measurable_id))).inv
  set F : ℝ → ℝ → ℝ :=
    fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * K (x + τ * (σ - x))) with hFdef
  set F' : ℝ → ℝ → ℝ :=
    fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * deriv K (x + τ * (σ - x)))
    with hF'def
  have hF_meas_all : ∀ x : ℝ,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    intro x
    have hm : Measurable (fun τ : ℝ => K (x + τ * (σ - x))) :=
      hK.comp (by fun_prop : Measurable fun τ : ℝ => x + τ * (σ - x))
    exact (hw_meas.mul ((measurable_const.sub measurable_id).mul hm)).aestronglyMeasurable
  have hF_meas : ∀ᶠ x in 𝓝 s,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    Filter.Eventually.of_forall hF_meas_all
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    have hm : Measurable (fun τ : ℝ => deriv K (s + τ * (σ - s))) :=
      (measurable_deriv (𝕜 := ℝ) K).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
    exact (hw_meas.mul (((measurable_const.sub measurable_id).pow_const 2).mul
      hm)).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F s) volume (0:ℝ) 1 := by
    refine (hw_int.mul_const C).mono_fun' (hF_meas_all s) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
    by_cases h1 : τ = 1
    · subst h1
      have hz : F s 1 = 0 := by
        simp only [hFdef]
        norm_num
      rw [hz]
      simp
    have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
      exact ⟨le_of_lt hτ.1, lt_of_le_of_ne hτ.2 h1⟩
    have h1τ0 : (0:ℝ) ≤ 1 - τ := by linarith [hτIco.2.le]
    have h1τ1 : (1:ℝ) - τ ≤ 1 := by linarith [hτIco.1]
    have hKb := hbdK s ⟨by linarith, by linarith⟩ τ hτIco
    rw [Real.norm_eq_abs] at hKb
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hval : ‖(1 - τ) * K (s + τ * (σ - s))‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1τ0]
      calc (1 - τ) * |K (s + τ * (σ - s))| ≤ 1 * C :=
            mul_le_mul h1τ1 hKb (abs_nonneg _) (by norm_num)
        _ = C := by ring
    calc ‖F s τ‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖(1 - τ) * K (s + τ * (σ - s))‖ := by
          simp only [hFdef, norm_mul, hw_norm]
      _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hval hw
  have h_bound : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo (s - δ) (s + δ),
        ‖F' x τ‖ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      exact ⟨le_of_lt hτ.1, hτ.2⟩
    have hKb := hbound x hx τ hτIcc
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hτIcc.2] : (0:ℝ) ≤ 1 - τ)] at hKb
    have h1τ0 : (0:ℝ) ≤ 1 - τ := by linarith [hτIcc.2]
    have h1τ1 : (1:ℝ) - τ ≤ 1 := by linarith [hτIcc.1]
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hval : ‖(1 - τ) ^ 2 * deriv K (x + τ * (σ - x))‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h1τ0]
      calc (1 - τ) ^ 2 * |deriv K (x + τ * (σ - x))|
          = (1 - τ) * ((1 - τ) * |deriv K (x + τ * (σ - x))|) := by ring
        _ ≤ 1 * C := mul_le_mul h1τ1 hKb (by positivity) (by norm_num)
        _ = C := by ring
    calc ‖F' x τ‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖(1 - τ) ^ 2 * deriv K (x + τ * (σ - x))‖ := by
          simp only [hF'def, norm_mul, hw_norm]
      _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hval hw
  have hbound_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C) volume (0:ℝ) 1 :=
    hw_int.mul_const C
  have h_diff : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo (s - δ) (s + δ), HasDerivAt (fun x => F x τ) (F' x τ) x := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
    by_cases h1 : τ = 1
    · subst h1
      have hzero : (fun x : ℝ => F x 1) = fun _ : ℝ => (0 : ℝ) := by
        funext y
        simp only [hFdef]
        norm_num
      have hzero' : F' x 1 = 0 := by
        simp only [hF'def]
        norm_num
      rw [hzero, hzero']
      exact hasDerivAt_const x 0
    · have hτlt : τ < 1 := lt_of_le_of_ne hτIcc.2 h1
      have hinner : HasDerivAt (fun x : ℝ => x + τ * (σ - x)) (1 - τ) x := by
        have hfun : (fun x : ℝ => x + τ * (σ - x)) = fun x : ℝ => (1 - τ) * x + τ * σ := by
          funext y; ring
        rw [hfun]
        simpa using ((hasDerivAt_id x).const_mul (1 - τ)).add_const (τ * σ)
      have houter : HasDerivAt K (deriv K (x + τ * (σ - x))) (x + τ * (σ - x)) :=
        (hdiff x hx τ ⟨hτIcc.1, hτlt⟩).hasDerivAt
      have hcomp := houter.scomp (𝕜 := ℝ) (F := ℝ) (x := x) hinner
      have hfull := (hcomp.const_mul (1 - τ)).const_mul (Real.sqrt (τ * (1 - τ)))⁻¹
      refine hfull.congr_deriv ?_
      simp only [hFdef, hF'def]
      ring
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := volume)
    (F := F) (F' := F') (x₀ := s) (s := Set.Ioo (s - δ) (s + δ))
    (bound := fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C)
    (isOpen_Ioo.mem_nhds ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa only [hFdef, hF'def] using hmain.2

end

end Work.OddVolterra.WinData
