import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.H2.sinCosSqInt
import Submission.Work.FTS_EllLimOK.ProducerH.H2.wRateArithAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open MeasureTheory

/-- `∫_x^{π/2} sin t · cos²t dt = cos³x / 3`. -/
theorem integral_sin_mul_cos_sq (x : ℝ) :
    ∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 = (Real.cos x) ^ 3 / 3 := by
  have hderiv : ∀ t ∈ Set.uIcc x (Real.pi / 2),
      HasDerivAt (fun t : ℝ => -((Real.cos t) ^ 3) / 3)
        (Real.sin t * (Real.cos t) ^ 2) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (Real.cos t) ^ 3)
        (3 * (Real.cos t) ^ 2 * (-Real.sin t)) t := by
      have h := (Real.hasDerivAt_cos t).pow 3
      convert h using 1
    have h2 : HasDerivAt (fun t : ℝ => -((Real.cos t) ^ 3) / 3)
        ((3 * (Real.cos t) ^ 2 * (-Real.sin t)) * (-(1 / 3))) t := by
      have h := (h1.neg).div_const 3
      convert h using 1
      ring
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun t : ℝ => Real.sin t * (Real.cos t) ^ 2).intervalIntegrable _ _)]
  simp [Real.cos_pi_div_two]
  ring

/-- The ordered (`θ ≤ θ'`) case of the modulus estimate. -/
private theorem wRateOrdered {β L c₁ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L)
    {G : ℝ → ℝ} (hGc : ContinuousOn G (Set.Ioo 0 (Real.pi / 2)))
    (h1 : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), |G t - c₁| ≤ L * (Real.pi / 2 - t) ^ β)
    {θ θ' : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2))
    (hle : θ ≤ θ') :
    |((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
      - ((Real.cos θ') ^ 3)⁻¹ * (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)|
      ≤ 4 * L * |θ - θ'| ^ β := by
  have hθle : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  have hθ'le : θ' ≤ Real.pi / 2 := le_of_lt hθ'.2
  have hcont : ContinuousOn (fun t : ℝ => G t - c₁) (Set.Ioo 0 (Real.pi / 2)) :=
    hGc.sub continuousOn_const
  have hbnd : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), |G t - c₁| ≤ L * (Real.pi / 2) ^ β := by
    intro t ht
    refine (h1 t ht).trans (mul_le_mul_of_nonneg_left ?_ hL)
    exact Real.rpow_le_rpow (by linarith [ht.2]) (by linarith [ht.1]) hβ.le
  have hInt : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      IntervalIntegrable (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        volume x (Real.pi / 2) :=
    fun x hx => sinCosSqInt hcont hbnd hx.1 (le_of_lt hx.2)
  -- split off the constant `c₁`
  have hsplit : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
        = (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
          + c₁ * ((Real.cos x) ^ 3 / 3) := by
    intro x hx
    have hI1 := hInt x hx
    have hI2 : IntervalIntegrable (fun t : ℝ => c₁ * (Real.sin t * (Real.cos t) ^ 2))
        volume x (Real.pi / 2) :=
      (by fun_prop : Continuous fun t : ℝ => c₁ * (Real.sin t * (Real.cos t) ^ 2)).intervalIntegrable _ _
    rw [show (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
        = ∫ t in x..(Real.pi / 2),
            (Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)
              + c₁ * (Real.sin t * (Real.cos t) ^ 2))
        from intervalIntegral.integral_congr (fun t _ => by ring)]
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      integral_sin_mul_cos_sq x]
  -- the resulting identity for `W`
  have hWid : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      ((Real.cos x) ^ 3)⁻¹ * (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
          - c₁ / 3
        = ((Real.cos x) ^ 3)⁻¹
          * (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)) := by
    intro x hx
    rw [hsplit x hx]
    have hcx : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩)
    field_simp
    ring
  -- pointwise bound in the `π/2`-endpoint regime (distance `≤ Real.pi/2 - θ'`)
  have hpt' : ∀ t ∈ Set.Ioo θ' (Real.pi / 2),
      |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        ≤ L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hθ'.1 ht.1
    have ht1 : t < Real.pi / 2 := ht.2
    have hsin : 0 ≤ Real.sin t :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos t :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht1⟩)
    have hsq : 0 ≤ Real.sin t * (Real.cos t) ^ 2 := mul_nonneg hsin (pow_nonneg hcos 2)
    have hGt : |G t - c₁| ≤ L * (Real.pi / 2 - t) ^ β := h1 t ⟨ht0, ht1⟩
    have hdt : Real.pi / 2 - t ≤ Real.pi / 2 - θ' := by linarith [ht.1]
    have hd0 : 0 ≤ Real.pi / 2 - t := by linarith [ht1]
    have hrp : (Real.pi / 2 - t) ^ β ≤ (Real.pi / 2 - θ') ^ β := Real.rpow_le_rpow hd0 hdt hβ.le
    calc |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        = (Real.sin t * (Real.cos t) ^ 2) * |G t - c₁| := by
          rw [abs_mul, abs_of_nonneg hsq]
      _ ≤ (Real.sin t * (Real.cos t) ^ 2) * (L * (Real.pi / 2 - t) ^ β) :=
          mul_le_mul_of_nonneg_left hGt hsq
      _ ≤ (Real.sin t * (Real.cos t) ^ 2) * (L * (Real.pi / 2 - θ') ^ β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hL) hsq
      _ = L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2) := by ring
  -- pointwise bound on `(θ, θ')` (distance `≤ Real.pi/2 - θ`)
  have hpt : ∀ t ∈ Set.Ioo θ θ',
      |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        ≤ L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hθ.1 ht.1
    have ht1 : t < Real.pi / 2 := by linarith [ht.2, hθ'le]
    have hsin : 0 ≤ Real.sin t :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos t :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht1⟩)
    have hsq : 0 ≤ Real.sin t * (Real.cos t) ^ 2 := mul_nonneg hsin (pow_nonneg hcos 2)
    have hGt : |G t - c₁| ≤ L * (Real.pi / 2 - t) ^ β := h1 t ⟨ht0, ht1⟩
    have hdt : Real.pi / 2 - t ≤ Real.pi / 2 - θ := by linarith [ht.1]
    have hd0 : 0 ≤ Real.pi / 2 - t := by linarith [ht1]
    have hrp : (Real.pi / 2 - t) ^ β ≤ (Real.pi / 2 - θ) ^ β := Real.rpow_le_rpow hd0 hdt hβ.le
    calc |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        = (Real.sin t * (Real.cos t) ^ 2) * |G t - c₁| := by
          rw [abs_mul, abs_of_nonneg hsq]
      _ ≤ (Real.sin t * (Real.cos t) ^ 2) * (L * (Real.pi / 2 - t) ^ β) :=
          mul_le_mul_of_nonneg_left hGt hsq
      _ ≤ (Real.sin t * (Real.cos t) ^ 2) * (L * (Real.pi / 2 - θ) ^ β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hL) hsq
      _ = L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := by ring
  -- the endpoint bound at `θ'`
  have htail : |∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
      ≤ L * (Real.pi / 2 - θ') ^ β * (Real.cos θ') ^ 3 / 3 := by
    have hf : IntervalIntegrable (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        volume θ' (Real.pi / 2) := hInt θ' hθ'
    have hb : IntervalIntegrable
        (fun t : ℝ => L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2))
        volume θ' (Real.pi / 2) :=
      (by fun_prop : Continuous fun t : ℝ =>
        L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2)).intervalIntegrable _ _
    have h2' : (∫ t in θ'..(Real.pi / 2), |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|)
        ≤ ∫ t in θ'..(Real.pi / 2),
            L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hθ'le hf.abs hb hpt'
    have h3' : (∫ t in θ'..(Real.pi / 2),
          L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2))
        = L * (Real.pi / 2 - θ') ^ β * ((Real.cos θ') ^ 3 / 3) := by
      rw [intervalIntegral.integral_const_mul, integral_sin_mul_cos_sq θ']
    calc |∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        ≤ ∫ t in θ'..(Real.pi / 2), |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)| :=
          intervalIntegral.abs_integral_le_integral_abs hθ'le
      _ ≤ ∫ t in θ'..(Real.pi / 2),
            L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2) := h2'
      _ = L * (Real.pi / 2 - θ') ^ β * ((Real.cos θ') ^ 3 / 3) := h3'
      _ = L * (Real.pi / 2 - θ') ^ β * (Real.cos θ') ^ 3 / 3 := by ring
  -- the intermediate value of the primitive of `sin · cos²`
  have hcosint : (∫ t in θ..θ', Real.sin t * (Real.cos t) ^ 2)
      = (Real.cos θ) ^ 3 / 3 - (Real.cos θ') ^ 3 / 3 := by
    have hc : Continuous fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 := by fun_prop
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) θ θ')
      (hc.intervalIntegrable (μ := volume) θ' (Real.pi / 2))
    rw [integral_sin_mul_cos_sq θ, integral_sin_mul_cos_sq θ'] at hadd
    linarith
  -- the two-point bound
  have hFbound : |(∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
      - (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))|
      ≤ L * (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 - (Real.cos θ') ^ 3) / 3 := by
    have hff : IntervalIntegrable (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        volume θ θ' :=
      (hInt θ hθ).mono_set (by
        rw [Set.uIcc_of_le hle, Set.uIcc_of_le hθle]
        exact Set.Icc_subset_Icc le_rfl hθ'le)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hff (hInt θ' hθ')
    have hdiff : (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        - (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        = ∫ t in θ..θ', Real.sin t * (Real.cos t) ^ 2 * (G t - c₁) := by linarith
    have hb : IntervalIntegrable
        (fun t : ℝ => L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2))
        volume θ θ' :=
      (by fun_prop : Continuous fun t : ℝ =>
        L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2)).intervalIntegrable _ _
    have h2 : (∫ t in θ..θ', |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|)
        ≤ ∫ t in θ..θ', L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hle hff.abs hb hpt
    have h3 : (∫ t in θ..θ', L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2))
        = L * (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3 - (Real.cos θ') ^ 3 / 3) := by
      rw [intervalIntegral.integral_const_mul, hcosint]
    rw [hdiff]
    calc |∫ t in θ..θ', Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        ≤ ∫ t in θ..θ', |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)| :=
          intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in θ..θ', L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := h2
      _ = L * (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3 - (Real.cos θ') ^ 3 / 3) := h3
      _ = L * (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 - (Real.cos θ') ^ 3) / 3 := by ring
  -- final algebra
  have hcos_pos' : 0 < Real.cos θ' :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
  have hcosle : Real.cos θ' ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ.1)
      (by linarith [hθ'.2, Real.pi_pos]) hle
  have hδ'nn : 0 ≤ Real.pi / 2 - θ' := by linarith [hθ'.2]
  have hδδ : Real.pi / 2 - θ' ≤ Real.pi / 2 - θ := by linarith [hle]
  have hδpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hcoslow : 2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (by linarith [hθ.2])
      (by linarith [hθ.1])
    have h2 : Real.cos θ = Real.sin (Real.pi / 2 - θ) := by
      have := Real.cos_pi_div_two_sub (Real.pi / 2 - θ)
      rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ from by ring] at this
    linarith [h, h2]
  have hsub : Real.cos θ - Real.cos θ' ≤ θ' - θ := by
    have h := Real.abs_cos_sub_cos_le θ θ'
    rw [abs_of_nonneg (sub_nonneg.mpr hcosle),
      abs_of_nonpos (sub_nonpos.mpr hle)] at h
    linarith
  have hdδ : θ' - θ ≤ Real.pi / 2 - θ := by linarith [hθ'le]
  have hsubst : ((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
      - ((Real.cos θ') ^ 3)⁻¹
        * (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
      = ((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        - ((Real.cos θ') ^ 3)⁻¹
          * (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)) := by
    have hA := hWid θ hθ
    have hB := hWid θ' hθ'
    linarith
  rw [hsubst, abs_of_nonpos (sub_nonpos.mpr hle),
    show -(θ - θ') = θ' - θ from by ring]
  exact wRateArithAux hL hcos_pos' hcosle hδ'nn hδδ hδpos hβ hβ1 hcoslow hsub hdδ hFbound htail

theorem wRateModulusUnif {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {L c₁ : ℝ}, 0 ≤ L → ∀ {G : ℝ → ℝ},
      ContinuousOn G (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |G t - c₁| ≤ L * (Real.pi / 2 - t) ^ β) →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
          - ((Real.cos θ') ^ 3)⁻¹
            * (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)|
          ≤ C * L * |θ - θ'| ^ β := by
  refine ⟨4, by norm_num, ?_⟩
  intro L c₁ hL G hGc h1 θ hθ θ' hθ'
  rcases le_total θ θ' with hle | hle
  · exact wRateOrdered hβ hβ1 hL hGc h1 hθ hθ' hle
  · have h2 := wRateOrdered hβ hβ1 hL hGc h1 hθ' hθ hle
    rw [abs_sub_comm, abs_sub_comm θ θ']
    exact h2

end Work.FTS_EllLimOK.ProducerH.H2
