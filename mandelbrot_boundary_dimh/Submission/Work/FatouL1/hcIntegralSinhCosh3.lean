import Mathlib

/-!
# The integral of `|sinh (π (y - a))| / cosh (π (y - a)) ^ 3`

For every real `a`,

  `∫ y, |sinh (π (y - a))| / cosh (π (y - a)) ^ 3 = 1 / π`

and the integrand is integrable.  The proof reduces, by the change of variables
`u = π (y - a)`, to the value `∫_ℝ |sinh u| / cosh u ^ 3 du = 1`, which is obtained
by splitting `ℝ` at `0` (the antiderivative of `sinh u / cosh u ^ 3` is
`-1 / (2 * cosh u ^ 2)`) and using the fundamental theorem of calculus on the
half lines.  Since the integrand is even, `integral_comp_abs` gives the value on
`ℝ` from the value on `(0, ∞)`.
-/

namespace Work.FatouL1

open MeasureTheory Set Filter
open scoped Real Topology

/-- The even integrand `|sinh u| / cosh u ^ 3`. -/
private noncomputable def φ (u : ℝ) : ℝ := |Real.sinh u| / Real.cosh u ^ 3

/-- `-1 / (2 * cosh x ^ 2)` is an antiderivative of `sinh x / cosh x ^ 3`. -/
private lemma hasDerivAt_sech2 (x : ℝ) :
    HasDerivAt (fun u : ℝ => -(1/2) * (Real.cosh u)⁻¹ ^ 2)
      (Real.sinh x / Real.cosh x ^ 3) x := by
  have h1 : HasDerivAt (fun u : ℝ => (Real.cosh u)⁻¹ ^ 2)
      (2 * (Real.cosh x)⁻¹ ^ 1 * (-(Real.sinh x) / Real.cosh x ^ 2)) x :=
    ((Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne').pow 2
  have h2 := h1.const_mul (-(1/2))
  convert h2 using 1
  field_simp

/-- `-(1/2) * cosh u⁻²` tends to `0` at `+∞`. -/
private lemma tendsto_neg_half_sech2 :
    Tendsto (fun u : ℝ => -(1/2) * (Real.cosh u)⁻¹ ^ 2) atTop (𝓝 0) := by
  have hcosh : Tendsto Real.cosh atTop atTop := by
    have hle : ∀ x : ℝ, Real.exp x / 2 ≤ Real.cosh x := by
      intro x
      rw [Real.cosh_eq]
      have := Real.exp_pos (-x)
      linarith
    have h_exp : Tendsto (fun x : ℝ => Real.exp x / 2) atTop atTop :=
      Filter.Tendsto.atTop_div_const (by norm_num) Real.tendsto_exp_atTop
    exact Filter.tendsto_atTop_mono hle h_exp
  have h1 : Tendsto (fun u : ℝ => (Real.cosh u)⁻¹) atTop (𝓝 0) := hcosh.inv_tendsto_atTop
  have h2 : Tendsto (fun u : ℝ => (Real.cosh u)⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using h1.pow 2
  have h3 := h2.const_mul (-(1/2))
  simpa only [neg_mul, mul_zero] using h3

/-- `∫_{(0,∞)} sinh x / cosh x ^ 3 dx = 1/2`. -/
private lemma integral_Ioi_sech_deriv :
    ∫ x in Ioi (0 : ℝ), Real.sinh x / Real.cosh x ^ 3 = 1/2 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ => -(1/2) * (Real.cosh u)⁻¹ ^ 2)
      (Real.sinh x / Real.cosh x ^ 3) x := fun x _ => hasDerivAt_sech2 x
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ Real.sinh x / Real.cosh x ^ 3 := by
    intro x hx
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    have hc : 0 < Real.cosh x ^ 3 := by positivity
    positivity
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (l := 0)
    hderiv hpos tendsto_neg_half_sech2
  simpa [Real.cosh_zero] using h

/-- `sinh x / cosh x ^ 3` is integrable on `(0, ∞)`. -/
private lemma integrableOn_Ioi_sech_deriv :
    IntegrableOn (fun x : ℝ => Real.sinh x / Real.cosh x ^ 3) (Ioi (0 : ℝ)) := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ => -(1/2) * (Real.cosh u)⁻¹ ^ 2)
      (Real.sinh x / Real.cosh x ^ 3) x := fun x _ => hasDerivAt_sech2 x
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ Real.sinh x / Real.cosh x ^ 3 := by
    intro x hx
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    have hc : 0 < Real.cosh x ^ 3 := by positivity
    positivity
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (a := 0) (l := 0)
    hderiv hpos tendsto_neg_half_sech2

/-- `φ` is even. -/
private lemma φ_neg (x : ℝ) : φ (-x) = φ x := by simp [φ]

/-- `φ` is integrable on `ℝ`. -/
private lemma integrable_φ : Integrable φ := by
  have hφ_pos : IntegrableOn φ (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_sech_deriv.congr_fun
      (fun x hx => by simp [φ, abs_of_pos (Real.sinh_pos_iff.mpr hx)]) measurableSet_Ioi
  have hφ_neg : IntegrableOn φ (Iio (0 : ℝ)) := by
    have hA : MeasurableEmbedding (fun x : ℝ => -x) :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hmap : Measure.map (fun x : ℝ => -x) volume = volume :=
      MeasureTheory.Measure.map_neg_eq_self volume
    have h2 : IntegrableOn (fun x : ℝ => φ (-x)) ((fun x : ℝ => -x) ⁻¹' Ioi (0 : ℝ)) volume := by
      simpa only [Function.comp_def] using
        (hA.integrableOn_map_iff (f := φ) (s := Ioi (0 : ℝ)) (μ := volume)).mp
          (by rw [hmap]; exact hφ_pos)
    have h1 : IntegrableOn (fun x : ℝ => φ (-x)) (Iio (0 : ℝ)) := by
      rwa [show (fun x : ℝ => -x) ⁻¹' Ioi (0 : ℝ) = Iio 0 from by ext x; simp] at h2
    exact h1.congr_fun (fun x _ => φ_neg x) measurableSet_Iio
  have hφ_pos' : IntegrableOn φ (Ici (0 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (b := 0) (f := φ)).mpr hφ_pos
  have hunion : IntegrableOn φ (Iio (0 : ℝ) ∪ Ici (0 : ℝ)) := hφ_neg.union hφ_pos'
  rwa [Iio_union_Ici, integrableOn_univ] at hunion

/-- `∫_ℝ |sinh u| / cosh u ^ 3 du = 1`. -/
private lemma integral_φ : ∫ u, φ u = 1 := by
  have hcongr : ∫ u, φ u = ∫ u, (fun x : ℝ => Real.sinh x / Real.cosh x ^ 3) |u| := by
    congr 1 with u
    simp [φ, Real.abs_sinh]
  rw [hcongr, integral_comp_abs (f := fun x : ℝ => Real.sinh x / Real.cosh x ^ 3),
    integral_Ioi_sech_deriv]
  norm_num

theorem hcIntegralSinhCosh3 (a : ℝ) :
    MeasureTheory.Integrable
        (fun y : ℝ => |Real.sinh (Real.pi * (y - a))| / Real.cosh (Real.pi * (y - a)) ^ 3) ∧
      ∫ y : ℝ, |Real.sinh (Real.pi * (y - a))| / Real.cosh (Real.pi * (y - a)) ^ 3
        = 1 / Real.pi := by
  have hk_int : Integrable (fun z : ℝ => φ (Real.pi * z)) :=
    integrable_φ.comp_mul_left' (R := Real.pi) Real.pi_ne_zero
  have hk_val : ∫ z : ℝ, φ (Real.pi * z) = 1 / Real.pi := by
    rw [MeasureTheory.Measure.integral_comp_mul_left φ Real.pi, integral_φ]
    simp [abs_of_pos (inv_pos.mpr Real.pi_pos)]
  set k : ℝ → ℝ := fun z => φ (Real.pi * z) with hk
  have hme : MeasurableEmbedding (fun y : ℝ => y + (-a)) :=
    (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding
  have hmap : Measure.map (fun y : ℝ => y + (-a)) volume = volume :=
    MeasureTheory.map_add_right_eq_self volume (-a)
  have hint : Integrable (fun y : ℝ => k (y + (-a))) := by
    have h1 : Integrable k (Measure.map (fun y : ℝ => y + (-a)) volume) := by
      rw [hmap]; exact hk_int
    have h2 : Integrable (k ∘ fun y : ℝ => y + (-a)) volume :=
      (hme.integrable_map_iff (g := k)).mp h1
    simpa only [Function.comp_def] using h2
  have hval : ∫ y, k (y + (-a)) = 1 / Real.pi := by
    have hmp : MeasurePreserving (fun y : ℝ => y + (-a)) volume volume :=
      MeasureTheory.measurePreserving_add_right volume (-a)
    have := MeasureTheory.MeasurePreserving.integral_comp hmp hme k
    rw [this, hk_val]
  refine ⟨?_, ?_⟩
  · simpa [k, φ, sub_eq_add_neg] using hint
  · simpa [k, φ, sub_eq_add_neg] using hval

end Work.FatouL1
