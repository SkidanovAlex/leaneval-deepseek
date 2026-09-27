import Mathlib

namespace Work.Mostow

open MeasureTheory
open scoped ENNReal

/-- For `x ≥ 0`, `cosh x ≤ exp x`. -/
private lemma tube_cosh_le_exp {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith [Real.exp_pos x]

/-- For every `x`, `sinh x ≤ exp x`. -/
private lemma tube_sinh_le_exp (x : ℝ) : Real.sinh x ≤ Real.exp x := by
  rw [Real.sinh_eq]
  have h : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  linarith [Real.exp_pos x]

/-- Pointwise upper bound: for `x ≥ 0`, `cosh(x)^k * sinh(x)^{m-1} ≤ e^{(k+m-1)x}`. -/
lemma tubePointwiseUpper (k m : ℕ) (hm : 1 ≤ m) :
    ∀ x : ℝ, 0 ≤ x →
      Real.cosh x ^ k * Real.sinh x ^ (m - 1) ≤
        Real.exp (((k + m : ℕ) - 1 : ℝ) * x) := by
  intro x hx
  have hcosh : Real.cosh x ≤ Real.exp x := tube_cosh_le_exp hx
  have hsinh : Real.sinh x ≤ Real.exp x := tube_sinh_le_exp x
  have hcosh0 : 0 ≤ Real.cosh x := (Real.cosh_pos x).le
  have hsinh0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
  have hexp0 : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have h1 : Real.cosh x ^ k ≤ Real.exp x ^ k := pow_le_pow_left₀ hcosh0 hcosh k
  have h2 : Real.sinh x ^ (m - 1) ≤ Real.exp x ^ (m - 1) :=
    pow_le_pow_left₀ hsinh0 hsinh (m - 1)
  have hcast : ((k + (m - 1) : ℕ) : ℝ) = ((k + m : ℕ) - 1 : ℝ) := by
    have h1 : k + (m - 1) = (k + m) - 1 := by omega
    rw [h1]
    simpa using (Nat.cast_sub (R := ℝ) (m := 1) (n := k + m) (by omega))
  calc Real.cosh x ^ k * Real.sinh x ^ (m - 1)
      ≤ Real.exp x ^ k * Real.exp x ^ (m - 1) :=
        mul_le_mul h1 h2 (pow_nonneg hsinh0 _) (pow_nonneg hexp0 _)
    _ = Real.exp x ^ (k + (m - 1)) := (pow_add _ _ _).symm
    _ = Real.exp (((k + (m - 1) : ℕ) : ℝ) * x) :=
        (Real.exp_nat_mul x (k + (m - 1))).symm
    _ = Real.exp (((k + m : ℕ) - 1 : ℝ) * x) := by rw [hcast]

/-- Pointwise lower bound: for `x ≥ 1/2`,
`(1/2)^k * ((1-e^{-1})/2)^{m-1} * e^{(k+m-1)x} ≤ cosh(x)^k * sinh(x)^{m-1}`. -/
lemma tubePointwiseLower (k m : ℕ) (hm : 1 ≤ m) :
    ∀ x : ℝ, 1/2 ≤ x →
      (1/2 : ℝ) ^ k * ((1 - Real.exp (-1)) / 2) ^ (m - 1) *
          Real.exp (((k + m : ℕ) - 1 : ℝ) * x)
        ≤ Real.cosh x ^ k * Real.sinh x ^ (m - 1) := by
  intro x hx
  have hcosh : Real.exp x / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]; have := Real.exp_pos (-x); linarith
  have hsinh : ((1 - Real.exp (-1)) / 2) * Real.exp x ≤ Real.sinh x := by
    have hexp : Real.exp (-x) ≤ Real.exp (-1) * Real.exp x := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    rw [Real.sinh_eq]; nlinarith [hexp]
  have hpos1 : (0 : ℝ) ≤ Real.exp x / 2 := by positivity
  have hpos2 : (0 : ℝ) ≤ ((1 - Real.exp (-1)) / 2) * Real.exp x := by
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    positivity
  have hA : (Real.exp x / 2) ^ k ≤ Real.cosh x ^ k := pow_le_pow_left₀ hpos1 hcosh k
  have hB : (((1 - Real.exp (-1)) / 2) * Real.exp x) ^ (m - 1) ≤ Real.sinh x ^ (m - 1) :=
    pow_le_pow_left₀ hpos2 hsinh (m - 1)
  have hcast : (((k + m : ℕ) - 1 : ℝ)) = ((k + (m - 1) : ℕ) : ℝ) := by
    have h1 : k + (m - 1) = (k + m) - 1 := by omega
    rw [h1]
    simpa using (Nat.cast_sub (R := ℝ) (m := 1) (n := k + m) (by omega)).symm
  have h1 : (Real.exp x / 2) ^ k = (1/2 : ℝ) ^ k * Real.exp x ^ k := by
    rw [div_pow, div_eq_mul_inv,
      show ((2 : ℝ) ^ k)⁻¹ = (1/2 : ℝ) ^ k from by rw [← inv_pow]; norm_num]
    ring
  have h2 : (((1 - Real.exp (-1)) / 2) * Real.exp x) ^ (m - 1)
      = ((1 - Real.exp (-1)) / 2) ^ (m - 1) * Real.exp x ^ (m - 1) := by rw [mul_pow]
  have key : (Real.exp x / 2) ^ k * (((1 - Real.exp (-1)) / 2) * Real.exp x) ^ (m - 1)
      = (1/2 : ℝ) ^ k * ((1 - Real.exp (-1)) / 2) ^ (m - 1) *
          Real.exp (((k + m : ℕ) - 1 : ℝ) * x) := by
    rw [h1, h2, hcast, Real.exp_nat_mul, pow_add]; ring
  rw [← key]
  exact mul_le_mul hA hB (pow_nonneg hpos2 _) (pow_nonneg (Real.cosh_pos x).le _)

/-- `∫_{Ioo c d} e^{a x} dx = (e^{ad} - e^{ac})/a` for `a ≠ 0` and `c ≤ d`. -/
lemma tubeSetIntegralExpMul (a c d : ℝ) (ha : a ≠ 0) (hcd : c ≤ d) :
    ∫ x in Set.Ioo c d, Real.exp (a * x) = (Real.exp (a * d) - Real.exp (a * c)) / a := by
  have hsub : ∫ x in c..d, Real.exp (a * x) * a = Real.exp (a * d) - Real.exp (a * c) := by
    have hcomp := intervalIntegral.integral_comp_mul_deriv (a := c) (b := d)
      (f := fun x : ℝ => a * x) (f' := fun _ : ℝ => a) (g := Real.exp)
      (fun x _ => by simpa using (hasDerivAt_id x).const_mul a) continuousOn_const
      Real.continuous_exp
    simp only [Function.comp_apply] at hcomp
    rw [hcomp, integral_exp]
  have hmul : ∫ x in c..d, Real.exp (a * x) * a = (∫ x in c..d, Real.exp (a * x)) * a :=
    intervalIntegral.integral_mul_const a _
  rw [hmul] at hsub
  have hI : ∫ x in c..d, Real.exp (a * x) = (Real.exp (a * d) - Real.exp (a * c)) / a := by
    field_simp at hsub ⊢
    linarith [hsub]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcd]
  exact hI

/-- Two-sided exponential bounds for `I(ρ) = ∫_{0}^{ρ} cosh(x)^k sinh(x)^{m-1} dx`, with
`n = k + m ≥ 2`. Upper: `cosh^k sinh^{m-1} ≤ e^{(n-1)x}` and `∫_0^ρ e^{(n-1)x} dx ≤ e^{(n-1)ρ}/(n-1)`.
Lower: on `[ρ/2, ρ]` (with `ρ ≥ 1`) one has `cosh x ≥ e^x/2` and `sinh x ≥ ((1-e^{-1})/2) e^x`, so
`cosh^k sinh^{m-1} ≥ c e^{(n-1)x}` with `c = (1/2)^k ((1-e^{-1})/2)^{m-1}`, and the integral over
`[ρ/2, ρ]` is `≥ c (1 - e^{-1/2}) e^{(n-1)ρ}/(n-1)`. -/
theorem tubeIntegralBounds (k m : ℕ) (hm : 1 ≤ m) (hkm : 2 ≤ k + m) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ENNReal.ofReal (c₁ * Real.exp (((k + m : ℕ) - 1 : ℝ) * ρ)) ≤
        ∫⁻ x in Set.Ioo (0 : ℝ) ρ,
          ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume ∧
      (∫⁻ x in Set.Ioo (0 : ℝ) ρ,
          ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume) ≤
        ENNReal.ofReal (c₂ * Real.exp (((k + m : ℕ) - 1 : ℝ) * ρ)) := by
  set a : ℝ := ((k + m : ℕ) - 1 : ℝ) with ha_def
  have ha1 : 1 ≤ a := by
    rw [ha_def]
    have h2 : (2 : ℝ) ≤ ((k + m : ℕ) : ℝ) := by exact_mod_cast hkm
    linarith
  have ha0 : 0 < a := by linarith
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have hbase_pos : 0 < (1 - Real.exp (-1)) / 2 := by
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    linarith
  set c : ℝ := (1/2 : ℝ) ^ k * ((1 - Real.exp (-1)) / 2) ^ (m - 1) with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact mul_pos (pow_pos (by norm_num) k) (pow_pos hbase_pos (m - 1))
  have hhalf_pos : 0 < 1 - Real.exp (-(1/2)) := by
    have : Real.exp (-(1/2)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    linarith
  refine ⟨c * (1 - Real.exp (-(1/2))) / a, 1 / a, ?_, ?_, ?_⟩
  · exact div_pos (mul_pos hc_pos hhalf_pos) ha0
  · exact div_pos one_pos ha0
  · intro ρ hρ
    have hρ0 : 0 ≤ ρ := by linarith
    have hρpos : 0 < ρ := by linarith
    have hcont_f : Continuous fun x : ℝ => Real.cosh x ^ k * Real.sinh x ^ (m - 1) := by
      fun_prop
    have hcont_exp : Continuous fun x : ℝ => Real.exp (a * x) := by fun_prop
    have hcont_g : Continuous fun x : ℝ => c * Real.exp (a * x) := by fun_prop
    have hIoo_sub_Icc : Set.Ioo (0 : ℝ) ρ ⊆ Set.Icc 0 ρ :=
      fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hInt_f : IntegrableOn (fun x : ℝ => Real.cosh x ^ k * Real.sinh x ^ (m - 1))
        (Set.Ioo (0 : ℝ) ρ) volume :=
      (hcont_f.integrableOn_Icc (a := 0) (b := ρ)).mono_set hIoo_sub_Icc
    have hnn_f : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) ρ)]
        (fun x : ℝ => Real.cosh x ^ k * Real.sinh x ^ (m - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (pow_nonneg (Real.cosh_pos x).le k)
        (pow_nonneg (Real.sinh_nonneg_iff.mpr (le_of_lt hx.1)) (m - 1))
    have hLin_eq : (∫⁻ x in Set.Ioo (0 : ℝ) ρ,
          ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume)
        = ENNReal.ofReal (∫ x in Set.Ioo (0 : ℝ) ρ,
            Real.cosh x ^ k * Real.sinh x ^ (m - 1) ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hInt_f hnn_f).symm
    -- upper bound
    have hInt_exp : IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ioo (0 : ℝ) ρ) volume :=
      (hcont_exp.integrableOn_Icc (a := 0) (b := ρ)).mono_set hIoo_sub_Icc
    have hmono : (∫ x in Set.Ioo (0 : ℝ) ρ,
          Real.cosh x ^ k * Real.sinh x ^ (m - 1) ∂volume)
        ≤ ∫ x in Set.Ioo (0 : ℝ) ρ, Real.exp (a * x) ∂volume :=
      setIntegral_mono_on hInt_f hInt_exp measurableSet_Ioo
        (fun x hx => tubePointwiseUpper k m hm x (le_of_lt hx.1))
    have hexpval : (∫ x in Set.Ioo (0 : ℝ) ρ, Real.exp (a * x) ∂volume)
        = (Real.exp (a * ρ) - 1) / a := by
      rw [tubeSetIntegralExpMul a 0 ρ ha_ne hρ0, mul_zero, Real.exp_zero]
    have hupper : (∫ x in Set.Ioo (0 : ℝ) ρ,
          Real.cosh x ^ k * Real.sinh x ^ (m - 1) ∂volume) ≤ (1 / a) * Real.exp (a * ρ) := by
      calc _ ≤ ∫ x in Set.Ioo (0 : ℝ) ρ, Real.exp (a * x) ∂volume := hmono
        _ = (Real.exp (a * ρ) - 1) / a := hexpval
        _ ≤ (1 / a) * Real.exp (a * ρ) := by
            have hE : (1 / a) * Real.exp (a * ρ) = Real.exp (a * ρ) / a := by ring
            rw [hE]
            exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (a * ρ)]) ha0.le
    have hUpper : (∫⁻ x in Set.Ioo (0 : ℝ) ρ,
          ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume)
        ≤ ENNReal.ofReal ((1 / a) * Real.exp (a * ρ)) := by
      rw [hLin_eq]; exact ENNReal.ofReal_le_ofReal hupper
    -- lower bound
    have hJsub : Set.Ioo (ρ / 2) ρ ⊆ Set.Ioo (0 : ℝ) ρ :=
      fun x hx => ⟨by linarith [hx.1, hρpos], hx.2⟩
    have hInt_g : IntegrableOn (fun x : ℝ => c * Real.exp (a * x)) (Set.Ioo (ρ / 2) ρ) volume :=
      (hcont_g.integrableOn_Icc (a := ρ / 2) (b := ρ)).mono_set
        (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hnn_g : 0 ≤ᵐ[volume.restrict (Set.Ioo (ρ / 2) ρ)]
        (fun x : ℝ => c * Real.exp (a * x)) :=
      Filter.Eventually.of_forall (fun x => mul_nonneg hc_pos.le (Real.exp_pos _).le)
    have hLin_g : (∫⁻ x in Set.Ioo (ρ / 2) ρ, ENNReal.ofReal (c * Real.exp (a * x)) ∂volume)
        = ENNReal.ofReal (∫ x in Set.Ioo (ρ / 2) ρ, c * Real.exp (a * x) ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hInt_g hnn_g).symm
    have hJval : (∫ x in Set.Ioo (ρ / 2) ρ, c * Real.exp (a * x) ∂volume)
        = c * ((Real.exp (a * ρ) - Real.exp (a * (ρ / 2))) / a) := by
      rw [MeasureTheory.integral_const_mul,
        tubeSetIntegralExpMul a (ρ / 2) ρ ha_ne (by linarith)]
    have hpointwise : ∀ x ∈ Set.Ioo (ρ / 2) ρ,
        ENNReal.ofReal (c * Real.exp (a * x))
          ≤ ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) :=
      fun x hx => ENNReal.ofReal_le_ofReal
        (tubePointwiseLower k m hm x (by linarith [hx.1]))
    have hmeas_g_ofReal : Measurable
        (fun x : ℝ => ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1))) :=
      hcont_f.measurable.ennreal_ofReal
    have hstep1 : (∫⁻ x in Set.Ioo (ρ / 2) ρ, ENNReal.ofReal (c * Real.exp (a * x)) ∂volume)
        ≤ ∫⁻ x in Set.Ioo (ρ / 2) ρ,
            ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume :=
      setLIntegral_mono hmeas_g_ofReal hpointwise
    have hstep2 : (∫⁻ x in Set.Ioo (ρ / 2) ρ,
          ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume)
        ≤ ∫⁻ x in Set.Ioo (0 : ℝ) ρ,
            ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume :=
      lintegral_mono_set hJsub
    have harho : 1 ≤ a * ρ := by nlinarith [ha1, hρ]
    have hexp_le : Real.exp (a * (ρ / 2)) ≤ Real.exp (-(1/2)) * Real.exp (a * ρ) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [harho]
    have hreal : (c * (1 - Real.exp (-(1/2))) / a) * Real.exp (a * ρ)
        ≤ c * ((Real.exp (a * ρ) - Real.exp (a * (ρ / 2))) / a) := by
      have hca : 0 ≤ c / a := div_nonneg hc_pos.le ha0.le
      have key : (1 - Real.exp (-(1/2))) * Real.exp (a * ρ)
          ≤ Real.exp (a * ρ) - Real.exp (a * (ρ / 2)) := by nlinarith [hexp_le]
      calc (c * (1 - Real.exp (-(1/2))) / a) * Real.exp (a * ρ)
          = (c / a) * ((1 - Real.exp (-(1/2))) * Real.exp (a * ρ)) := by ring
        _ ≤ (c / a) * (Real.exp (a * ρ) - Real.exp (a * (ρ / 2))) :=
            mul_le_mul_of_nonneg_left key hca
        _ = c * ((Real.exp (a * ρ) - Real.exp (a * (ρ / 2))) / a) := by ring
    constructor
    · calc ENNReal.ofReal ((c * (1 - Real.exp (-(1/2))) / a) * Real.exp (a * ρ))
          ≤ ENNReal.ofReal (c * ((Real.exp (a * ρ) - Real.exp (a * (ρ / 2))) / a)) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (∫ x in Set.Ioo (ρ / 2) ρ, c * Real.exp (a * x) ∂volume) := by
            rw [hJval]
        _ = ∫⁻ x in Set.Ioo (ρ / 2) ρ, ENNReal.ofReal (c * Real.exp (a * x)) ∂volume :=
            hLin_g.symm
        _ ≤ ∫⁻ x in Set.Ioo (ρ / 2) ρ,
              ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume := hstep1
        _ ≤ ∫⁻ x in Set.Ioo (0 : ℝ) ρ,
              ENNReal.ofReal (Real.cosh x ^ k * Real.sinh x ^ (m - 1)) ∂volume := hstep2
    · exact hUpper

end Work.Mostow
