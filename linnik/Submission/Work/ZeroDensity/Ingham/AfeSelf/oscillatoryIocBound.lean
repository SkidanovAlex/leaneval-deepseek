import Mathlib

open MeasureTheory

set_option maxHeartbeats 1200000

namespace Work.ZeroDensity.Ingham.AfeSelf

/-- The oscillating exponential `e^{i φ(x)}`. -/
noncomputable def ocE (φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((φ x : ℝ) : ℂ))

/-- The weight `w` divided by `i · ψ`. -/
noncomputable def ocU (w ψ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ((w x : ℝ) : ℂ) / (Complex.I * ((ψ x : ℝ) : ℂ))

/-- The derivative of `ocU w ψ`. -/
noncomputable def ocU' (w w' ψ χ : ℝ → ℝ) (x : ℝ) : ℂ :=
  (((w' x : ℝ) : ℂ) * (Complex.I * ((ψ x : ℝ) : ℂ)) -
      ((w x : ℝ) : ℂ) * (Complex.I * ((χ x : ℝ) : ℂ))) /
    (Complex.I * ((ψ x : ℝ) : ℂ)) ^ 2

/-- `χ / ψ²` is the total variation of `1/ψ`, bounded by `1/μ`. -/
theorem chiDivPsiSqIntegralLe {ψ χ : ℝ → ℝ} {a b μ : ℝ}
    (hab : a ≤ b) (hμ : 0 < μ)
    (hψ : ∀ x ∈ Set.Icc a b, HasDerivAt ψ (χ x) x)
    (hχc : ContinuousOn χ (Set.Icc a b))
    (hψμ : ∀ x ∈ Set.Icc a b, μ ≤ |ψ x|) :
    ∫ x in a..b, χ x / (ψ x) ^ 2 ≤ 1 / μ := by
  have hne : ∀ x ∈ Set.Icc a b, ψ x ≠ 0 :=
    fun x hx => abs_pos.mp (lt_of_lt_of_le hμ (hψμ x hx))
  have hψcont : ContinuousOn ψ (Set.Icc a b) :=
    fun x hx => (hψ x hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun x => -(χ x) / (ψ x) ^ 2) (Set.Icc a b) := by
    have h2 : ContinuousOn (fun x => (ψ x) ^ 2) (Set.Icc a b) := hψcont.pow 2
    exact (hχc.neg).div h2 (fun x hx => pow_ne_zero 2 (hne x hx))
  have hint : IntervalIntegrable (fun x => -(χ x) / (ψ x) ^ 2) volume a b := by
    refine (show ContinuousOn (fun x => -(χ x) / (ψ x) ^ 2) (Set.uIcc a b) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]; exact hcont
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => (ψ y)⁻¹) (-(χ x) / (ψ x) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hψ x hx).inv (hne x hx)
  have hval : ∫ x in a..b, -(χ x) / (ψ x) ^ 2 = (ψ b)⁻¹ - (ψ a)⁻¹ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hval2 : ∫ x in a..b, χ x / (ψ x) ^ 2 = (ψ a)⁻¹ - (ψ b)⁻¹ := by
    have hc : ∫ x in a..b, χ x / (ψ x) ^ 2 = ∫ x in a..b, -(-(χ x) / (ψ x) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx; ring
    rw [hc, intervalIntegral.integral_neg, hval]; ring
  rw [hval2]
  have hsign : (∀ x ∈ Set.Icc a b, 0 < ψ x) ∨ (∀ x ∈ Set.Icc a b, ψ x < 0) := by
    have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    rcases lt_trichotomy (ψ a) 0 with hlt | heq | hgt
    · right
      intro x hx
      rcases lt_trichotomy (ψ x) 0 with hxlt | hxeq | hxgt
      · exact hxlt
      · exact absurd hxeq (hne x hx)
      · exfalso
        have hax : a ≤ x := hx.1
        have hcont_ax : ContinuousOn ψ (Set.Icc a x) :=
          hψcont.mono (Set.Icc_subset_Icc_right hx.2)
        have hmem : (0 : ℝ) ∈ Set.Icc (ψ a) (ψ x) := ⟨le_of_lt hlt, le_of_lt hxgt⟩
        obtain ⟨y, hy, hyeq⟩ := intermediate_value_Icc hax hcont_ax hmem
        exact hne y ⟨hy.1, le_trans hy.2 hx.2⟩ hyeq
    · exact absurd heq (hne a ha_mem)
    · left
      intro x hx
      rcases lt_trichotomy (ψ x) 0 with hxlt | hxeq | hxgt
      · exfalso
        have hax : a ≤ x := hx.1
        have hcont_ax : ContinuousOn ψ (Set.Icc a x) :=
          hψcont.mono (Set.Icc_subset_Icc_right hx.2)
        have hmem : (0 : ℝ) ∈ Set.Icc (ψ x) (ψ a) := ⟨le_of_lt hxlt, le_of_lt hgt⟩
        obtain ⟨y, hy, hyeq⟩ := intermediate_value_Icc' hax hcont_ax hmem
        exact hne y ⟨hy.1, le_trans hy.2 hx.2⟩ hyeq
      · exact absurd hxeq (hne x hx)
      · exact hxgt
  rcases hsign with hpos | hneg
  · have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
    have h1 : (ψ a)⁻¹ ≤ 1 / μ := by
      have hμa : μ ≤ ψ a := by
        have := hψμ a ha
        rwa [abs_of_pos (hpos a ha)] at this
      simpa [one_div] using one_div_le_one_div_of_le hμ hμa
    have h2 : 0 ≤ (ψ b)⁻¹ := by
      have : 0 < ψ b := hpos b hb
      exact inv_nonneg.mpr (le_of_lt this)
    calc (ψ a)⁻¹ - (ψ b)⁻¹ ≤ (ψ a)⁻¹ := sub_le_self _ h2
      _ ≤ 1 / μ := h1
  · have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
    have h1 : (ψ a)⁻¹ ≤ 0 := le_of_lt ((inv_neg'' (a := ψ a)).mpr (hneg a ha))
    have h2 : -(ψ b)⁻¹ ≤ 1 / μ := by
      have hle : μ ≤ -(ψ b) := by
        have hbabs := hψμ b hb
        rw [abs_of_neg (hneg b hb)] at hbabs
        linarith
      have := one_div_le_one_div_of_le hμ hle
      simpa [one_div, inv_neg] using this
    have hkey : (ψ a)⁻¹ - (ψ b)⁻¹ = (ψ a)⁻¹ + (-(ψ b)⁻¹) := by ring
    rw [hkey]
    linarith

theorem oscillatoryIocBound {φ ψ χ w w' : ℝ → ℝ} {a b μ : ℝ} (hab : a ≤ b) (hμ : 0 < μ)
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivAt φ (ψ x) x)
    (hψ : ∀ x ∈ Set.Icc a b, HasDerivAt ψ (χ x) x) (hχc : ContinuousOn χ (Set.Icc a b))
    (hχ : ∀ x ∈ Set.Icc a b, 0 ≤ χ x)
    (hψμ : ∀ x ∈ Set.Icc a b, μ ≤ |ψ x|)
    (hw : ∀ x ∈ Set.Icc a b, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Set.Icc a b))
    (hw0 : ∀ x ∈ Set.Icc a b, 0 ≤ w x) (hw' : ∀ x ∈ Set.Icc a b, w' x ≤ 0) :
    ‖∫ x in a..b, ((w x : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ x : ℝ) : ℂ))‖ ≤ 4 * w a / μ := by
  change ‖∫ x in a..b, ((w x : ℝ) : ℂ) * ocE φ x‖ ≤ 4 * w a / μ
  have hne : ∀ x ∈ Set.Icc a b, ψ x ≠ 0 :=
    fun x hx => abs_pos.mp (lt_of_lt_of_le hμ (hψμ x hx))
  have hφcont : ContinuousOn φ (Set.Icc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hψcont : ContinuousOn ψ (Set.Icc a b) :=
    fun x hx => (hψ x hx).continuousAt.continuousWithinAt
  have hwcont : ContinuousOn w (Set.Icc a b) :=
    fun x hx => (hw x hx).continuousAt.continuousWithinAt
  -- derivative of the oscillating exponential
  have hE : ∀ x ∈ Set.Icc a b,
      HasDerivAt (ocE φ) (ocE φ x * (Complex.I * ((ψ x : ℝ) : ℂ))) x := by
    intro x hx
    have h1 : HasDerivAt (fun y => Complex.I * ((φ y : ℝ) : ℂ))
        (Complex.I * ((ψ x : ℝ) : ℂ)) x :=
      HasDerivAt.const_mul Complex.I ((hφ x hx).ofReal_comp)
    exact h1.cexp
  -- derivative of `u = w / (i ψ)`
  have hu : ∀ x ∈ Set.Icc a b, HasDerivAt (ocU w ψ) (ocU' w w' ψ χ x) x := by
    intro x hx
    have hnum : HasDerivAt (fun y => ((w y : ℝ) : ℂ)) ((w' x : ℝ) : ℂ) x :=
      (hw x hx).ofReal_comp
    have hden : HasDerivAt (fun y => Complex.I * ((ψ y : ℝ) : ℂ))
        (Complex.I * ((χ x : ℝ) : ℂ)) x :=
      HasDerivAt.const_mul Complex.I ((hψ x hx).ofReal_comp)
    have hd0 : Complex.I * ((ψ x : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hne x hx))
    exact hnum.div hden hd0
  -- continuity of the auxiliary functions
  have hBcont : ContinuousOn (fun x => Complex.I * ((ψ x : ℝ) : ℂ)) (Set.Icc a b) :=
    continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn' hψcont)
  have hEcont : ContinuousOn (ocE φ) (Set.Icc a b) := by
    have hinner : ContinuousOn (fun x => Complex.I * ((φ x : ℝ) : ℂ)) (Set.Icc a b) :=
      continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn' hφcont)
    exact Complex.continuous_exp.comp_continuousOn' hinner
  have hU'cont : ContinuousOn (ocU' w w' ψ χ) (Set.Icc a b) := by
    have hA : ContinuousOn (fun x => ((w x : ℝ) : ℂ)) (Set.Icc a b) :=
      Complex.continuous_ofReal.comp_continuousOn' hwcont
    have hC : ContinuousOn (fun x => ((w' x : ℝ) : ℂ)) (Set.Icc a b) :=
      Complex.continuous_ofReal.comp_continuousOn' hw'c
    have hD : ContinuousOn (fun x => Complex.I * ((χ x : ℝ) : ℂ)) (Set.Icc a b) :=
      continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn' hχc)
    have hnum : ContinuousOn (fun x => ((w' x : ℝ) : ℂ) * (Complex.I * ((ψ x : ℝ) : ℂ)) -
        ((w x : ℝ) : ℂ) * (Complex.I * ((χ x : ℝ) : ℂ))) (Set.Icc a b) :=
      (hC.mul hBcont).sub (hA.mul hD)
    have hden : ContinuousOn (fun x => (Complex.I * ((ψ x : ℝ) : ℂ)) ^ 2) (Set.Icc a b) :=
      hBcont.pow 2
    have hd0 : ∀ x ∈ Set.Icc a b, (Complex.I * ((ψ x : ℝ) : ℂ)) ^ 2 ≠ 0 :=
      fun x hx => pow_ne_zero 2 (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hne x hx)))
    exact hnum.div hden hd0
  -- norm of the oscillating exponential
  have hEnorm : ∀ x, ‖ocE φ x‖ = 1 := fun x => by
    rw [ocE, mul_comm Complex.I]
    exact Complex.norm_exp_ofReal_mul_I (φ x)
  -- interval integrability for integration by parts
  have hEvint : IntervalIntegrable (fun x => ocE φ x * (Complex.I * ((ψ x : ℝ) : ℂ))) volume a b := by
    refine (show ContinuousOn (fun x => ocE φ x * (Complex.I * ((ψ x : ℝ) : ℂ))) (Set.uIcc a b) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hEcont.mul hBcont
  have hU'int : IntervalIntegrable (ocU' w w' ψ χ) volume a b := by
    refine (show ContinuousOn (ocU' w w' ψ χ) (Set.uIcc a b) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]; exact hU'cont
  have hEicc : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (ocE φ) (ocE φ x * (Complex.I * ((ψ x : ℝ) : ℂ))) x := by
    intro x hx; rw [Set.uIcc_of_le hab] at hx; exact hE x hx
  have huicc : ∀ x ∈ Set.uIcc a b, HasDerivAt (ocU w ψ) (ocU' w w' ψ χ x) x := by
    intro x hx; rw [Set.uIcc_of_le hab] at hx; exact hu x hx
  -- integration by parts
  have hIBP : ∫ x in a..b, ocU w ψ x * (ocE φ x * (Complex.I * ((ψ x : ℝ) : ℂ)))
      = ocU w ψ b * ocE φ b - ocU w ψ a * ocE φ a -
        ∫ x in a..b, ocU' w w' ψ χ x * ocE φ x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul huicc hEicc hU'int hEvint
  have hcongr : ∫ x in a..b, ((w x : ℝ) : ℂ) * ocE φ x
      = ∫ x in a..b, ocU w ψ x * (ocE φ x * (Complex.I * ((ψ x : ℝ) : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hψc : ((ψ x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne x hx)
    have hd0 : Complex.I * ((ψ x : ℝ) : ℂ) ≠ 0 := mul_ne_zero hI hψc
    simp only [ocU]
    field_simp <;> ring
  have hmain : ∫ x in a..b, ((w x : ℝ) : ℂ) * ocE φ x
      = ocU w ψ b * ocE φ b - ocU w ψ a * ocE φ a -
        ∫ x in a..b, ocU' w w' ψ χ x * ocE φ x := by
    rw [hcongr, hIBP]
  -- monotonicity of `w`
  have hwanti : AntitoneOn w (Set.Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun x hx => (hw x hx).continuousAt.continuousWithinAt)
      (fun x hx => ((hw x (interior_subset hx)).differentiableAt).differentiableWithinAt) ?_
    intro x hx
    rw [(hw x (interior_subset hx)).deriv]
    exact hw' x (interior_subset hx)
  -- fundamental theorem of calculus for `w'`
  have hwFTC : ∫ x in a..b, w' x = w b - w a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
    · intro x hx; rw [Set.uIcc_of_le hab] at hx; exact hw x hx
    · refine (show ContinuousOn w' (Set.uIcc a b) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab]; exact hw'c
  -- integrals of the two summands
  have hint1 : IntervalIntegrable (fun x => -(w' x) / μ) volume a b := by
    refine (show ContinuousOn (fun x => -(w' x) / μ) (Set.uIcc a b) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]; exact (hw'c.neg).div_const μ
  have hint2 : IntervalIntegrable (fun x => w a * (χ x / (ψ x) ^ 2)) volume a b := by
    refine (show ContinuousOn (fun x => w a * (χ x / (ψ x) ^ 2)) (Set.uIcc a b) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]
    have hdiv : ContinuousOn (fun x => χ x / (ψ x) ^ 2) (Set.Icc a b) :=
      hχc.div (hψcont.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
    exact ((continuous_const : Continuous (fun _ : ℝ => w a)).continuousOn).mul hdiv
  have hnegw : ∫ x in a..b, -(w' x) / μ = (w a - w b) / μ := by
    have hc : ∫ x in a..b, -(w' x) / μ = ∫ x in a..b, (1 / μ) * (-(w' x)) := by
      apply intervalIntegral.integral_congr
      intro x hx; ring
    rw [hc, intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, hwFTC]
    ring
  have hchiInt : ∫ x in a..b, w a * (χ x / (ψ x) ^ 2)
      = w a * (∫ x in a..b, χ x / (ψ x) ^ 2) :=
    intervalIntegral.integral_const_mul (w a) _
  have hsplit : ∫ x in a..b, (-(w' x) / μ + w a * (χ x / (ψ x) ^ 2))
      = (w a - w b) / μ + w a * (∫ x in a..b, χ x / (ψ x) ^ 2) := by
    rw [intervalIntegral.integral_add hint1 hint2, hnegw, hchiInt]
  -- pointwise bound for `‖u'‖`
  have hpoint : ∀ x ∈ Set.Icc a b,
      ‖ocU' w w' ψ χ x‖ ≤ -(w' x) / μ + w a * (χ x / (ψ x) ^ 2) := by
    intro x hx
    have hwx : 0 ≤ w x := hw0 x hx
    have hwax : w x ≤ w a := hwanti (Set.left_mem_Icc.mpr hab) hx hx.1
    have hχx : 0 ≤ χ x := hχ x hx
    have hw'x : w' x ≤ 0 := hw' x hx
    have hψabs : μ ≤ |ψ x| := hψμ x hx
    have hψpos : 0 < |ψ x| := lt_of_lt_of_le hμ hψabs
    have hbnorm : ‖Complex.I * ((ψ x : ℝ) : ℂ)‖ = |ψ x| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hnum : ‖((w' x : ℝ) : ℂ) * (Complex.I * ((ψ x : ℝ) : ℂ)) -
        ((w x : ℝ) : ℂ) * (Complex.I * ((χ x : ℝ) : ℂ))‖
        ≤ (-w' x) * |ψ x| + w x * χ x := by
      calc ‖((w' x : ℝ) : ℂ) * (Complex.I * ((ψ x : ℝ) : ℂ)) -
            ((w x : ℝ) : ℂ) * (Complex.I * ((χ x : ℝ) : ℂ))‖
          ≤ ‖((w' x : ℝ) : ℂ) * (Complex.I * ((ψ x : ℝ) : ℂ))‖ +
            ‖((w x : ℝ) : ℂ) * (Complex.I * ((χ x : ℝ) : ℂ))‖ := norm_sub_le _ _
        _ = |w' x| * |ψ x| + |w x| * |χ x| := by
            simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = (-w' x) * |ψ x| + w x * χ x := by
            rw [abs_of_nonpos hw'x, abs_of_nonneg hwx, abs_of_nonneg hχx]
    rw [ocU']
    rw [norm_div, norm_pow, hbnorm]
    have hsq : (|ψ x| : ℝ) ^ 2 = (ψ x) ^ 2 := sq_abs (ψ x)
    calc ‖((w' x : ℝ) : ℂ) * (Complex.I * ((ψ x : ℝ) : ℂ)) -
            ((w x : ℝ) : ℂ) * (Complex.I * ((χ x : ℝ) : ℂ))‖ / |ψ x| ^ 2
        ≤ ((-w' x) * |ψ x| + w x * χ x) / |ψ x| ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = (-w' x) / |ψ x| + w x * χ x / |ψ x| ^ 2 := by
          field_simp [ne_of_gt hψpos] <;> ring
      _ ≤ (-w' x) / μ + w a * (χ x / (ψ x) ^ 2) := by
          rw [hsq]
          apply add_le_add
          · exact div_le_div_of_nonneg_left (by linarith [hw'x]) hμ hψabs
          · rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_right hwax (div_nonneg hχx (sq_nonneg (ψ x)))
  -- norm of `u`
  have hUnorm : ∀ x ∈ Set.Icc a b, ‖ocU w ψ x‖ = w x / |ψ x| := by
    intro x hx
    simp only [ocU, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (hw0 x hx)]
  have hUb : ‖ocU w ψ b‖ ≤ w b / μ := by
    rw [hUnorm b (Set.right_mem_Icc.mpr hab)]
    exact div_le_div_of_nonneg_left (hw0 b (Set.right_mem_Icc.mpr hab)) hμ
      (hψμ b (Set.right_mem_Icc.mpr hab))
  have hUa : ‖ocU w ψ a‖ ≤ w a / μ := by
    rw [hUnorm a (Set.left_mem_Icc.mpr hab)]
    exact div_le_div_of_nonneg_left (hw0 a (Set.left_mem_Icc.mpr hab)) hμ
      (hψμ a (Set.left_mem_Icc.mpr hab))
  -- boundary term
  have hB : ‖ocU w ψ b * ocE φ b - ocU w ψ a * ocE φ a‖ ≤ 2 * w a / μ := by
    calc ‖ocU w ψ b * ocE φ b - ocU w ψ a * ocE φ a‖
        ≤ ‖ocU w ψ b * ocE φ b‖ + ‖ocU w ψ a * ocE φ a‖ := norm_sub_le _ _
      _ = ‖ocU w ψ b‖ + ‖ocU w ψ a‖ := by
          rw [norm_mul, norm_mul, hEnorm b, hEnorm a, mul_one, mul_one]
      _ ≤ w b / μ + w a / μ := add_le_add hUb hUa
      _ ≤ w a / μ + w a / μ := by
          have : w b / μ ≤ w a / μ :=
            div_le_div_of_nonneg_right
              (hwanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab) (le_of_lt hμ)
          linarith
      _ = 2 * w a / μ := by ring
  -- remainder term
  have hR : ‖∫ x in a..b, ocU' w w' ψ χ x * ocE φ x‖ ≤ 2 * w a / μ := by
    have hnorm_eq : ∀ x, ‖ocU' w w' ψ χ x * ocE φ x‖ = ‖ocU' w w' ψ χ x‖ := by
      intro x; rw [norm_mul, hEnorm x, mul_one]
    have hAc : ContinuousOn (fun x => ‖ocU' w w' ψ χ x‖) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]; exact continuous_norm.comp_continuousOn hU'cont
    have hAc_int : IntervalIntegrable (fun x => ‖ocU' w w' ψ χ x‖) volume a b :=
      hAc.intervalIntegrable
    have hgc : ContinuousOn (fun x => -(w' x) / μ + w a * (χ x / (ψ x) ^ 2)) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      refine ((hw'c.neg).div_const μ).add ?_
      have hdiv : ContinuousOn (fun x => χ x / (ψ x) ^ 2) (Set.Icc a b) :=
        hχc.div (hψcont.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
      exact ((continuous_const : Continuous (fun _ : ℝ => w a)).continuousOn).mul hdiv
    have hgc_int : IntervalIntegrable (fun x => -(w' x) / μ + w a * (χ x / (ψ x) ^ 2))
        volume a b := hgc.intervalIntegrable
    calc ‖∫ x in a..b, ocU' w w' ψ χ x * ocE φ x‖
        ≤ ∫ x in a..b, ‖ocU' w w' ψ χ x * ocE φ x‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, ‖ocU' w w' ψ χ x‖ := by
          apply intervalIntegral.integral_congr
          intro x hx; exact hnorm_eq x
      _ ≤ ∫ x in a..b, (-(w' x) / μ + w a * (χ x / (ψ x) ^ 2)) :=
          intervalIntegral.integral_mono_on hab hAc_int hgc_int hpoint
      _ = (w a - w b) / μ + w a * (∫ x in a..b, χ x / (ψ x) ^ 2) := hsplit
      _ ≤ 2 * w a / μ := by
          have hchi := chiDivPsiSqIntegralLe hab hμ hψ hχc hψμ
          have hwa : 0 ≤ w a := hw0 a (Set.left_mem_Icc.mpr hab)
          have step1 : w a * (∫ x in a..b, χ x / (ψ x) ^ 2) ≤ w a * (1 / μ) :=
            mul_le_mul_of_nonneg_left hchi hwa
          calc (w a - w b) / μ + w a * (∫ x in a..b, χ x / (ψ x) ^ 2)
              ≤ (w a - w b) / μ + w a * (1 / μ) := add_le_add (le_refl _) step1
            _ = (2 * w a - w b) / μ := by ring
            _ ≤ 2 * w a / μ := by
                apply div_le_div_of_nonneg_right _ (le_of_lt hμ)
                have := hw0 b (Set.right_mem_Icc.mpr hab)
                linarith
  rw [hmain]
  calc ‖ocU w ψ b * ocE φ b - ocU w ψ a * ocE φ a -
          ∫ x in a..b, ocU' w w' ψ χ x * ocE φ x‖
      ≤ ‖ocU w ψ b * ocE φ b - ocU w ψ a * ocE φ a‖ +
        ‖∫ x in a..b, ocU' w w' ψ χ x * ocE φ x‖ := norm_sub_le _ _
    _ ≤ 2 * w a / μ + 2 * w a / μ := add_le_add hB hR
    _ = 4 * w a / μ := by ring

end Work.ZeroDensity.Ingham.AfeSelf
