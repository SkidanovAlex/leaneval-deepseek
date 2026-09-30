import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mertens

open MeasureTheory

/-- Pointwise algebraic identity relating the two forms of the integrand which appear
in the telescoping identity. -/
lemma inv_rpow_mul_log_eq (x ε : ℝ) (hx : 1 < x) (hε : 0 < ε) :
    1 / (x ^ (1 + ε) * Real.log x)
      = (Real.exp (-(ε * Real.log x)) / (ε * Real.log x)) * (ε / x) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
  rw [show -(ε * Real.log x) = -(Real.log x * ε) by ring, Real.exp_neg]
  field_simp

/-- The derivative of `t ↦ -log (log t) / t^ε` for `t > 1`. -/
lemma hasDerivAt_loglog_div_rpow (x ε : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t => -Real.log (Real.log t) / t^ε)
      (ε * (Real.log (Real.log x) / x^(1+ε)) - 1/(x^(1+ε) * Real.log x)) x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hL : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx0)
  have h2 : HasDerivAt (fun t => Real.log (Real.log t)) (x⁻¹ / Real.log x) x := h1.log hL
  have h3 : HasDerivAt (fun t => t^ε) (ε * x^(ε-1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx0))
  have hk : HasDerivAt (fun t => -Real.log (Real.log t)) (-(x⁻¹ / Real.log x)) x := h2.neg
  have h4 : HasDerivAt (fun t => -Real.log (Real.log t) / t^ε)
      (((-(x⁻¹ / Real.log x)) * x^ε - (-Real.log (Real.log x)) * (ε * x^(ε-1)))/(x^ε)^2) x :=
    hk.div h3 (ne_of_gt (Real.rpow_pos_of_pos hx0 ε))
  refine h4.congr_deriv ?_
  rw [Real.rpow_sub hx0 ε 1, Real.rpow_one, Real.rpow_add hx0 1 ε, Real.rpow_one]
  field_simp
  ring

/-- Integration-by-parts (telescoping) half of `loglog_rpow_telescope`:
the `ε`-weighted integral of `log (log t) / t^(1+ε)` equals the boundary terms plus the
integral of `1 / (t^(1+ε) * log t)`. -/
lemma ibp_loglog_div_rpow (a b ε : ℝ) (ha : 1 < a) (hab : a ≤ b) (hε : 0 < ε) :
    ε * ∫ t in a..b, Real.log (Real.log t) / t ^ (1 + ε) =
      Real.log (Real.log a) / a ^ ε - Real.log (Real.log b) / b ^ ε +
        ∫ t in a..b, 1 / (t ^ (1 + ε) * Real.log t) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hle : ∀ t ∈ Set.Icc a b, 1 < t := fun t ht => lt_of_lt_of_le ha ht.1
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => lt_of_lt_of_le ha0 ht.1
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (hpos t ht))
  have hcc : ContinuousOn (fun t => Real.log (Real.log t)) (Set.Icc a b) :=
    hlog.log (fun t ht => ne_of_gt (Real.log_pos (hle t ht)))
  have hrpow : ContinuousOn (fun t => t^(1+ε)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (hpos t ht)))
  have hrpowε : ContinuousOn (fun t => t^ε) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (hpos t ht)))
  have hA : ContinuousOn (fun t => Real.log (Real.log t)/t^(1+ε)) (Set.Icc a b) :=
    hcc.div hrpow (fun t ht => ne_of_gt (Real.rpow_pos_of_pos (hpos t ht) _))
  have hB : ContinuousOn (fun t => 1/(t^(1+ε)*Real.log t)) (Set.Icc a b) :=
    continuousOn_const.div (hrpow.mul hlog)
      (fun t ht => ne_of_gt (mul_pos (Real.rpow_pos_of_pos (hpos t ht) _)
        (Real.log_pos (hle t ht))))
  have hF : ContinuousOn (fun t => -Real.log (Real.log t)/t^ε) (Set.Icc a b) :=
    (hcc.neg).div hrpowε (fun t ht => ne_of_gt (Real.rpow_pos_of_pos (hpos t ht) ε))
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun t => -Real.log (Real.log t)/t^ε)
        (ε * (Real.log (Real.log x)/x^(1+ε)) - 1/(x^(1+ε)*Real.log x)) x :=
    fun x hx => hasDerivAt_loglog_div_rpow x ε (lt_trans ha hx.1)
  have hintA : ContinuousOn (fun t => ε * (Real.log (Real.log t)/t^(1+ε))) (Set.Icc a b) :=
    continuousOn_const.mul hA
  have hint : IntervalIntegrable
      (fun t => ε * (Real.log (Real.log t)/t^(1+ε)) - 1/(t^(1+ε)*Real.log t)) volume a b :=
    (hintA.sub hB).intervalIntegrable_of_Icc hab
  have hintA' : IntervalIntegrable (fun t => ε * (Real.log (Real.log t)/t^(1+ε))) volume a b :=
    hintA.intervalIntegrable_of_Icc hab
  have hintB' : IntervalIntegrable (fun t => 1/(t^(1+ε)*Real.log t)) volume a b :=
    hB.intervalIntegrable_of_Icc hab
  have hFTC : (∫ t in a..b, (ε * (Real.log (Real.log t)/t^(1+ε)) - 1/(t^(1+ε)*Real.log t)))
      = -Real.log (Real.log b)/b^ε - -Real.log (Real.log a)/a^ε := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hderiv hint
    simpa using this
  have hsplit : (∫ t in a..b, (ε * (Real.log (Real.log t)/t^(1+ε)) - 1/(t^(1+ε)*Real.log t)))
      = ε * (∫ t in a..b, Real.log (Real.log t)/t^(1+ε))
        - ∫ t in a..b, 1/(t^(1+ε)*Real.log t) := by
    rw [intervalIntegral.integral_sub hintA' hintB', intervalIntegral.integral_const_mul]
  have h2 : ε * (∫ t in a..b, Real.log (Real.log t)/t^(1+ε))
        - ∫ t in a..b, 1/(t^(1+ε)*Real.log t)
      = Real.log (Real.log a)/a^ε - Real.log (Real.log b)/b^ε := by
    rw [← hsplit]
    exact hFTC.trans (by ring)
  linarith [h2]

/-- Substitution half of `loglog_rpow_telescope`: with `v = ε log t`, the integral
`1 / (t^(1+ε) log t)` becomes `exp(-v)/v`. -/
lemma integral_inv_rpow_log (a b ε : ℝ) (ha : 1 < a) (hab : a ≤ b) (hε : 0 < ε) :
    (∫ t in a..b, 1 / (t ^ (1 + ε) * Real.log t))
      = ∫ v in (ε * Real.log a)..(ε * Real.log b), Real.exp (-v) / v := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have h1 : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t => ε * Real.log t) (ε/x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx'.1
    have h : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx0)
    have := h.const_mul ε
    simpa [div_eq_mul_inv] using this
  have h2 : ContinuousOn (fun x => ε/x) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id
      (fun x hx => ne_of_gt (lt_of_lt_of_le ha0 hx.1))
  have hcontg : ContinuousOn (fun v => Real.exp (-v)/v) (Set.Ioi 0) :=
    (Real.continuous_exp.comp_continuousOn continuousOn_id.neg).div continuousOn_id
      (fun v hv => ne_of_gt hv)
  have h3 : ContinuousOn (fun v => Real.exp (-v)/v) ((fun t => ε * Real.log t) '' Set.uIcc a b) := by
    refine hcontg.mono ?_
    rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    have hla : 0 < Real.log a := Real.log_pos ha
    have hlx : Real.log a ≤ Real.log x := Real.log_le_log ha0 hx'.1
    exact mul_pos hε (lt_of_lt_of_le hla hlx)
  have hconv := intervalIntegral.integral_comp_mul_deriv'
      (a := a) (b := b)
      (f := fun t => ε * Real.log t) (f' := fun t => ε / t)
      (g := fun v => Real.exp (-v)/v) h1 h2 h3
  have hcongr : (∫ t in a..b, 1 / (t ^ (1 + ε) * Real.log t))
      = ∫ t in a..b, ((fun v => Real.exp (-v)/v) ∘ (fun t => ε*Real.log t)) t * (ε/t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht'.1
    simp only [Function.comp_apply]
    exact inv_rpow_mul_log_eq t ε ht1 hε
  rw [hcongr]
  simpa using hconv

theorem loglog_rpow_telescope (a b ε : ℝ) (ha : 1 < a) (hab : a ≤ b) (hε : 0 < ε) :
    ε * ∫ t in a..b, Real.log (Real.log t) / t ^ (1 + ε) =
      Real.log (Real.log a) / a ^ ε - Real.log (Real.log b) / b ^ ε +
        ∫ v in (ε * Real.log a)..(ε * Real.log b), Real.exp (-v) / v := by
  rw [ibp_loglog_div_rpow a b ε ha hab hε, integral_inv_rpow_log a b ε ha hab hε]

end Work.BMF.mertens
