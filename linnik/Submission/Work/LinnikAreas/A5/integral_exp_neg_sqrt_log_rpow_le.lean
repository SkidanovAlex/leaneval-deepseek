import Mathlib

namespace Work.LinnikAreas.A5

open MeasureTheory

/-- Derivative of the auxiliary function `t ↦ (1 + c√(log t)) · exp(-c√(log t))`
for `t > 1`. -/
private lemma hasDerivAt_psi (c : ℝ) (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t => (1 + c * Real.sqrt (Real.log t)) * Real.exp (-c * Real.sqrt (Real.log t)))
      (-(c^2 * x⁻¹ * Real.exp (-c * Real.sqrt (Real.log x)) / 2)) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hw : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlogx)
  set d := x⁻¹ / (2 * Real.sqrt (Real.log x)) with hddef
  have hv : HasDerivAt (fun t => Real.sqrt (Real.log t)) d x := by
    have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    simpa [d] using h1.sqrt hlogx.ne'
  have hp : HasDerivAt (fun t => c * Real.sqrt (Real.log t)) (c * d) x := hv.const_mul c
  have hA : HasDerivAt (fun t => 1 + c * Real.sqrt (Real.log t)) (c * d) x := hp.const_add 1
  have hq : HasDerivAt (fun t => -c * Real.sqrt (Real.log t)) (-c * d) x := hv.const_mul (-c)
  have hB : HasDerivAt (fun t => Real.exp (-c * Real.sqrt (Real.log t)))
      (Real.exp (-c * Real.sqrt (Real.log x)) * (-c * d)) x := hq.exp
  have hprod := hA.mul hB
  have hval : (c * d) * Real.exp (-c * Real.sqrt (Real.log x))
        + (1 + c * Real.sqrt (Real.log x)) * (Real.exp (-c * Real.sqrt (Real.log x)) * (-c * d))
      = -(c^2 * x⁻¹ * Real.exp (-c * Real.sqrt (Real.log x)) / 2) := by
    rw [hddef]
    field_simp
    ring
  rw [hval] at hprod
  exact hprod

theorem integral_exp_neg_sqrt_log_rpow_le (x₀ R lam c : ℝ) (hx₀ : 0 < x₀) (hc : 0 < c)
    (hlam : 0 < lam) (hlamR : lam ≤ R) {q : ℝ} (hq : 1 < q) :
    (∫ t in (1:ℝ)..q^x₀, Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q)))
      ≤ 2 * Real.exp (R * x₀) / c^2 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hL : 0 < Real.log q := Real.log_pos hq
  have hb1 : (1:ℝ) ≤ q ^ x₀ := Real.one_le_rpow hq.le hx₀.le
  -- `Icc 1 (q^x₀)` avoids `0`, so all the elementary functions are continuous there.
  have hnotmem : ∀ t ∈ Set.Icc (1:ℝ) (q^x₀), t ≠ 0 := fun t ht =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
  -- Step 1: pointwise domination of the integrand
  have hpt : ∀ t ∈ Set.Icc (1:ℝ) (q^x₀),
      Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q))
        ≤ Real.exp (lam * x₀) * (t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t))) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hlogt_le : Real.log t ≤ x₀ * Real.log q := by
      calc Real.log t ≤ Real.log (q ^ x₀) := Real.log_le_log htpos ht.2
        _ = x₀ * Real.log q := Real.log_rpow hq0 x₀
    have hLpos : 0 < lam / Real.log q := div_pos hlam hL
    have hrpow : t ^ (lam / Real.log q) = Real.exp (Real.log t * (lam / Real.log q)) :=
      Real.rpow_def_of_pos htpos _
    have hle1 : Real.log t * (lam / Real.log q) ≤ lam * x₀ := by
      calc Real.log t * (lam / Real.log q)
            ≤ (x₀ * Real.log q) * (lam / Real.log q) :=
              mul_le_mul_of_nonneg_right hlogt_le hLpos.le
        _ = lam * x₀ := by field_simp
    have hexp : t ^ (lam / Real.log q) ≤ Real.exp (lam * x₀) := by
      rw [hrpow]; exact Real.exp_le_exp.mpr hle1
    have hsplit : t ^ (-(1 - lam / Real.log q)) = t⁻¹ * t ^ (lam / Real.log q) := by
      have h : -(1 - lam / Real.log q) = -1 + lam / Real.log q := by ring
      rw [h, Real.rpow_add htpos, Real.rpow_neg_one]
    have hEpos : 0 ≤ Real.exp (-c * Real.sqrt (Real.log t)) := (Real.exp_pos _).le
    have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr htpos.le
    calc Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q))
        = Real.exp (-c * Real.sqrt (Real.log t)) * (t⁻¹ * t ^ (lam / Real.log q)) := by rw [hsplit]
      _ ≤ Real.exp (-c * Real.sqrt (Real.log t)) * (t⁻¹ * Real.exp (lam * x₀)) := by
            apply mul_le_mul_of_nonneg_left _ hEpos
            exact mul_le_mul_of_nonneg_left hexp htinv
      _ = Real.exp (lam * x₀) * (t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t))) := by ring
  -- Continuity of the two integrands on `[1, q^x₀]`
  have hsq : ContinuousOn (fun t => Real.sqrt (Real.log t)) (Set.Icc (1:ℝ) (q^x₀)) :=
    Real.continuous_sqrt.comp_continuousOn
      (Real.continuousOn_log.mono (by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact hnotmem t ht))
  have hEcont : ContinuousOn (fun t => Real.exp (-c * Real.sqrt (Real.log t)))
      (Set.Icc (1:ℝ) (q^x₀)) :=
    Real.continuous_exp.comp_continuousOn (hsq.const_mul (-c))
  have hJcont : ContinuousOn (fun t => t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t)))
      (Set.Icc (1:ℝ) (q^x₀)) :=
    (continuousOn_id.inv₀ (fun t ht => hnotmem t ht)).mul hEcont
  have hrpowc : ContinuousOn (fun t : ℝ => t ^ (-(1 - lam / Real.log q)))
      (Set.Icc (1:ℝ) (q^x₀)) :=
    ContinuousOn.rpow continuousOn_id continuousOn_const
      (fun t ht => Or.inl (hnotmem t ht))
  have hHcont : ContinuousOn
      (fun t => Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q)))
      (Set.Icc (1:ℝ) (q^x₀)) := hEcont.mul hrpowc
  -- Step 2: the integral of `t⁻¹ exp(-c√(log t))` is at most `2/c²`
  have hInt : (∫ t in (1:ℝ)..q^x₀, t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t)))
      ≤ 2 / c^2 := by
    have hderiv : ∀ x ∈ Set.Ioo (1:ℝ) (q^x₀),
        HasDerivAt (fun t => -(2/c^2) * ((1 + c * Real.sqrt (Real.log t)) * Real.exp (-c * Real.sqrt (Real.log t))))
          (x⁻¹ * Real.exp (-c * Real.sqrt (Real.log x))) x := by
      intro x hx
      have h2 : -(2/c^2) * (-(c^2 * x⁻¹ * Real.exp (-c * Real.sqrt (Real.log x)) / 2))
          = x⁻¹ * Real.exp (-c * Real.sqrt (Real.log x)) := by
        field_simp
      have hd := (hasDerivAt_psi c x hx.1).const_mul (-(2/c^2))
      rw [h2] at hd
      exact hd
    have hKcont : ContinuousOn
        (fun t => -(2/c^2) * ((1 + c * Real.sqrt (Real.log t)) * Real.exp (-c * Real.sqrt (Real.log t))))
        (Set.Icc (1:ℝ) (q^x₀)) :=
      (((hsq.const_mul c).const_add 1).mul hEcont).const_mul (-(2/c^2))
    have hJcont_u : ContinuousOn (fun t => t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t)))
        (Set.uIcc (1:ℝ) (q^x₀)) := by
      rw [Set.uIcc_of_le hb1]; exact hJcont
    have hint : IntervalIntegrable (fun t => t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t)))
        volume (1:ℝ) (q^x₀) := hJcont_u.intervalIntegrable
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := (1:ℝ)) (b := q^x₀)
      (f := fun t => -(2/c^2) * ((1 + c * Real.sqrt (Real.log t)) * Real.exp (-c * Real.sqrt (Real.log t))))
      (f' := fun t => t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t))) hb1 hKcont hderiv hint
    have hK1 : -(2/c^2) * ((1 + c * Real.sqrt (Real.log (1:ℝ))) * Real.exp (-c * Real.sqrt (Real.log (1:ℝ))))
        = -(2/c^2) := by
      norm_num [Real.log_one]
    have hKb : -(2/c^2) * ((1 + c * Real.sqrt (Real.log (q^x₀))) * Real.exp (-c * Real.sqrt (Real.log (q^x₀))))
        ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
      exact mul_nonneg (by
        have : 0 ≤ c * Real.sqrt (Real.log (q^x₀)) := mul_nonneg hc.le (Real.sqrt_nonneg _)
        linarith) (Real.exp_pos _).le
    rw [hfund, hK1]
    linarith [hKb]
  -- Step 3: assemble
  have hmono : (∫ t in (1:ℝ)..q^x₀,
        Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q)))
      ≤ ∫ t in (1:ℝ)..q^x₀,
          Real.exp (lam * x₀) * (t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t))) := by
    have hHcont_u : ContinuousOn
        (fun t => Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q)))
        (Set.uIcc (1:ℝ) (q^x₀)) := by
      rw [Set.uIcc_of_le hb1]; exact hHcont
    have hGcont_u : ContinuousOn
        (fun t => Real.exp (lam * x₀) * (t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t))))
        (Set.uIcc (1:ℝ) (q^x₀)) := by
      rw [Set.uIcc_of_le hb1]; exact hJcont.const_mul (Real.exp (lam * x₀))
    exact intervalIntegral.integral_mono_on hb1 hHcont_u.intervalIntegrable
      hGcont_u.intervalIntegrable hpt
  calc (∫ t in (1:ℝ)..q^x₀, Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q)))
      ≤ ∫ t in (1:ℝ)..q^x₀, Real.exp (lam * x₀) * (t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t))) := hmono
    _ = Real.exp (lam * x₀) * ∫ t in (1:ℝ)..q^x₀, t⁻¹ * Real.exp (-c * Real.sqrt (Real.log t)) := by
          rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.exp (lam * x₀) * (2 / c^2) :=
          mul_le_mul_of_nonneg_left hInt (Real.exp_pos _).le
    _ ≤ 2 * Real.exp (R * x₀) / c^2 := by
          have hle : Real.exp (lam * x₀) ≤ Real.exp (R * x₀) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlamR hx₀.le)
          have hc2 : 0 ≤ 2 / c^2 := by positivity
          have : Real.exp (lam * x₀) * (2 / c^2) = 2 * Real.exp (lam * x₀) / c^2 := by ring
          calc Real.exp (lam * x₀) * (2 / c^2) = 2 * Real.exp (lam * x₀) / c^2 := this
            _ ≤ 2 * Real.exp (R * x₀) / c^2 := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                linarith [hle]

end Work.LinnikAreas.A5
