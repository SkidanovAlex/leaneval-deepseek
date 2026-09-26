import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

noncomputable section

open MeasureTheory UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics

/-! ## Elementary decay and moment estimates on `(1, ∞)` -/

/-- For `c > 0` and any real exponent `M`, the function `t ↦ t ^ M * exp (-(c * t))` is
integrable on `(1, ∞)`: the exponential beats every power. -/
lemma integrableOn_rpow_mul_exp_neg_mul_Ioi (M c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ M * Real.exp (-(c * t))) (Set.Ioi (1 : ℝ)) := by
  have hc2 : 0 < c / 2 := by linarith
  have hlim : Filter.Tendsto (fun t : ℝ => t ^ M * Real.exp ((-(c / 2)) * t))
      Filter.atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero M (c / 2) hc2
  have hev : ∀ᶠ t : ℝ in Filter.atTop, t ^ M * Real.exp ((-(c / 2)) * t) < 1 :=
    hlim.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Iio 1))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  have hT1 : 1 ≤ max T 1 := le_max_right T 1
  have key : ∀ t : ℝ, max T 1 ≤ t → t ^ M ≤ Real.exp ((c / 2) * t) := by
    intro t ht
    have h1 : t ^ M * Real.exp ((-(c / 2)) * t) < 1 := hT t (le_trans (le_max_left T 1) ht)
    have hmul : Real.exp ((-(c / 2)) * t) * Real.exp ((c / 2) * t) = 1 := by
      rw [← Real.exp_add, show (-(c / 2)) * t + (c / 2) * t = 0 by ring, Real.exp_zero]
    calc t ^ M = t ^ M * 1 := (mul_one _).symm
      _ = t ^ M * (Real.exp ((-(c / 2)) * t) * Real.exp ((c / 2) * t)) := by rw [hmul]
      _ = (t ^ M * Real.exp ((-(c / 2)) * t)) * Real.exp ((c / 2) * t) := by ring
      _ ≤ 1 * Real.exp ((c / 2) * t) :=
            mul_le_mul_of_nonneg_right h1.le (Real.exp_nonneg _)
      _ = Real.exp ((c / 2) * t) := one_mul _
  have hcont : ContinuousOn (fun t : ℝ => t ^ M * Real.exp (-(c * t))) (Set.Ici (1 : ℝ)) := by
    have h1 : ContinuousOn (fun t : ℝ => t ^ M) (Set.Ici (1 : ℝ)) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (by linarith [Set.mem_Ici.mp hx]))
    have h2 : ContinuousOn (fun t : ℝ => Real.exp (-(c * t))) (Set.Ici (1 : ℝ)) :=
      ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))).continuousOn
    exact h1.mul h2
  have hleft : IntegrableOn (fun t : ℝ => t ^ M * Real.exp (-(c * t)))
      (Set.Ioc (1 : ℝ) (max T 1)) :=
    ((hcont.mono Set.Icc_subset_Ici_self).integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hright : IntegrableOn (fun t : ℝ => t ^ M * Real.exp (-(c * t)))
      (Set.Ioi (max T 1)) := by
    refine Integrable.mono' (exp_neg_integrableOn_Ioi (max T 1) hc2) ?_ ?_
    · exact ((hcont.mono (fun t ht => le_of_lt (lt_of_le_of_lt hT1 (Set.mem_Ioi.mp ht))))).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htT : max T 1 ≤ t := le_of_lt ht
      have htM : 0 ≤ t ^ M := Real.rpow_nonneg (by linarith [hT1.trans htT]) M
      have hsplit : t ^ M * Real.exp (-(c * t))
          = (t ^ M * Real.exp ((-(c / 2)) * t)) * Real.exp ((-(c / 2)) * t) := by
        rw [mul_assoc, ← Real.exp_add,
          show (-(c / 2)) * t + (-(c / 2)) * t = -(c * t) by ring]
      have hb : t ^ M * Real.exp ((-(c / 2)) * t) ≤ 1 := by
        have h := key t htT
        have h2 := mul_le_mul_of_nonneg_right h (Real.exp_pos ((-(c / 2)) * t)).le
        rwa [show Real.exp ((c / 2) * t) * Real.exp ((-(c / 2)) * t) = 1 by
          rw [← Real.exp_add, show (c / 2) * t + (-(c / 2)) * t = 0 by ring, Real.exp_zero]] at h2
      rw [Real.norm_of_nonneg (mul_nonneg htM (Real.exp_nonneg _)), hsplit]
      calc (t ^ M * Real.exp ((-(c / 2)) * t)) * Real.exp ((-(c / 2)) * t)
          ≤ 1 * Real.exp ((-(c / 2)) * t) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
        _ = Real.exp ((-(c / 2)) * t) := one_mul _
  have hunion := hleft.union hright
  have hset : Set.Ioc (1 : ℝ) (max T 1) ∪ Set.Ioi (max T 1) = Set.Ioi (1 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact h1
      · exact lt_of_le_of_lt hT1 h3
    · intro h1
      by_cases h2 : t ≤ max T 1
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (lt_of_not_ge h2)
  rwa [hset] at hunion

/-- The same decay test on any right half-line contained in `(0,∞)`. -/
lemma integrableOn_rpow_mul_exp_neg_mul_Ioi_pos (M : ℝ) {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => t ^ M * Real.exp (-(d * t))) (Set.Ioi a) := by
  rcases le_or_gt 1 a with h1 | h1
  · exact (integrableOn_rpow_mul_exp_neg_mul_Ioi M d hd).mono_set (Set.Ioi_subset_Ioi h1)
  · have hcont : ContinuousOn (fun t : ℝ => t ^ M * Real.exp (-(d * t))) (Set.Icc a 1) := by
      have h1' : ContinuousOn (fun t : ℝ => t ^ M) (Set.Icc a 1) :=
        ContinuousOn.rpow_const continuousOn_id
          (fun x hx => Or.inl (by linarith [hx.1]))
      exact h1'.mul ((Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg))).continuousOn
    have hleft : IntegrableOn (fun t : ℝ => t ^ M * Real.exp (-(d * t))) (Set.Ioc a 1) :=
      (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hright : IntegrableOn (fun t : ℝ => t ^ M * Real.exp (-(d * t))) (Set.Ioi 1) :=
      integrableOn_rpow_mul_exp_neg_mul_Ioi M d hd
    have hunion := hleft.union hright
    have hset : Set.Ioc a 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi a := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h3)
        · exact h1
        · exact lt_trans h1 h3
      · intro h1
        by_cases h2 : t ≤ 1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (lt_of_not_ge h2)
    rwa [hset] at hunion

/-- The derivative of `y ↦ exp (-(c * y))` with respect to the real variable. -/
lemma hasDerivAt_exp_neg_mul (c : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(c : ℂ) * (y : ℂ)))
      (Complex.exp (-(c : ℂ) * (x : ℂ)) * (-(c : ℂ))) x := by
  have hinner : HasDerivAt (fun y : ℝ => -(c : ℂ) * (y : ℂ)) (-(c : ℂ)) x := by
    simpa using ((HasDerivAt.ofReal_comp (hasDerivAt_id x)).const_mul (-(c : ℂ)))
  exact (Complex.hasDerivAt_exp (-(c : ℂ) * (x : ℂ))).comp x hinner

/-- `exp (-(c * y))` as a complex exponential. -/
lemma exp_neg_mul_ofReal (c y : ℝ) :
    Complex.exp (-(c : ℂ) * (y : ℂ)) = ((Real.exp (-(c * y)) : ℝ) : ℂ) := by
  rw [show -(c : ℂ) * (y : ℂ) = ((-(c * y) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]

/-- `t ↦ exp (-(c t))` is integrable on `(1,∞)` for `c > 0`. -/
lemma integrableOn_exp_neg_mul_complex (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ)) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 1 hc) ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    rw [Complex.norm_exp]
    have hre : (-(c : ℂ) * (t : ℂ)).re = -(c * t) := by simp
    rw [hre]
    exact le_of_eq (by ring_nf)

/-- `t ↦ t · exp (-(c t))` is integrable on `(1,∞)` for `c > 0`. -/
lemma integrableOn_id_mul_exp_neg_mul_complex (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ)) := by
  have hdom : IntegrableOn (fun t : ℝ => t * Real.exp (-(c * t))) (Set.Ioi (1 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_Ioi 1 c hc
    simpa [Real.rpow_one] using h
  refine Integrable.mono' hdom ?_ ?_
  · exact (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := by linarith [Set.mem_Ioi.mp ht]
    simp [Complex.norm_exp, abs_of_nonneg ht0]

/-- `∫_1^∞ exp (-(c t)) dt = exp (-c)/c` for `c > 0`. -/
lemma integral_exp_neg_mul_Ioi_one {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (1 : ℝ), Complex.exp (-(c : ℂ) * (t : ℂ)) = Complex.exp (-(c : ℂ)) / (c : ℂ) := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hderiv : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => -(Complex.exp (-(c : ℂ) * (y : ℂ))) / (c : ℂ))
        (Complex.exp (-(c : ℂ) * (x : ℂ))) x := by
    intro x _
    have h := ((hasDerivAt_exp_neg_mul c x).neg).div_const (c : ℂ)
    refine h.congr_deriv ?_
    field_simp
  have hint := integrableOn_exp_neg_mul_complex c hc
  have hreal : Filter.Tendsto (fun y : ℝ => Real.exp (-(c * y))) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => -(c * y)) Filter.atTop Filter.atBot :=
      (Filter.Tendsto.const_mul_atTop_of_neg (show -c < 0 by linarith) Filter.tendsto_id).congr'
        (Filter.Eventually.of_forall (fun y => by simp))
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h1
  have hcplx : Filter.Tendsto (fun y : ℝ => Complex.exp (-(c : ℂ) * (y : ℂ))) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => ((Real.exp (-(c * y)) : ℝ) : ℂ)) Filter.atTop (𝓝 ((0:ℝ):ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp hreal
    simpa [exp_neg_mul_ofReal, Complex.ofReal_zero] using h1
  have htend : Filter.Tendsto (fun y : ℝ => -(Complex.exp (-(c : ℂ) * (y : ℂ))) / (c : ℂ))
      Filter.atTop (𝓝 0) := by
    simpa using hcplx.neg.div_const (c : ℂ)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun y : ℝ => -(Complex.exp (-(c : ℂ) * (y : ℂ))) / (c : ℂ))
    (f' := fun y : ℝ => Complex.exp (-(c : ℂ) * (y : ℂ))) hderiv hint htend
  rw [h, Complex.ofReal_one, mul_one, zero_sub, ← neg_div, neg_neg]

/-- `∫_1^∞ t exp (-(c t)) dt = exp (-c)(c+1)/c²` for `c > 0`. -/
lemma integral_id_mul_exp_neg_mul_Ioi_one {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))
      = Complex.exp (-(c : ℂ)) * ((c : ℂ) + 1) / (c : ℂ) ^ 2 := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hderiv : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => -(((y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2)
          * Complex.exp (-(c : ℂ) * (y : ℂ))))
        ((x : ℂ) * Complex.exp (-(c : ℂ) * (x : ℂ))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2)
        ((1 : ℂ) / (c : ℂ)) x := by
      simpa using ((HasDerivAt.ofReal_comp (hasDerivAt_id x)).div_const (c : ℂ)).add_const
        (1 / (c : ℂ) ^ 2)
    have h2 := hasDerivAt_exp_neg_mul c x
    have h := (h1.mul h2).neg
    refine h.congr_deriv ?_
    field_simp
    ring
  have hint := integrableOn_id_mul_exp_neg_mul_complex c hc
  have hreal1 : Filter.Tendsto (fun y : ℝ => y * Real.exp (-(c * y))) Filter.atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
    simpa [Real.rpow_one] using h
  have hcplx1 : Filter.Tendsto (fun y : ℝ => (y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ)))
      Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => ((y * Real.exp (-(c * y)) : ℝ) : ℂ))
        Filter.atTop (𝓝 ((0:ℝ):ℂ)) := (Complex.continuous_ofReal.tendsto 0).comp hreal1
    simpa [Complex.ofReal_mul, exp_neg_mul_ofReal, Complex.ofReal_zero] using h1
  have hcplx : Filter.Tendsto (fun y : ℝ => Complex.exp (-(c : ℂ) * (y : ℂ)))
      Filter.atTop (𝓝 0) := by
    have hreal : Filter.Tendsto (fun y : ℝ => Real.exp (-(c * y))) Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun y : ℝ => -(c * y)) Filter.atTop Filter.atBot :=
        (Filter.Tendsto.const_mul_atTop_of_neg (show -c < 0 by linarith) Filter.tendsto_id).congr'
          (Filter.Eventually.of_forall (fun y => by simp))
      simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h1
    have h1 : Filter.Tendsto (fun y : ℝ => ((Real.exp (-(c * y)) : ℝ) : ℂ))
        Filter.atTop (𝓝 ((0:ℝ):ℂ)) := (Complex.continuous_ofReal.tendsto 0).comp hreal
    simpa [exp_neg_mul_ofReal, Complex.ofReal_zero] using h1
  have hF : Filter.Tendsto (fun y : ℝ => -(((y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2)
      * Complex.exp (-(c : ℂ) * (y : ℂ)))) Filter.atTop (𝓝 0) := by
    have h2 : (fun y : ℝ => -(((y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2)
        * Complex.exp (-(c : ℂ) * (y : ℂ))))
        = fun y : ℝ => -((1 / (c : ℂ)) * ((y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ))))
            - (1 / (c : ℂ) ^ 2) * Complex.exp (-(c : ℂ) * (y : ℂ)) := by
      funext y; ring
    rw [h2]
    have hA : Filter.Tendsto (fun y : ℝ => -((1 / (c : ℂ))
        * ((y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ))))) Filter.atTop (𝓝 (-((1 / (c : ℂ)) * 0))) :=
      (hcplx1.const_mul (1 / (c : ℂ))).neg
    have hB : Filter.Tendsto (fun y : ℝ => (1 / (c : ℂ) ^ 2)
        * Complex.exp (-(c : ℂ) * (y : ℂ))) Filter.atTop (𝓝 ((1 / (c : ℂ) ^ 2) * 0)) :=
      hcplx.const_mul (1 / (c : ℂ) ^ 2)
    have hC : Filter.Tendsto (fun y : ℝ => -((1 / (c : ℂ))
        * ((y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ))))
          - (1 / (c : ℂ) ^ 2) * Complex.exp (-(c : ℂ) * (y : ℂ)))
        Filter.atTop (𝓝 (-((1 / (c : ℂ)) * 0) - (1 / (c : ℂ) ^ 2) * 0)) := hA.sub hB
    have hD : Filter.Tendsto (fun y : ℝ => -((1 / (c : ℂ))
        * ((y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ))))
          - (1 / (c : ℂ) ^ 2) * Complex.exp (-(c : ℂ) * (y : ℂ)))
        Filter.atTop (𝓝 0) := by
      simpa using hC
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun y => by ring)) hD
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun y : ℝ => -(((y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2)
      * Complex.exp (-(c : ℂ) * (y : ℂ))))
    (f' := fun y : ℝ => (y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ))) hderiv hint hF
  rw [h]
  simp only [Complex.ofReal_one, mul_one, zero_sub, neg_neg]
  rw [show ((1 : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2) = ((c : ℂ) + 1) / (c : ℂ) ^ 2 by field_simp]
  ring

/-- If `d ≤ 0`, then `e^{-d t}` is not integrable on `(T, ∞)`: it does not decay. -/
lemma not_integrableOn_exp_neg_of_nonpos {d : ℝ} (hd : d ≤ 0) (T : ℝ) :
    ¬ IntegrableOn (fun t : ℝ => Real.exp (-d * t)) (Set.Ioi T) := by
  intro hI
  set T' : ℝ := max T 0 with hT'def
  have hTT' : T ≤ T' := le_max_left T 0
  have hT'0 : 0 ≤ T' := le_max_right T 0
  have hle1 : ∀ t ∈ Set.Ioi T', (1 : ℝ) ≤ Real.exp (-d * t) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt hT'0 ht)
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (-d * t) := Real.exp_le_exp.mpr (mul_nonneg (by linarith) ht0)
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi T') := by
    refine Integrable.mono' (hI.mono_set (Set.Ioi_subset_Ioi hTT'))
      measurable_const.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_one]
    exact hle1 t ht
  obtain h3 | h3 := (integrableOn_const_iff (C := (1 : ℝ))).mp h1
  · norm_num at h3
  · rw [Real.volume_Ioi] at h3
    exact absurd h3 (not_lt.mpr le_top)

/-- If `d ≤ 0`, a non-zero affine function of `t` times `e^{-d t}` is not integrable on
`(1,∞)`: the exponential does not decay and the affine factor stays away from `0`. -/
lemma eq_zero_of_integrableOn_affine_mul_exp_neg {d : ℝ} (hd : d ≤ 0) {a b : ℂ}
    (h : IntegrableOn (fun t : ℝ =>
      (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(d : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ))) :
    a = 0 ∧ b = 0 := by
  by_contra hcon
  obtain ⟨T, ε, hε, hT⟩ : ∃ T ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, T ≤ t → ε ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
    rcases eq_or_ne b 0 with hb | hb
    · subst hb
      refine ⟨0, ‖a‖, norm_pos_iff.mpr ?_, fun t _ => ?_⟩
      · intro h0; exact hcon ⟨h0, rfl⟩
      · simp
    · have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
      refine ⟨(‖a‖ + 1) / ‖b‖, 1, one_pos, fun t ht => ?_⟩
      have hTpos : 0 < (‖a‖ + 1) / ‖b‖ := div_pos (by positivity) hbpos
      have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le hTpos ht)
      have h1 : ‖a‖ + 1 ≤ t * ‖b‖ := (div_le_iff₀ hbpos).mp ht
      have h3 : ‖(t : ℂ) * Complex.I * b‖ - ‖a‖ ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
        have h4 := norm_sub_le (a + (t : ℂ) * Complex.I * b) a
        rw [add_sub_cancel_left] at h4
        linarith
      have h5 : ‖(t : ℂ) * Complex.I * b‖ = t * ‖b‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        congr 1
        simp [abs_of_nonneg ht0]
      rw [h5] at h3
      linarith
  set T' : ℝ := max T 1 with hT'def
  have hT'1 : (1 : ℝ) ≤ T' := le_max_right T 1
  have hTT' : T ≤ T' := le_max_left T 1
  have hpoint : ∀ t ∈ Set.Ioi T', ε * Real.exp (-d * t) ≤
      ‖(a + (t : ℂ) * Complex.I * b) * Complex.exp (-(d : ℂ) * (t : ℂ))‖ := by
    intro t ht
    have htT : T ≤ t := le_trans hTT' (le_of_lt (Set.mem_Ioi.mp ht))
    have ht0 : 0 ≤ t := by have := Set.mem_Ioi.mp ht; linarith
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(d : ℂ) * (t : ℂ)).re = -d * t := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hT t htT) (Real.exp_nonneg _)
  have hint1 : IntegrableOn (fun t : ℝ => ε * Real.exp (-d * t)) (Set.Ioi T') := by
    refine Integrable.mono' (h.mono_set (Set.Ioi_subset_Ioi hT'1)).norm ?_ ?_
    · exact ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (mul_nonneg hε.le (Real.exp_nonneg _))]
      exact hpoint t ht
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-d * t)) (Set.Ioi T') := by
    have h2 : IntegrableOn (fun x : ℝ => ε⁻¹ * (ε * Real.exp (-d * x))) (Set.Ioi T') :=
      Integrable.const_mul hint1 (ε⁻¹)
    exact IntegrableOn.congr_fun h2
      (fun t _ => inv_mul_cancel_left₀ hε.ne' (Real.exp (-d * t))) measurableSet_Ioi
  exact absurd hint2 (not_integrableOn_exp_neg_of_nonpos hd T')



/-- The two moment integrals on `(1, ∞)` in the affine shape used in the main theorem:
for `c > 0`, `∫_1^∞ (a + i b t)e^{-ct}dt = a·e^{-c}/c + ib·e^{-c}(c+1)/c²`. -/
lemma integral_affine_mul_exp_neg_mul_Ioi_one {c : ℝ} (hc : 0 < c) (a b : ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(c : ℂ) * (t : ℂ))
      = a * (Complex.exp (-(c : ℂ)) / (c : ℂ))
        + (Complex.I * b) * (Complex.exp (-(c : ℂ)) * ((c : ℂ) + 1) / (c : ℂ) ^ 2) := by
  have hE := integrableOn_exp_neg_mul_complex c hc
  have hI := integrableOn_id_mul_exp_neg_mul_complex c hc
  have h1 : IntegrableOn (fun t : ℝ => a * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi 1) :=
    Integrable.const_mul hE a
  have h2 : IntegrableOn (fun t : ℝ => (Complex.I * b)
      * ((t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ)))) (Set.Ioi 1) :=
    Integrable.const_mul hI (Complex.I * b)
  rw [show (∫ t in Set.Ioi (1 : ℝ), (a + (t : ℂ) * Complex.I * b)
        * Complex.exp (-(c : ℂ) * (t : ℂ)))
      = ∫ t in Set.Ioi (1 : ℝ), (a * Complex.exp (-(c : ℂ) * (t : ℂ))
          + (Complex.I * b) * ((t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ)))) from
      setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring),
    integral_add h1 h2]
  rw [integral_const_mul, integral_exp_neg_mul_Ioi_one hc,
    integral_const_mul, integral_id_mul_exp_neg_mul_Ioi_one hc]


/-! ## The `high` part and the closed forms -/

/-- Multiplying an integrable real function by a constant. -/
lemma integrableOn_const_mul_real {f : ℝ → ℝ} {s : Set ℝ} (h : IntegrableOn f s) (c : ℝ) :
    IntegrableOn (fun x : ℝ => c * f x) s := Integrable.const_mul h c

/-- A non-zero affine function times a *decaying* exponential with `c > 0` is integrable on
`(1, ∞)`. -/
lemma integrableOn_affine_mul_exp_neg_mul_complex (c : ℝ) (hc : 0 < c) (a b : ℂ) :
    IntegrableOn (fun t : ℝ => (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(c : ℂ) * (t : ℂ)))
      (Set.Ioi (1 : ℝ)) := by
  have hbase : IntegrableOn (fun t : ℝ => t * Real.exp (-(c * t))) (Set.Ioi (1 : ℝ)) := by
    simpa [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_Ioi 1 c hc
  have hdom : IntegrableOn (fun t : ℝ => (‖a‖ + ‖b‖) * (t * Real.exp (-(c * t))))
      (Set.Ioi (1 : ℝ)) := integrableOn_const_mul_real hbase (‖a‖ + ‖b‖)
  refine Integrable.mono' hdom ?_ ?_
  · exact ((continuous_const.add ((Complex.continuous_ofReal.mul continuous_const).mul
        continuous_const)).mul (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    have ht0 : (0 : ℝ) ≤ t := by linarith
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(c : ℂ) * (t : ℂ)).re = -(c * t) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      ring
    rw [hre]
    have h1 : ‖a + (t : ℂ) * Complex.I * b‖ ≤ (‖a‖ + ‖b‖) * t := by
      calc ‖a + (t : ℂ) * Complex.I * b‖ ≤ ‖a‖ + ‖(t : ℂ) * Complex.I * b‖ := norm_add_le _ _
        _ = ‖a‖ + t * ‖b‖ := by
              rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
              congr 1
              simp [abs_of_nonneg ht0]
        _ ≤ (‖a‖ + ‖b‖) * t := by nlinarith [ht1, norm_nonneg a, norm_nonneg b]
    calc ‖a + (t : ℂ) * Complex.I * b‖ * Real.exp (-(c * t))
        ≤ ((‖a‖ + ‖b‖) * t) * Real.exp (-(c * t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = (‖a‖ + ‖b‖) * (t * Real.exp (-(c * t))) := by ring

/-- `sinSq r = 2 - 2 cos (π r²)`. -/
lemma sinSq_eq_two_sub_two_cos (r : ℝ) :
    sinSq r = ((2 - 2 * Real.cos (Real.pi * r ^ 2) : ℝ) : ℂ) := by
  have h1 : sinSq r = ((4 * Real.sin (Real.pi * r ^ 2 / 2) ^ 2 : ℝ) : ℂ) := by
    rw [sinSq, show Real.pi * (r : ℂ) ^ 2 / 2 = ((Real.pi * r ^ 2 / 2 : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [h1]
  congr 1
  have h := Real.cos_two_mul' (Real.pi * r ^ 2 / 2)
  have h2 := Real.sin_sq (Real.pi * r ^ 2 / 2)
  have h3 : 2 * (Real.pi * r ^ 2 / 2) = Real.pi * r ^ 2 := by ring
  rw [h3] at h
  linarith

/-- `sinSq r = 2 - 2 cos (π r² - 2π)`, by the periodicity of `cos`. -/
lemma sinSq_eq_two_sub_two_cos_sub (r : ℝ) :
    sinSq r = ((2 - 2 * Real.cos (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ) := by
  rw [sinSq_eq_two_sub_two_cos r]
  congr 1
  rw [Real.cos_sub_two_pi]

/-- The second zero of `2 - 2 cos`: `psi1 (2π) = 0`. -/
lemma psi1_two_pi : psi1 (2 * Real.pi) = 0 := by
  have h := sq_mul_psi1 (2 * Real.pi)
  rw [Real.cos_two_pi] at h
  have h' : (2 * Real.pi) ^ 2 * psi1 (2 * Real.pi) = 0 := by linarith
  exact (mul_eq_zero.mp h').resolve_left (by positivity)

/-- The regularisation of the `c^{-1}` pole of `∫_1^∞ e^{-ct}dt`: for `c ≠ 0`,
`(2 - 2cos c)·(E/c) = c·psi1 c·E`. -/
lemma two_sub_two_cos_mul_div {c : ℝ} (hc : c ≠ 0) (E : ℂ) :
    ((2 - 2 * Real.cos c : ℝ) : ℂ) * (E / (c : ℂ)) = (c : ℂ) * (psi1 c : ℂ) * E := by
  have h : ((2 - 2 * Real.cos c : ℝ) : ℂ) = (c : ℂ) ^ 2 * (psi1 c : ℂ) := by
    rw [← sq_mul_psi1 c]; push_cast; ring
  rw [h]
  field_simp

/-- The regularisation of the `c^{-2}` pole: for `c ≠ 0`,
`(2 - 2cos c)·(E(c+1)/c²) = psi1 c·(c+1)·E`. -/
lemma two_sub_two_cos_mul_div_sq {c : ℝ} (hc : c ≠ 0) (E : ℂ) :
    ((2 - 2 * Real.cos c : ℝ) : ℂ) * (E * ((c : ℂ) + 1) / (c : ℂ) ^ 2)
      = (psi1 c : ℂ) * ((c : ℂ) + 1) * E := by
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have h : ((2 - 2 * Real.cos c : ℝ) : ℂ) = (c : ℂ) ^ 2 * (psi1 c : ℂ) := by
    rw [← sq_mul_psi1 c]; push_cast; ring
  rw [h]
  field_simp

/-- **The closed form of the `high` part.**  Multiplying the two-term closed form of
`∫_1^∞ (a + bt)e^{-ct}dt` by `2 - 2cos c = c²psi1 c` gives the `psi1`-regularised expression
appearing in `highPart`. -/
lemma sinSq_mul_closed {r c : ℝ} (hc : c ≠ 0)
    (hcos : sinSq r = ((2 - 2 * Real.cos c : ℝ) : ℂ)) (E a b : ℂ) :
    sinSq r * (a * (E / (c : ℂ)) + b * (E * ((c : ℂ) + 1) / (c : ℂ) ^ 2))
      = (c : ℂ) * (psi1 c : ℂ) * E * a
        + (psi1 c : ℂ) * ((c : ℂ) + 1) * E * b := by
  rw [hcos, mul_add,
    show ((2 - 2 * Real.cos c : ℝ) : ℂ) * (a * (E / (c : ℂ)))
        = a * (((2 - 2 * Real.cos c : ℝ) : ℂ) * (E / (c : ℂ))) by ring,
    two_sub_two_cos_mul_div hc E,
    show ((2 - 2 * Real.cos c : ℝ) : ℂ) * (b * (E * ((c : ℂ) + 1) / (c : ℂ) ^ 2))
        = b * (((2 - 2 * Real.cos c : ℝ) : ℂ) * (E * ((c : ℂ) + 1) / (c : ℂ) ^ 2)) by ring,
    two_sub_two_cos_mul_div_sq hc E]
  ring

/-- `highPart` written with its four `psi1` factors. -/
lemma highPart_eq_closed (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    highPart G τ r =
      ((Real.pi * r ^ 2 : ℝ) : ℂ) * (psi1 (Real.pi * r ^ 2) : ℂ)
          * Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ)) * G 0 0 τ
      + (psi1 (Real.pi * r ^ 2) : ℂ) * (((Real.pi * r ^ 2 : ℝ) : ℂ) + 1)
          * Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ)) * (Complex.I * G 0 1 τ)
      + ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) * (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
          * Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) * G 1 0 τ
      + (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
          * (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) + 1)
          * Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) * (Complex.I * G 1 1 τ) := by
  rw [show highPart G τ r =
      ((Real.pi * r ^ 2 : ℝ) : ℂ) * (psi1 (Real.pi * r ^ 2) : ℂ)
          * Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ)) * G 0 0 τ
      + Complex.I * (psi1 (Real.pi * r ^ 2) : ℂ) * (((Real.pi * r ^ 2 : ℝ) : ℂ) + 1)
          * Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ)) * G 0 1 τ
      + ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) * (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
          * Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) * G 1 0 τ
      + Complex.I * (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
          * (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) + 1)
          * Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) * G 1 1 τ from rfl]
  ring


/-- **The `low + trunc + high` decomposition reproduces the contour integral.**  Wherever the
Bochner integral `∫_0^∞ K^{(d)}(τ,it) e^{-πr²t} dt` converges, the CKMRV layer
`paperLayer = layerLow + layerTrunc + highPart` equals `4 sin²(πr²/2)` times it, i.e.
`Work.Kernels.kernelTransform (Kfun ℓ d) τ r`.

The proof is the telescoping `∫_0^∞ = ∫_0^1 + ∫_1^∞ = ∫_0^1 + ∫_1^∞(K - A) + ∫_1^∞ A` together
with the closed form of `∫_1^∞ A(τ,it)e^{-πr²t}dt`, which is `highPart` (the double zeros of
`2 - 2cos(πr²) = 4 sin²(πr²/2)` at `λ = πr² = 0` and at `μ = πr² - 2π = 0` being exactly the
factors `psi1`). -/
theorem paperLayer_agreement (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    (h8 : d = 8 → ∀ j : Fin 2, G 1 j = 0)
    (htail : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ τ : UpperHalfPlane,
      τ ∈ Work.Asymptotics.DomainD →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (Work.Kernels.scale τ) ^ N * t ^ M * Real.exp (-(Real.pi * t))) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      Work.Asymptotics.paperLayer G ℓ d τ r
        = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r := by
  intro τ r hτ hr hInt
  obtain ⟨C, N, M, hC, hN, hM, hAe⟩ := htail
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  set L : ℝ := Real.pi * r ^ 2 with hL
  set Mu : ℝ := L - 2 * Real.pi with hMu
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLne : L ≠ 0 := hLpos.ne'
  have hcosL : sinSq r = ((2 - 2 * Real.cos L : ℝ) : ℂ) := by
    rw [sinSq_eq_two_sub_two_cos r, hL]
  have hcosMu : sinSq r = ((2 - 2 * Real.cos Mu : ℝ) : ℂ) := by
    have h : Real.cos Mu = Real.cos (Real.pi * r ^ 2 - 2 * Real.pi) := by rw [hMu, hL]
    rw [sinSq_eq_two_sub_two_cos_sub r, h]
  set F : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hF
  have hargE : ∀ t : ℝ, Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    intro t
    congr 1
    rw [hL]; push_cast; ring
  have hF_eq : F = fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    funext t
    simp only [hF]
    rw [hargE t]
  set P : ℝ → ℂ := fun t => (G 0 0 τ + (t : ℂ) * Complex.I * G 0 1 τ)
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hP
  set Q : ℝ → ℂ := fun t => (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
      * Complex.exp (-(Mu : ℂ) * (t : ℂ)) with hQ
  have hAe_eq : ∀ t : ℝ, Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) = P t + Q t := by
    intro t
    have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hMu, hL]
      push_cast
      ring
    simp only [Aexp, hP, hQ]
    rw [add_mul, add_mul]
    rw [show (Complex.exp (2 * Real.pi * t) * (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ))
          * Complex.exp (-(L : ℂ) * (t : ℂ))
        = (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
      hexp]
  have hFint : IntegrableOn F (Set.Ioi 0) := by rw [hF]; exact hInt
  have hFint1 : IntegrableOn F (Set.Ioi 1) := hFint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hFint01 : IntegrableOn F (Set.Ioc 0 1) := hFint.mono_set Set.Ioc_subset_Ioi_self
  -- integrability of the tail `K - A`
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) :=
    measurable_Kaxis_Kfun ℓ d hd τ
  have hmeasA : Measurable (fun t : ℝ => Aexp G τ t) := by unfold Aexp; fun_prop
  have hmeasE : Measurable (fun t : ℝ => Complex.exp (-(L : ℂ) * (t : ℂ))) := by fun_prop
  have hdom : IntegrableOn (fun t : ℝ => C * (Work.Kernels.scale τ) ^ N
      * (t ^ M * Real.exp (-((Real.pi + L) * t)))) (Set.Ici (1 : ℝ)) :=
    integrableOn_const_mul_real
      ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
        (integrableOn_rpow_mul_exp_neg_mul_Ioi M (Real.pi + L) (by linarith)))
      (C * (Work.Kernels.scale τ) ^ N)
  have hDiffIntIci : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ici (1 : ℝ)) := by
    refine Integrable.mono' hdom ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable ?_
    filter_upwards [hAe τ hτ] with t ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(L : ℂ) * (t : ℂ)).re = -(L * t) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      ring
    rw [hre]
    refine (mul_le_mul_of_nonneg_right ht (Real.exp_nonneg _)).trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.exp_add,
      show -(Real.pi * t) + -(L * t) = -((Real.pi + L) * t) by ring]
    ring
  have hDiffInt : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ)) :=
    IntegrableOn.congr_set_ae hDiffIntIci (Ioi_ae_eq_Ici' (by simp : volume ({(1 : ℝ)} : Set ℝ) = 0))
  have hAeInt : IntegrableOn (fun t : ℝ => Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
      (Set.Ioi 1) := by
    have h1 : IntegrableOn (fun t : ℝ => F t - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi 1) :=
      Integrable.sub hFint1 hDiffInt
    refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
    rw [hF_eq]
    ring
  -- the two moment integrals
  have hPint : IntegrableOn P (Set.Ioi 1) := by
    rw [hP]
    exact integrableOn_affine_mul_exp_neg_mul_complex L hLpos (G 0 0 τ) (G 0 1 τ)
  have hPval : ∫ t in Set.Ioi (1 : ℝ), P t
      = G 0 0 τ * (Complex.exp (-(L : ℂ)) / (L : ℂ))
        + (Complex.I * G 0 1 τ)
          * (Complex.exp (-(L : ℂ)) * ((L : ℂ) + 1) / (L : ℂ) ^ 2) := by
    rw [hP]
    exact integral_affine_mul_exp_neg_mul_Ioi_one hLpos (G 0 0 τ) (G 0 1 τ)
  have hmain : sinSq r * (∫ t in Set.Ioi (1 : ℝ),
        Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))) = highPart G τ r := by
    by_cases hMu_pos : 0 < Mu
    · have hQint : IntegrableOn Q (Set.Ioi 1) := by
        rw [hQ]
        exact integrableOn_affine_mul_exp_neg_mul_complex Mu hMu_pos (G 1 0 τ) (G 1 1 τ)
      have hQval : ∫ t in Set.Ioi (1 : ℝ), Q t
          = G 1 0 τ * (Complex.exp (-(Mu : ℂ)) / (Mu : ℂ))
            + (Complex.I * G 1 1 τ)
              * (Complex.exp (-(Mu : ℂ)) * ((Mu : ℂ) + 1) / (Mu : ℂ) ^ 2) := by
        rw [hQ]
        exact integral_affine_mul_exp_neg_mul_Ioi_one hMu_pos (G 1 0 τ) (G 1 1 τ)
      have hAeval : ∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = (∫ t in Set.Ioi (1 : ℝ), P t) + ∫ t in Set.Ioi (1 : ℝ), Q t := by
        rw [← integral_add hPint hQint]
        exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => hAe_eq t)
      rw [hAeval, hPval, hQval, mul_add,
        sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ))) (G 0 0 τ) (Complex.I * G 0 1 τ),
        sinSq_mul_closed hMu_pos.ne' hcosMu (Complex.exp (-(Mu : ℂ))) (G 1 0 τ)
          (Complex.I * G 1 1 τ),
        highPart_eq_closed, hMu, hL]
      ring
    · have hMu_nonpos : Mu ≤ 0 := not_lt.mp hMu_pos
      have hQint : IntegrableOn Q (Set.Ioi 1) := by
        have h1 : IntegrableOn (fun t : ℝ =>
            Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) - P t) (Set.Ioi 1) :=
          Integrable.sub hAeInt hPint
        refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
        rw [hAe_eq t]
        ring
      have hG10 : G 1 0 τ = 0 ∧ G 1 1 τ = 0 :=
        eq_zero_of_integrableOn_affine_mul_exp_neg hMu_nonpos hQint
      have hAevalP : ∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = ∫ t in Set.Ioi (1 : ℝ), P t := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        rw [hAe_eq t, hQ, hG10.1, hG10.2]
        ring
      rw [hAevalP, hPval,
        sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ))) (G 0 0 τ) (Complex.I * G 0 1 τ),
        highPart_eq_closed, hG10.1, hG10.2, hL]
      ring
  -- the telescoping
  have hsplit0 : ∫ t in Set.Ioi (0 : ℝ), F t
      = (∫ t in (0 : ℝ)..1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t := by
    have hunion : ∫ t in Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ), F t
        = (∫ t in Set.Ioc (0 : ℝ) 1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t :=
      setIntegral_union (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2)))
        measurableSet_Ioi hFint01 hFint1
    have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h3)
        · exact h1
        · exact lt_trans zero_lt_one h3
      · intro h1
        by_cases h2 : x ≤ 1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (lt_of_not_ge h2)
    rw [hset] at hunion
    rw [hunion, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsplit1 : ∫ t in Set.Ioi (1 : ℝ), F t
      = (∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
        + ∫ t in Set.Ioi (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    rw [← integral_add hAeInt hDiffInt]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [hF_eq]; ring)
  have htruncIoi : ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))
      = ∫ t in Set.Ioi (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) :=
    setIntegral_congr_set (Ioi_ae_eq_Ici' (by simp : volume ({(1 : ℝ)} : Set ℝ) = 0)).symm
  have hlow : layerLow ℓ d τ r = sinSq r * ∫ t in (0 : ℝ)..1, F t := by
    rw [layerLow, hF]
  have htrunc : layerTrunc G ℓ d τ r
      = sinSq r * ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    rw [layerTrunc]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ici (fun t _ => by rw [hargE t])
  rw [show Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r
      = sinSq r * ∫ t in Set.Ioi (0 : ℝ), F t from by
        rw [Work.Kernels.kernelTransform, sinSq, hF]]
  rw [paperLayer, hlow, htrunc, htruncIoi, ← hmain, hsplit0, hsplit1]
  ring

end Work.Asymptotics
