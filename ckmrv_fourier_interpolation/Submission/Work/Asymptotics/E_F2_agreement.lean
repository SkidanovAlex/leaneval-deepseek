import Mathlib
import Submission.Work.Asymptotics.E_TailClosed
import Submission.Work.Asymptotics.paperLayer_eq_kernelTransform

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane Work.Kernels
open scoped Topology

namespace Work.Asymptotics

/-! ## Moment integrals on `(B,∞)`

The closed form of `∫_B^∞ A(τ,it) e^{-πr²t} dt` needs the two moment integrals
`∫_B^∞ e^{-ct}dt = e^{-cB}/c` and `∫_B^∞ t e^{-ct}dt = e^{-cB}(cB+1)/c²` at a general threshold
`B ≥ 1` (the `B = 1` case is in `Work.Asymptotics.paperLayer_agreement`). -/

/-- `e^{-cy} → 0` as `y → +∞`. -/
lemma E_F2_tendsto_exp_neg (c : ℝ) (hc : 0 < c) :
    Tendsto (fun y : ℝ => Complex.exp (-(c : ℂ) * (y : ℂ))) atTop (𝓝 0) := by
  have hreal : Tendsto (fun y : ℝ => Real.exp (-(c * y))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => -(c * y)) atTop Filter.atBot :=
      (Tendsto.const_mul_atTop_of_neg (show -c < 0 by linarith) tendsto_id).congr'
        (Eventually.of_forall (fun y => by simp))
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h1
  have h1 : Tendsto (fun y : ℝ => ((Real.exp (-(c * y)) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hreal
  simpa [exp_neg_mul_ofReal, Complex.ofReal_zero] using h1

/-- `y e^{-cy} → 0` as `y → +∞`. -/
lemma E_F2_tendsto_id_mul_exp_neg (c : ℝ) (hc : 0 < c) :
    Tendsto (fun y : ℝ => (y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ))) atTop (𝓝 0) := by
  have hreal : Tendsto (fun y : ℝ => y * Real.exp (-(c * y))) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
    simpa [Real.rpow_one] using h
  have h1 : Tendsto (fun y : ℝ => ((y * Real.exp (-(c * y)) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hreal
  simpa [Complex.ofReal_mul, exp_neg_mul_ofReal, Complex.ofReal_zero] using h1

/-- `∫_B^∞ e^{-ct} dt = e^{-cB}/c` for `c > 0`. -/
lemma E_F2_integral_exp_neg_mul_Ioi {c B : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi B, Complex.exp (-(c : ℂ) * (t : ℂ))
      = Complex.exp (-(c : ℂ) * (B : ℂ)) / (c : ℂ) := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hderiv : ∀ x ∈ Set.Ici B, HasDerivAt (fun y : ℝ => -(Complex.exp (-(c : ℂ) * (y : ℂ))) / (c : ℂ))
      (Complex.exp (-(c : ℂ) * (x : ℂ))) x := by
    intro x _
    have h := ((hasDerivAt_exp_neg_mul c x).neg).div_const (c : ℂ)
    refine h.congr_deriv ?_
    field_simp
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) := by
    refine Integrable.mono' (exp_neg_integrableOn_Ioi B hc) ?_ ?_
    · exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      rw [Complex.norm_exp]
      simp
  have htend : Tendsto (fun y : ℝ => -(Complex.exp (-(c : ℂ) * (y : ℂ))) / (c : ℂ)) atTop (𝓝 0) := by
    simpa using (E_F2_tendsto_exp_neg c hc).neg.div_const (c : ℂ)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [h]
  ring

/-- `∫_B^∞ t e^{-ct} dt = e^{-cB}(cB+1)/c²` for `c > 0`, `B ≥ 1`. -/
lemma E_F2_integral_id_mul_exp_neg_mul_Ioi {c B : ℝ} (hc : 0 < c) (hB : 1 ≤ B) :
    ∫ t in Set.Ioi B, (t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))
      = Complex.exp (-(c : ℂ) * (B : ℂ)) * ((c : ℂ) * (B : ℂ) + 1) / (c : ℂ) ^ 2 := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hderiv : ∀ x ∈ Set.Ici B, HasDerivAt (fun y : ℝ => -(((y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2)
      * Complex.exp (-(c : ℂ) * (y : ℂ)))) ((x : ℂ) * Complex.exp (-(c : ℂ) * (x : ℂ))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2) ((1 : ℂ) / (c : ℂ)) x := by
      simpa using ((HasDerivAt.ofReal_comp (hasDerivAt_id x)).div_const (c : ℂ)).add_const
        (1 / (c : ℂ) ^ 2)
    have h2 := hasDerivAt_exp_neg_mul c x
    have h := (h1.mul h2).neg
    refine h.congr_deriv ?_
    field_simp
    ring
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    (integrableOn_id_mul_exp_neg_mul_complex c hc).mono_set (Set.Ioi_subset_Ioi hB)
  have htend : Tendsto (fun y : ℝ => -(((y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2)
      * Complex.exp (-(c : ℂ) * (y : ℂ)))) atTop (𝓝 0) := by
    have h2 : (fun y : ℝ => -(((y : ℂ) / (c : ℂ) + 1 / (c : ℂ) ^ 2) * Complex.exp (-(c : ℂ) * (y : ℂ))))
        = fun y : ℝ => -((1 / (c : ℂ)) * ((y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ))))
            - (1 / (c : ℂ) ^ 2) * Complex.exp (-(c : ℂ) * (y : ℂ)) := by
      funext y; ring
    rw [h2]
    have hA := ((E_F2_tendsto_id_mul_exp_neg c hc).const_mul (1 / (c : ℂ))).neg
    have hB' := (E_F2_tendsto_exp_neg c hc).const_mul (1 / (c : ℂ) ^ 2)
    simpa using hA.sub hB'
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [h]
  field_simp
  ring

/-- A non-zero affine function times a decaying exponential is integrable on `(B,∞)`, `B ≥ 1`. -/
lemma E_F2_integrableOn_affine_mul_exp_neg_mul_Ioi (c B : ℝ) (hc : 0 < c) (hB : 1 ≤ B) (a b : ℂ) :
    IntegrableOn (fun t : ℝ => (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(c : ℂ) * (t : ℂ)))
      (Set.Ioi B) := by
  have hE : IntegrableOn (fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    (integrableOn_exp_neg_mul_complex c hc).mono_set (Set.Ioi_subset_Ioi hB)
  have hI : IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    (integrableOn_id_mul_exp_neg_mul_complex c hc).mono_set (Set.Ioi_subset_Ioi hB)
  have h1 : IntegrableOn (fun t : ℝ => a * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    hE.const_mul a
  have h2 : IntegrableOn (fun t : ℝ => (Complex.I * b) * ((t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))))
      (Set.Ioi B) := hI.const_mul (Complex.I * b)
  refine IntegrableOn.congr_fun (h1.add h2) (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

/-- The affine moment integral `∫_B^∞ (a + i b t) e^{-ct} dt`. -/
lemma E_F2_integral_affine_mul_exp_neg_mul_Ioi {c B : ℝ} (hc : 0 < c) (hB : 1 ≤ B) (a b : ℂ) :
    ∫ t in Set.Ioi B, (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(c : ℂ) * (t : ℂ))
      = a * (Complex.exp (-(c : ℂ) * (B : ℂ)) / (c : ℂ))
        + (Complex.I * b) * (Complex.exp (-(c : ℂ) * (B : ℂ))
            * (((c : ℂ) * (B : ℂ) + 1)) / (c : ℂ) ^ 2) := by
  have hE : IntegrableOn (fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    (integrableOn_exp_neg_mul_complex c hc).mono_set (Set.Ioi_subset_Ioi hB)
  have hI : IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    (integrableOn_id_mul_exp_neg_mul_complex c hc).mono_set (Set.Ioi_subset_Ioi hB)
  have h1 : IntegrableOn (fun t : ℝ => a * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    hE.const_mul a
  have h2 : IntegrableOn (fun t : ℝ => (Complex.I * b) * ((t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))))
      (Set.Ioi B) := hI.const_mul (Complex.I * b)
  rw [show (∫ t in Set.Ioi B, (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(c : ℂ) * (t : ℂ)))
      = ∫ t in Set.Ioi B, (a * Complex.exp (-(c : ℂ) * (t : ℂ))
          + (Complex.I * b) * ((t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ)))) from
      setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)]
  rw [integral_add h1 h2, integral_const_mul, E_F2_integral_exp_neg_mul_Ioi hc,
    integral_const_mul, E_F2_integral_id_mul_exp_neg_mul_Ioi hc hB]

/-- The regularisation of the two poles of the moment integrals at `c = 0`, for a general
exponential factor `E` and affine factor `D`: `(2 - 2cos c)·(a E/c + b E D/c²)
= c ψ(c) E a + ψ(c) D E b`. -/
lemma E_F2_sinSq_mul_closed {r c : ℝ} (hc : c ≠ 0)
    (hcos : sinSq r = ((2 - 2 * Real.cos c : ℝ) : ℂ)) (E D a b : ℂ) :
    sinSq r * (a * (E / (c : ℂ)) + b * (E * D / (c : ℂ) ^ 2))
      = (c : ℂ) * (psi1 c : ℂ) * E * a + (psi1 c : ℂ) * D * E * b := by
  have h2 : ((2 - 2 * Real.cos c : ℝ) : ℂ) = (c : ℂ) ^ 2 * (psi1 c : ℂ) := by
    rw [← sq_mul_psi1 c]; push_cast; ring
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hA : ((2 - 2 * Real.cos c : ℝ) : ℂ) * (E / (c : ℂ)) = (c : ℂ) * (psi1 c : ℂ) * E := by
    rw [h2]; field_simp
  have hB : ((2 - 2 * Real.cos c : ℝ) : ℂ) * (E * D / (c : ℂ) ^ 2) = (psi1 c : ℂ) * D * E := by
    rw [h2]; field_simp
  rw [hcos, mul_add,
    show ((2 - 2 * Real.cos c : ℝ) : ℂ) * (a * (E / (c : ℂ)))
        = a * (((2 - 2 * Real.cos c : ℝ) : ℂ) * (E / (c : ℂ))) by ring,
    hA,
    show ((2 - 2 * Real.cos c : ℝ) : ℂ) * (b * (E * D / (c : ℂ) ^ 2))
        = b * (((2 - 2 * Real.cos c : ℝ) : ℂ) * (E * D / (c : ℂ) ^ 2)) by ring,
    hB]
  ring

/-- If `d ≤ 0`, a non-zero affine function of `t` times `e^{-d t}` is not integrable on
`(T,∞)` for any threshold `T`: the exponential does not decay and the affine factor stays away
from `0`.  This is `Work.Asymptotics.eq_zero_of_integrableOn_affine_mul_exp_neg` with the
threshold `1` replaced by an arbitrary `T`. -/
lemma E_F2_eq_zero_of_integrableOn_affine_mul_exp_neg_Ioi {d T : ℝ} (hd : d ≤ 0) {a b : ℂ}
    (h : IntegrableOn (fun t : ℝ =>
      (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(d : ℂ) * (t : ℂ))) (Set.Ioi T)) :
    a = 0 ∧ b = 0 := by
  by_contra hcon
  obtain ⟨T₀, ε, hε, hT⟩ : ∃ T₀ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, T₀ ≤ t → ε ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
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
  set T' : ℝ := max (max T₀ 1) T with hT'def
  have hT'1 : (1 : ℝ) ≤ T' := le_trans (le_max_right T₀ 1) (le_max_left _ T)
  have hT'T₀ : T₀ ≤ T' := le_trans (le_max_left T₀ 1) (le_max_left _ T)
  have hT'T : T ≤ T' := le_max_right _ T
  have hpoint : ∀ t ∈ Set.Ioi T', ε * Real.exp (-d * t) ≤
      ‖(a + (t : ℂ) * Complex.I * b) * Complex.exp (-(d : ℂ) * (t : ℂ))‖ := by
    intro t ht
    have htT : T₀ ≤ t := le_trans hT'T₀ (le_of_lt (Set.mem_Ioi.mp ht))
    have ht0 : 0 ≤ t := by have := Set.mem_Ioi.mp ht; linarith
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(d : ℂ) * (t : ℂ)).re = -d * t := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hT t htT) (Real.exp_nonneg _)
  have hint1 : IntegrableOn (fun t : ℝ => ε * Real.exp (-d * t)) (Set.Ioi T') := by
    refine Integrable.mono' (h.mono_set (Set.Ioi_subset_Ioi hT'T)).norm ?_ ?_
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


/-- **The closed form of the tail integral at a general threshold `B`.**
For `B ≥ 1` and `r ≠ 0`, if the tail `t ↦ A(τ,it)e^{-πr²t}` is integrable on `(B,∞)` then its
integral is the explicit closed form `E_TailClosed G B w r`. -/
lemma E_F2_E_TailClosed_eq_integral (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (B : ℝ)
    (w : UpperHalfPlane) (r : ℝ) (hB : 1 ≤ B) (hr : r ≠ 0)
    (hint : IntegrableOn (fun t : ℝ => Aexp G w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi B)) :
    E_TailClosed G B w r = sinSq r * ∫ t in Set.Ioi B, Aexp G w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  set L : ℝ := Real.pi * r ^ 2 with hL
  set Mu : ℝ := L - 2 * Real.pi with hMu
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLne : L ≠ 0 := hLpos.ne'
  have hcosL : sinSq r = ((2 - 2 * Real.cos L : ℝ) : ℂ) := by
    rw [sinSq_eq_two_sub_two_cos r, hL]
  have hcosMu : sinSq r = ((2 - 2 * Real.cos Mu : ℝ) : ℂ) := by
    have h : Real.cos Mu = Real.cos (Real.pi * r ^ 2 - 2 * Real.pi) := by rw [hMu, hL]
    rw [sinSq_eq_two_sub_two_cos_sub r, h]
  have hargE : ∀ t : ℝ, Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    intro t; congr 1; rw [hL]; push_cast; ring
  have hint' : IntegrableOn (fun t : ℝ => Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ)))
      (Set.Ioi B) := by
    refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show Aexp G w t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ))
    rw [hargE t]
  set P : ℝ → ℂ := fun t => (G 0 0 w + (t : ℂ) * Complex.I * G 0 1 w)
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hP
  set Q : ℝ → ℂ := fun t => (G 1 0 w + (t : ℂ) * Complex.I * G 1 1 w)
      * Complex.exp (-(Mu : ℂ) * (t : ℂ)) with hQ
  have hAe_eq : ∀ t : ℝ, Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ)) = P t + Q t := by
    intro t
    have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; rw [hMu, hL]; push_cast; ring
    simp only [Aexp, hP, hQ]
    rw [add_mul, add_mul]
    rw [show (Complex.exp (2 * Real.pi * t) * (G 1 0 w + (t : ℂ) * Complex.I * G 1 1 w))
          * Complex.exp (-(L : ℂ) * (t : ℂ))
        = (G 1 0 w + (t : ℂ) * Complex.I * G 1 1 w)
          * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
      hexp]
  have hPint : IntegrableOn P (Set.Ioi B) := by
    rw [hP]
    exact E_F2_integrableOn_affine_mul_exp_neg_mul_Ioi L B hLpos hB (G 0 0 w) (G 0 1 w)
  have hPval : ∫ t in Set.Ioi B, P t
      = G 0 0 w * (Complex.exp (-(L : ℂ) * (B : ℂ)) / (L : ℂ))
        + (Complex.I * G 0 1 w) * (Complex.exp (-(L : ℂ) * (B : ℂ))
            * (((L : ℂ) * (B : ℂ) + 1)) / (L : ℂ) ^ 2) := by
    rw [hP]
    exact E_F2_integral_affine_mul_exp_neg_mul_Ioi (c := L) (B := B) hLpos hB (G 0 0 w) (G 0 1 w)
  have hL' : L = Real.pi * r ^ 2 := hL
  have hMu' : Mu = Real.pi * r ^ 2 - 2 * Real.pi := by rw [hMu, hL]
  have hmainL : E_TailClosed G B w r
      = sinSq r * ∫ t in Set.Ioi B, Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    by_cases hMu_pos : 0 < Mu
    · have hQint : IntegrableOn Q (Set.Ioi B) := by
        rw [hQ]
        exact E_F2_integrableOn_affine_mul_exp_neg_mul_Ioi Mu B hMu_pos hB (G 1 0 w) (G 1 1 w)
      have hQval : ∫ t in Set.Ioi B, Q t
          = G 1 0 w * (Complex.exp (-(Mu : ℂ) * (B : ℂ)) / (Mu : ℂ))
            + (Complex.I * G 1 1 w) * (Complex.exp (-(Mu : ℂ) * (B : ℂ))
                * (((Mu : ℂ) * (B : ℂ) + 1)) / (Mu : ℂ) ^ 2) := by
        rw [hQ]
        exact E_F2_integral_affine_mul_exp_neg_mul_Ioi (c := Mu) (B := B) hMu_pos hB (G 1 0 w) (G 1 1 w)
      have hAeval : ∫ t in Set.Ioi B, Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = (∫ t in Set.Ioi B, P t) + ∫ t in Set.Ioi B, Q t := by
        rw [← integral_add hPint hQint]
        exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => hAe_eq t)
      rw [hAeval, hPval, hQval, mul_add,
        E_F2_sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ) * (B : ℂ)))
          (((L : ℂ) * (B : ℂ) + 1)) (G 0 0 w) (Complex.I * G 0 1 w),
        E_F2_sinSq_mul_closed hMu_pos.ne' hcosMu (Complex.exp (-(Mu : ℂ) * (B : ℂ)))
          (((Mu : ℂ) * (B : ℂ) + 1)) (G 1 0 w) (Complex.I * G 1 1 w)]
      rw [E_TailClosed, tcLambda]
      simp only [psiC]
      rw [hMu', hL']
      ring_nf
    · have hMu_nonpos : Mu ≤ 0 := not_lt.mp hMu_pos
      have hQint : IntegrableOn Q (Set.Ioi B) := by
        have h1 : IntegrableOn (fun t : ℝ => Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ)) - P t)
            (Set.Ioi B) := Integrable.sub hint' hPint
        refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
        rw [hAe_eq t]; ring
      have hG10 : G 1 0 w = 0 ∧ G 1 1 w = 0 :=
        E_F2_eq_zero_of_integrableOn_affine_mul_exp_neg_Ioi hMu_nonpos hQint
      have hAevalP : ∫ t in Set.Ioi B, Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = ∫ t in Set.Ioi B, P t := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        rw [hAe_eq t, hQ, hG10.1, hG10.2]; ring
      rw [hAevalP, hPval,
        E_F2_sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ) * (B : ℂ)))
          (((L : ℂ) * (B : ℂ) + 1)) (G 0 0 w) (Complex.I * G 0 1 w)]
      rw [E_TailClosed, tcLambda]
      simp only [psiC]
      rw [hL', hG10.1, hG10.2]
      ring_nf
  have hIntEq : (∫ t in Set.Ioi B, Aexp G w t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = ∫ t in Set.Ioi B, Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show Aexp G w t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ))
    rw [hargE t]
  rw [hmainL, hIntEq]


/-- The closed form of the tail integral at the threshold `B`, over `[B,∞)` (the form in which
`E_TailT` presents the tail): this is `E_F2_E_TailClosed_eq_integral` together with the a.e.
identity `(B,∞) = [B,∞)`. -/
lemma E_F2_E_TailClosed_eq_integral_Ici (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (B : ℝ)
    (w : UpperHalfPlane) (r : ℝ) (hB : 1 ≤ B) (hr : r ≠ 0)
    (hint : IntegrableOn (fun t : ℝ => Aexp G w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici B)) :
    E_TailClosed G B w r = sinSq r * ∫ t in Set.Ici B, Aexp G w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  have hIoi : IntegrableOn (fun t : ℝ => Aexp G w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi B) :=
    hint.mono_set Set.Ioi_subset_Ici_self
  rw [E_F2_E_TailClosed_eq_integral G B w r hB hr hIoi]
  congr 1
  exact setIntegral_congr_set (Ioi_ae_eq_Ici' (by simp : volume ({(B : ℝ)} : Set ℝ) = 0))


/-- **The `trunc` piece at the threshold `B = (scale w)^{N₀}`.**  The layer `E_TailT` is
`sinSq r` times the contour integral of the piecewise kernel `K` below `B` and `K - Aexp`
above `B`; splitting `(1,∞) = (1,B) ∪ [B,∞)` this is `sinSq r` times
`∫_1^∞ K e^{-πr²t} - ∫_B^∞ A e^{-πr²t}`. -/
lemma E_F2_E_TailT_eq (ℓ : LogLambdaData) (d : ℕ) (N₀ : ℝ) (w : UpperHalfPlane) (r : ℝ)
    (hB : 1 ≤ (scale w) ^ N₀)
    (hF : IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) w t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1))
    (hG : IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) w t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici ((scale w) ^ N₀))) :
    E_TailT ℓ d N₀ w r = sinSq r *
      ((∫ t in Set.Ici 1, Kaxis (Kfun ℓ d) w t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        - ∫ t in Set.Ici ((scale w) ^ N₀), Aexp (Gcusp ℓ d) w t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
  rw [E_TailT, tailIntegral]
  rw [show E_Bw N₀ w = (scale w) ^ N₀ from rfl]
  set B : ℝ := (scale w) ^ N₀ with hBdef
  have hB' : 1 ≤ B := by rw [hBdef]; exact hB
  have hcx : ∀ t : ℝ, (Real.exp (-(Real.pi * r ^ 2 * t)) : ℂ)
      = Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    rw [← exp_neg_mul_ofReal (Real.pi * r ^ 2) t]
    congr 1
    push_cast
    ring
  set F : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hFdef
  set G : ℝ → ℂ := fun t => Aexp (Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hGdef
  set g : ℝ → ℂ := fun t => (if t < B then Kaxis (Kfun ℓ d) w t
      else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)
        * (Real.exp (-(Real.pi * r ^ 2 * t)) : ℂ) with hgdef
  have hFint1 : IntegrableOn F (Set.Ici 1) := by rw [hFdef]; exact hF
  have hFintIco : IntegrableOn F (Set.Ico 1 B) := hFint1.mono_set (fun t ht => ht.1)
  have hFintB : IntegrableOn F (Set.Ici B) :=
    hFint1.mono_set (fun t ht => le_trans hB' (Set.mem_Ici.mp ht))
  have hGintB : IntegrableOn G (Set.Ici B) := by rw [hBdef, hGdef]; exact hG
  have hFGB : IntegrableOn (fun t => F t - G t) (Set.Ici B) := hFintB.sub hGintB
  have hgIco : IntegrableOn g (Set.Ico 1 B) := by
    refine hFintIco.congr_fun (fun t ht => ?_) measurableSet_Ico
    simp only [hFdef, hgdef]
    rw [if_pos ht.2, hcx t]
  have hgIci : IntegrableOn g (Set.Ici B) := by
    refine hFGB.congr_fun (fun t ht => ?_) measurableSet_Ici
    simp only [hFdef, hGdef, hgdef]
    rw [if_neg (not_lt.mpr (Set.mem_Ici.mp ht)), hcx t]
    ring
  have hdisj : Disjoint (Set.Ico (1 : ℝ) B) (Set.Ici B) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_lt.mpr hx2))
  have hset : Set.Ico (1 : ℝ) B ∪ Set.Ici B = Set.Ici 1 := by
    ext t; constructor
    · rintro (⟨h1, _⟩ | h3)
      · exact Set.mem_Ici.mpr h1
      · exact Set.mem_Ici.mpr (le_trans hB' (Set.mem_Ici.mp h3))
    · intro ht
      have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
      rcases lt_or_ge t B with h | h
      · exact Or.inl ⟨ht1, h⟩
      · exact Or.inr (Set.mem_Ici.mpr h)
  have hsplitg : ∫ t in Set.Ici (1 : ℝ), g t
      = (∫ t in Set.Ico (1 : ℝ) B, g t) + ∫ t in Set.Ici B, g t := by
    have h := setIntegral_union hdisj measurableSet_Ici hgIco hgIci
    rw [hset] at h
    exact h
  have hsplitF : ∫ t in Set.Ici (1 : ℝ), F t
      = (∫ t in Set.Ico (1 : ℝ) B, F t) + ∫ t in Set.Ici B, F t := by
    have h := setIntegral_union hdisj measurableSet_Ici hFintIco hFintB
    rw [hset] at h
    exact h
  have hcongrIco : ∫ t in Set.Ico (1 : ℝ) B, g t = ∫ t in Set.Ico (1 : ℝ) B, F t := by
    refine setIntegral_congr_fun measurableSet_Ico (fun t ht => ?_)
    simp only [hFdef, hgdef]
    rw [if_pos ht.2, hcx t]
  have hcongrIci : ∫ t in Set.Ici B, g t = ∫ t in Set.Ici B, (F t - G t) := by
    refine setIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
    simp only [hFdef, hGdef, hgdef]
    rw [if_neg (not_lt.mpr (Set.mem_Ici.mp ht)), hcx t]
    ring
  have hsub : ∫ t in Set.Ici B, (F t - G t)
      = (∫ t in Set.Ici B, F t) - ∫ t in Set.Ici B, G t := integral_sub hFintB hGintB
  have hgoal : ∫ t in Set.Ici (1 : ℝ), g t = (∫ t in Set.Ici (1 : ℝ), F t)
      - ∫ t in Set.Ici B, G t := by
    rw [hsplitg, hcongrIco, hcongrIci, hsub, hsplitF]
    ring
  have hfin : sinSq r * (∫ t in Set.Ici (1 : ℝ), g t)
      = sinSq r * ((∫ t in Set.Ici 1, F t) - ∫ t in Set.Ici ((scale w) ^ N₀), G t) := by
    rw [hgoal, hBdef]
  simpa only [hgdef, hBdef] using hfin


theorem E_F2_agreement (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (N₀ C N M : ℝ) (hN₀ : 0 ≤ N₀) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → 0 < t →
      t ≤ (Work.Kernels.scale w) ^ N₀ →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
      (Work.Kernels.scale w) ^ N₀ ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t))) :
    ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.KEpsilon → r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      Work.Asymptotics.E_Expr ℓ d N₀ w r
        = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w r := by
  intro w r hw hr hInt
  set B : ℝ := (scale w) ^ N₀ with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; exact Real.one_le_rpow (one_le_scale w) hN₀
  set L : ℝ := Real.pi * r ^ 2 with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  set F : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hFdef
  set G : ℝ → ℂ := fun t => Aexp (Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hGdef
  have hFint0 : IntegrableOn F (Set.Ioi 0) := by rw [hFdef]; exact hInt
  have hFint1 : IntegrableOn F (Set.Ici 1) :=
    hFint0.mono_set (fun t ht => lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht))
  have hFintB : IntegrableOn F (Set.Ici B) :=
    hFint0.mono_set (fun t ht => lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hB1) (Set.mem_Ici.mp ht))
  have hFint01 : IntegrableOn F (Set.Ioc 0 1) := hFint0.mono_set Set.Ioc_subset_Ioi_self
  have hFintIoi1 : IntegrableOn F (Set.Ioi 1) := hFint0.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  -- integrability of the tail difference `(K - A)·e^{-πr²t}` on `[B,∞)`, from `htail`
  have hmeasK : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) := measurable_Kaxis_Kfun ℓ d hd w
  have hmeasA : Measurable (fun t : ℝ => Aexp (Gcusp ℓ d) w t) := by unfold Aexp; fun_prop
  have hmeasE : Measurable (fun t : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    fun_prop
  have hdom1 : IntegrableOn (fun t : ℝ => C * (scale w) ^ N * (t ^ M * Real.exp (-((Real.pi + L) * t))))
      (Set.Ici (1 : ℝ)) :=
    integrableOn_const_mul_real ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_rpow_mul_exp_neg_mul_Ioi M (Real.pi + L) (by linarith [Real.pi_pos])))
      (C * (scale w) ^ N)
  have hdomB : IntegrableOn (fun t : ℝ => C * (scale w) ^ N * (t ^ M * Real.exp (-((Real.pi + L) * t))))
      (Set.Ici B) := hdom1.mono_set (fun t ht => le_trans hB1 (Set.mem_Ici.mp ht))
  have hDiffInt : IntegrableOn (fun t : ℝ => (Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici B) := by
    refine Integrable.mono' hdomB ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have htB : B ≤ t := Set.mem_Ici.mp ht
    have htB' : (scale w) ^ N₀ ≤ t := by rw [← hBdef]; exact htB
    have hb := htail w t hw htB'
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))).re = -(L * t) := by
      rw [hL]
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, pow_two]
      ring
    rw [hre]
    calc ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖ * Real.exp (-(L * t))
        ≤ (C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t))) * Real.exp (-(L * t)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = C * (scale w) ^ N * (t ^ M * Real.exp (-((Real.pi + L) * t))) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add,
            show -(Real.pi * t) + -(L * t) = -((Real.pi + L) * t) by ring]
  have hGintB : IntegrableOn G (Set.Ici B) := by
    have h1 : IntegrableOn (fun t : ℝ => F t - (Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici B) := hFintB.sub hDiffInt
    refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ici
    simp only [hFdef, hGdef]
    ring
  -- the two auxiliary integrability statements in the exact forms the lemmas ask for
  have hF' : IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
    rw [← hFdef]; exact hFint1
  have hG' : IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici ((scale w) ^ N₀)) := by
    rw [← hBdef, ← hGdef]; exact hGintB
  have hG'' : IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici B) := by
    rw [← hGdef]; exact hGintB
  have hB' : 1 ≤ (scale w) ^ N₀ := by rw [← hBdef]; exact hB1
  -- the `trunc` piece
  have hTT : E_TailT ℓ d N₀ w r = sinSq r * ((∫ t in Set.Ici 1, F t) - ∫ t in Set.Ici B, G t) := by
    have h := E_F2_E_TailT_eq ℓ d N₀ w r hB' hF' hG'
    have h1 : (∫ t in Set.Ici 1, Kaxis (Kfun ℓ d) w t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) = ∫ t in Set.Ici 1, F t :=
      setIntegral_congr_fun measurableSet_Ici (fun t _ => by simp only [hFdef])
    have h2 : (∫ t in Set.Ici ((scale w) ^ N₀), Aexp (Gcusp ℓ d) w t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) = ∫ t in Set.Ici B, G t := by
      simp only [hBdef, hGdef]
    rw [h, h1, h2]
  -- the closed form of the tail
  have hTC : E_TailClosed (Gcusp ℓ d) B w r = sinSq r * ∫ t in Set.Ici B, G t := by
    have h := E_F2_E_TailClosed_eq_integral_Ici (G := Gcusp ℓ d) (B := B) (w := w) (r := r) hB1 hr hG''
    have h2 : (∫ t in Set.Ici B, Aexp (Gcusp ℓ d) w t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) = ∫ t in Set.Ici B, G t :=
      setIntegral_congr_fun measurableSet_Ici (fun t _ => by simp only [hGdef])
    rw [h, h2]
  -- the `low` piece
  have hlow : layerLow ℓ d w r = sinSq r * ∫ t in (0 : ℝ)..1, F t := by
    rw [layerLow]
  -- the kernel transform
  have hkernel : kernelTransform (Kfun ℓ d) w r = sinSq r * ∫ t in Set.Ioi 0, F t := by
    simp only [kernelTransform, sinSq, hFdef]
  -- the splitting of the full contour
  have hsplit0 : ∫ t in Set.Ioi (0 : ℝ), F t = (∫ t in (0 : ℝ)..1, F t) + ∫ t in Set.Ici 1, F t := by
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) :=
      Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2))
    have hunion : ∫ t in Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ), F t
        = (∫ t in Set.Ioc (0 : ℝ) 1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t :=
      setIntegral_union hdisj measurableSet_Ioi hFint01 hFintIoi1
    have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext x; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, _⟩ | h3)
        · exact h1
        · exact lt_trans zero_lt_one h3
      · intro h1
        by_cases h2 : x ≤ 1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (lt_of_not_ge h2)
    rw [hset] at hunion
    rw [hunion, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_congr_set (Ioi_ae_eq_Ici' (by simp : volume ({(1 : ℝ)} : Set ℝ) = 0))]
  have hEw : E_Bw N₀ w = B := by
    rw [show E_Bw N₀ w = (scale w) ^ N₀ from rfl, ← hBdef]
  rw [E_Expr, hEw, hlow, hTT, hTC, hkernel, hsplit0]
  ring


end Work.Asymptotics
