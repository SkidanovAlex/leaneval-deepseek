import Mathlib.Analysis.Fourier.AddCircle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open MeasureTheory intervalIntegral

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- The continuous, even (about `1`) extension of `f` from `[-1/2,1/2]` to `[0,2]`.
Concretely `hExt f u = f (min u (2-u) - 1/2)`, so on `[0,1]` it equals `f (u - 1/2)`. -/
def hExt (f : ℝ → ℝ) (u : ℝ) : ℝ := f (min u (2 - u) - 1 / 2)

lemma hExt_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (hExt f) := by
  unfold hExt
  exact hf.comp (by fun_prop)

lemma hExt_symm (f : ℝ → ℝ) (u : ℝ) : hExt f (2 - u) = hExt f u := by
  unfold hExt
  congr 1
  rw [show (2 : ℝ) - (2 - u) = u by ring, min_comm]

lemma hExt_eq_on (f : ℝ → ℝ) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    hExt f u = f (u - 1/2) := by
  unfold hExt
  congr 1
  rw [min_eq_left (by linarith [hu.2])]

lemma hExt_add_half {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Icc (-(1/2):ℝ) (1/2)) :
    hExt f (x + 1/2) = f x := by
  rw [hExt_eq_on f (show x + 1/2 ∈ Set.Icc (0:ℝ) 1 from
    ⟨by linarith [hx.1], by linarith [hx.2]⟩)]
  congr 1; ring

/-- `∫_{-1/2}^{1/2} f² = ∫_0^1 (hExt f)²`. -/
lemma integral_sq_eq {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in (-(1/2))..(1/2), (f x)^2) = ∫ u in 0..1, (hExt f u)^2 := by
  have h : (∫ x in (0:ℝ)..1, (f (x + -(1/2)))^2) = ∫ x in (-(1/2))..(1/2), (f x)^2 := by
    have := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 1)
      (fun y : ℝ => (f y)^2) (-(1/2))
    rw [show (0:ℝ) + -(1/2) = -(1/2) by norm_num,
        show (1:ℝ) + -(1/2) = 1/2 by norm_num] at this
    simpa using this
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
  simp only []
  rw [hExt_eq_on f hu]
  rw [show u + -(1/2) = u - 1/2 by ring]

/-- `∫_0^1 (hExt f)² = (1/2) ∫_0^2 (hExt f)²`, from the symmetry `hExt f (2-u) = hExt f u`. -/
lemma half_integral_eq {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ u in 0..1, (hExt f u)^2) = (1/2) * ∫ u in 0..2, (hExt f u)^2 := by
  have hcont : Continuous (fun u : ℝ => (hExt f u)^2) := (hExt_continuous hf).pow 2
  have hii1 : IntervalIntegrable (fun u : ℝ => (hExt f u)^2) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hii2 : IntervalIntegrable (fun u : ℝ => (hExt f u)^2) volume 1 2 :=
    hcont.intervalIntegrable 1 2
  have hadj : (∫ u in 0..1, (hExt f u)^2) + (∫ u in 1..2, (hExt f u)^2)
      = ∫ u in 0..2, (hExt f u)^2 :=
    intervalIntegral.integral_add_adjacent_intervals hii1 hii2
  have hsub : (∫ u in 1..2, (hExt f u)^2) = ∫ u in 0..1, (hExt f u)^2 := by
    have h : (∫ x in (1:ℝ)..2, (hExt f (2 - x))^2) = ∫ x in (0:ℝ)..1, (hExt f x)^2 := by
      have hh := intervalIntegral.integral_comp_sub_left (a := (1:ℝ)) (b := 2)
        (fun u : ℝ => (hExt f u)^2) 2
      rw [show (2:ℝ) - 2 = 0 by norm_num, show (2:ℝ) - 1 = 1 by norm_num] at hh
      exact hh
    have hcongr : (∫ x in 1..2, (hExt f (2 - x))^2) = ∫ x in 1..2, (hExt f x)^2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only []
      rw [hExt_symm]
    rw [hcongr] at h
    exact h
  rw [hsub] at hadj
  linarith [hadj]

/-- The complexified extension. -/
def hExtC (f : ℝ → ℝ) : ℝ → ℂ := fun u => (hExt f u : ℂ)

lemma hExtC_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (hExtC f) :=
  Complex.continuous_ofReal.comp (hExt_continuous hf)

/-- The `n`-th cosine coefficient of `f` on the interval (using the `u = x + 1/2` picture). -/
def cosCoeff (f : ℝ → ℝ) (n : ℤ) : ℝ :=
  ∫ u in 0..1, hExt f u * Real.cos ((n:ℝ) * Real.pi * u)

lemma cosCoeff_zero_eq {f : ℝ → ℝ} (hf : Continuous f) :
    cosCoeff f 0 = ∫ x in (-(1/2))..(1/2), f x := by
  unfold cosCoeff
  simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one]
  have hsub := intervalIntegral.integral_comp_add_right (a := (-(1/2):ℝ)) (b := 1/2)
        (fun u : ℝ => hExt f u) (1/2)
  rw [show (-(1/2):ℝ) + 1/2 = 0 by norm_num, show (1:ℝ)/2 + 1/2 = 1 by norm_num] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only []
  rw [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)] at hx
  rw [hExt_add_half hx]

lemma cosCoeff_succ_eq {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) :
    cosCoeff f ((k : ℤ) + 1)
      = ∫ x in (-(1/2))..(1/2), f x * Real.cos (((k : ℝ) + 1) * Real.pi * (x + 1/2)) := by
  unfold cosCoeff
  have hsub := intervalIntegral.integral_comp_add_right (a := (-(1/2):ℝ)) (b := 1/2)
        (fun u : ℝ => hExt f u * Real.cos ((((k:ℤ)+1 : ℤ) : ℝ) * Real.pi * u)) (1/2)
  rw [show (-(1/2):ℝ) + 1/2 = 0 by norm_num, show (1:ℝ)/2 + 1/2 = 1 by norm_num] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only []
  rw [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)] at hx
  rw [hExt_add_half hx]
  rw [show ((((k:ℤ)+1 : ℤ) : ℝ)) = (k:ℝ) + 1 by push_cast; ring]

lemma fourier_coe_two (n : ℤ) (u : ℝ) :
    fourier n (↑u : AddCircle (2:ℝ)) = Complex.exp ((n:ℂ) * ↑Real.pi * Complex.I * u) := by
  rw [fourier_coe_apply]; congr 1; push_cast; ring

lemma fourier_coe_two_neg (n : ℤ) (u : ℝ) :
    fourier (-n) (↑u : AddCircle (2:ℝ)) = Complex.exp (-((n:ℂ) * ↑Real.pi * Complex.I * u)) := by
  rw [fourier_coe_two]; congr 1; push_cast; ring

lemma fourier_coe_two_period (n : ℤ) (u : ℝ) :
    fourier (-n) (↑(2 - u) : AddCircle (2:ℝ)) = fourier n (↑u : AddCircle (2:ℝ)) := by
  rw [fourier_coe_two_neg, fourier_coe_two]
  have hpow : -((n:ℂ) * ↑Real.pi * Complex.I * ↑(2 - u : ℝ))
      = (n:ℂ) * ↑Real.pi * Complex.I * ↑u + ((↑(-n) : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
    push_cast; ring
  rw [hpow, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma fourier_coe_two_add (n : ℤ) (u : ℝ) :
    fourier (-n) (↑u : AddCircle (2:ℝ)) + fourier n (↑u : AddCircle (2:ℝ))
      = 2 * ↑(Real.cos ((n:ℝ) * Real.pi * u)) := by
  rw [fourier_coe_two_neg, fourier_coe_two]
  set x : ℝ := (n:ℝ) * Real.pi * u with hx
  have h1 : (n:ℂ) * ↑Real.pi * Complex.I * u = ↑x * Complex.I := by
    rw [hx]; push_cast; ring
  rw [h1]
  have he : Complex.exp (-(↑x * Complex.I))
      = ↑(Real.cos x) - ↑(Real.sin x) * Complex.I := by
    have h := Complex.exp_ofReal_mul_I (-x)
    rw [show (↑(-x) : ℂ) * Complex.I = -(↑x * Complex.I) by push_cast; ring] at h
    rw [h, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  rw [he, Complex.exp_ofReal_mul_I]
  push_cast
  ring

lemma integral_phi {f : ℝ → ℝ} (hf : Continuous f) (n : ℤ) :
    (∫ u in (0:ℝ)..2, fourier (-n) (↑u : AddCircle (2:ℝ)) * (hExt f u : ℂ))
      = 2 * (cosCoeff f n : ℂ) := by
  set φ : ℝ → ℂ := fun u => fourier (-n) (↑u : AddCircle (2:ℝ)) * (hExt f u : ℂ) with hφ
  have hcontφ : Continuous φ := by
    rw [hφ]
    rw [show (fun u : ℝ => fourier (-n) (↑u : AddCircle (2:ℝ)) * (hExt f u : ℂ))
        = fun u : ℝ => Complex.exp (-((n:ℂ) * ↑Real.pi * Complex.I * ↑u)) * (hExt f u : ℂ) from by
          funext u; rw [fourier_coe_two_neg]]
    apply Continuous.mul
    · fun_prop
    · exact Complex.continuous_ofReal.comp (hExt_continuous hf)
  have h01φ : IntervalIntegrable φ volume (0:ℝ) 1 := hcontφ.intervalIntegrable 0 1
  have h12φ : IntervalIntegrable φ volume (1:ℝ) 2 := hcontφ.intervalIntegrable 1 2
  have hsplit : (∫ u in (0:ℝ)..2, φ u)
      = (∫ u in (0:ℝ)..1, φ u) + (∫ u in (1:ℝ)..2, φ u) :=
    (intervalIntegral.integral_add_adjacent_intervals h01φ h12φ).symm
  have hsub : (∫ u in (1:ℝ)..2, φ u) = ∫ v in (0:ℝ)..1, φ (2 - v) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1) φ 2
    rw [show (2:ℝ) - 1 = 1 by norm_num, show (2:ℝ) - 0 = 2 by norm_num] at h
    exact h.symm
  have hφ2 : ∀ v : ℝ, φ (2 - v) = fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ) := by
    intro v
    rw [hφ]; simp only []
    rw [fourier_coe_two_period, hExt_symm]
  have hsub2 : (∫ u in (1:ℝ)..2, φ u)
      = ∫ v in (0:ℝ)..1, fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ) := by
    rw [hsub]
    apply intervalIntegral.integral_congr
    intro v hv; simp only []; exact hφ2 v
  have hcontg : Continuous (fun v : ℝ => fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ)) := by
    rw [show (fun v : ℝ => fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ))
        = fun v : ℝ => Complex.exp ((n:ℂ) * ↑Real.pi * Complex.I * ↑v) * (hExt f v : ℂ) from by
          funext v; rw [fourier_coe_two]]
    apply Continuous.mul
    · fun_prop
    · exact Complex.continuous_ofReal.comp (hExt_continuous hf)
  have h01g : IntervalIntegrable (fun v : ℝ => fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ))
      volume (0:ℝ) 1 := hcontg.intervalIntegrable 0 1
  have hcombine : (∫ u in (0:ℝ)..1, φ u)
      + (∫ v in (0:ℝ)..1, fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ))
      = ∫ v in (0:ℝ)..1, (φ v + fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ)) :=
    (intervalIntegral.integral_add h01φ h01g).symm
  have hpt : ∀ v : ℝ, φ v + fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ)
      = 2 * ↑(Real.cos ((n:ℝ) * Real.pi * v)) * (hExt f v : ℂ) := by
    intro v
    rw [hφ]; simp only []
    rw [← add_mul, fourier_coe_two_add]
  have hcos : (∫ v in (0:ℝ)..1, 2 * ↑(Real.cos ((n:ℝ) * Real.pi * v)) * (hExt f v : ℂ))
      = 2 * (cosCoeff f n : ℂ) := by
    rw [show (fun v : ℝ => 2 * ↑(Real.cos ((n:ℝ) * Real.pi * v)) * (hExt f v : ℂ))
        = fun v => 2 * ((hExt f v : ℂ) * ↑(Real.cos ((n:ℝ) * Real.pi * v))) from by
          funext v; ring]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [show (fun v : ℝ => (hExt f v : ℂ) * ↑(Real.cos ((n:ℝ) * Real.pi * v)))
        = fun v => ↑(hExt f v * Real.cos ((n:ℝ) * Real.pi * v)) from by
          funext v; push_cast; ring]
    rw [intervalIntegral.integral_ofReal]
    rfl
  rw [hsplit, hsub2, hcombine]
  rw [show (∫ v in (0:ℝ)..1, (φ v + fourier n (↑v : AddCircle (2:ℝ)) * (hExt f v : ℂ)))
      = ∫ v in (0:ℝ)..1, 2 * ↑(Real.cos ((n:ℝ) * Real.pi * v)) * (hExt f v : ℂ) from by
        apply intervalIntegral.integral_congr
        intro v hv; exact hpt v]
  exact hcos

lemma fourierCoeffOn_hExt_eq {f : ℝ → ℝ} (hf : Continuous f) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0:ℝ) < 2) (fun u => (hExt f u : ℂ)) n
      = (cosCoeff f n : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  rw [show (2:ℝ) - 0 = 2 by norm_num]
  simp only [smul_eq_mul]
  rw [Complex.real_smul]
  have hIgoal : (∫ x : ℝ in (0:ℝ)..2, fourier (-n) (↑x : AddCircle (2:ℝ)) * (hExt f x : ℂ))
      = 2 * (cosCoeff f n : ℂ) := integral_phi hf n
  have hfin : (↑(1/2 : ℝ) : ℂ) * (∫ x : ℝ in (0:ℝ)..2, fourier (-n) (↑x : AddCircle (2:ℝ)) * (hExt f x : ℂ))
      = ↑(cosCoeff f n) := by
    rw [hIgoal]
    rw [show (↑(1/2 : ℝ) : ℂ) = 1/2 by norm_num]
    ring
  exact hfin

lemma memLp_continuous_Ioc {F : ℝ → ℂ} (hF : Continuous F) (a b : ℝ) :
    MemLp F 2 (volume.restrict (Set.Ioc a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  refine MemLp.of_bound hF.aestronglyMeasurable (max C 0) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact le_trans (hC x (Set.Ioc_subset_Icc_self hx)) (le_max_left _ _)

theorem cos_basis_parseval {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in (-(1 / 2))..(1 / 2), (f x) ^ 2)
      = (∫ x in (-(1 / 2))..(1 / 2), f x) ^ 2
        + ∑' k : ℕ, 2 * (∫ x in (-(1 / 2))..(1 / 2),
            f x * Real.cos (((k : ℝ) + 1) * Real.pi * (x + 1 / 2))) ^ 2 := by
  have h02 : (0:ℝ) < 2 := by norm_num
  have hL2 : MemLp (fun u => (hExt f u : ℂ)) 2 (volume.restrict (Set.Ioc (0:ℝ) 2)) :=
    memLp_continuous_Ioc (Complex.continuous_ofReal.comp (hExt_continuous hf)) 0 2
  have hpar := tsum_sq_fourierCoeffOn h02 hL2
  have hLHS : (∑' i : ℤ, ‖fourierCoeffOn h02 (fun u => (hExt f u : ℂ)) i‖ ^ 2)
      = ∑' i : ℤ, (cosCoeff f i)^2 := by
    congr 1
    funext i
    rw [fourierCoeffOn_hExt_eq hf i]
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  have hRHS : ((2:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..2, ‖(fun u => (hExt f u : ℂ)) x‖^2
      = ∫ x in (-(1/2))..(1/2), (f x)^2 := by
    rw [show (2:ℝ) - 0 = 2 by norm_num]
    have hb : (∫ x in (0:ℝ)..2, ‖((hExt f x : ℂ))‖^2) = ∫ x in (0:ℝ)..2, (hExt f x)^2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only []
      rw [Complex.sq_norm, Complex.normSq_ofReal]
      ring
    rw [hb]
    rw [smul_eq_mul]
    rw [show (2:ℝ)⁻¹ = 1/2 by norm_num]
    rw [← half_integral_eq hf, integral_sq_eq hf]
  have hmain : (∫ x in (-(1/2))..(1/2), (f x)^2) = ∑' i : ℤ, (cosCoeff f i)^2 := by
    rw [← hRHS, ← hLHS]
    exact hpar.symm
  have heven : Function.Even (fun i : ℤ => (cosCoeff f i)^2) := by
    intro i
    show (cosCoeff f (-i))^2 = (cosCoeff f i)^2
    congr 1
    unfold cosCoeff
    apply intervalIntegral.integral_congr
    intro u hu
    simp only []
    rw [show (((-i : ℤ) : ℝ) * Real.pi * u) = -(((i:ℤ):ℝ) * Real.pi * u) by push_cast; ring,
        Real.cos_neg]
  have hsummable : Summable (fun i : ℤ => (cosCoeff f i)^2) := by
    have h0 : Summable (fun i : ℤ =>
        ‖fourierCoeffOn h02 (fun u => (hExt f u : ℂ)) i‖^2) :=
      (hasSum_sq_fourierCoeffOn h02 hL2).summable
    refine h0.congr ?_
    intro i
    rw [fourierCoeffOn_hExt_eq hf i, Complex.sq_norm, Complex.normSq_ofReal]
    ring
  have hreindex : (∑' i : ℤ, (cosCoeff f i)^2)
      = (cosCoeff f 0)^2 + 2 * ∑' k : ℕ, (cosCoeff f ((k:ℤ)+1))^2 := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsummable]
    have hpnat : (∑' (n : ℕ+), (cosCoeff f (↑n : ℤ))^2)
        = ∑' k : ℕ, (cosCoeff f ((k:ℤ)+1))^2 := by
      rw [tsum_pnat_eq_tsum_succ (f := fun m : ℕ => (cosCoeff f (m : ℤ))^2)]
      simp only [Nat.cast_add, Nat.cast_one]
    rw [hpnat, nsmul_eq_mul]
    rfl
  rw [hmain, hreindex, cosCoeff_zero_eq hf]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [cosCoeff_succ_eq hf k]

end

end Commons.Analysis.Fourier