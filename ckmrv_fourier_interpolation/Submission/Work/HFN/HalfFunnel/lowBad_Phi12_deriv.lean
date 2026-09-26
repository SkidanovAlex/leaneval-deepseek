import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.HFN.HalfFunnel.lowBad_Aexp_tail
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.TailIntegral

noncomputable section

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open MeasureTheory UpperHalfPlane
open Filter
open scoped Topology

set_option maxHeartbeats 1000000

open Work.Kernels

/-! ## Geometry of the bad set -/

lemma lowBadSet_im_bounds {τ : ℍ} (hτ : lowBadSet τ) : (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2 :=
  ⟨hτ.2.1, hτ.2.2.1⟩

lemma lowBadSet_isBounded : Bornology.IsBounded lowBadSet :=
  badStrip_bounded.subset (fun τ hτ => mem_badStrip hτ)

lemma lowRho_pos : 0 < lowRho := by norm_num [lowRho]

/-! ## Flatness at the cusp `0` on the bad set -/

theorem lowBad_flat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ N : ℝ, 0 ≤ N → ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ), lowBadSet τ → 0 < t → t ≤ δ →
        ‖Kaxis (Kfun ℓ d) τ t‖ ≤ c * t ^ N := by
  obtain ⟨δ, hδ, h⟩ := Kaxis_cusp_of_bounded ℓ d hd lowBadSet_isBounded
  exact fun N hN => ⟨δ, hδ, h N hN⟩

/-! ## The translate pole off the window -/

lemma tsign_abs (τ : ℍ) : |tsign τ| = 1 := by
  unfold tsign
  split <;> norm_num

lemma norm_tpole_le_im (τ : ℍ) (t : ℝ) (h : t ≠ τ.im) :
    ‖tpole τ t‖ ≤ (1 / (2 * Real.pi)) / |t - τ.im| := by
  have hden : ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ))).im = t - τ.im := by
    simp [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      UpperHalfPlane.coe_im, mul_one, sub_zero]
  have hnum : ‖((tsign τ : ℂ) / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    have h1 : ‖(tsign τ : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, tsign_abs]
    have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
    rw [norm_div, h1, h2]
  have hpos : 0 < |t - τ.im| := abs_pos.mpr (sub_ne_zero.mpr h)
  have hge : |t - τ.im| ≤ ‖((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))
    rwa [hden] at this
  rw [tpole, norm_div, hnum]
  exact div_le_div_of_nonneg_left (by positivity) hpos hge

lemma norm_tpole_le_off {τ : ℍ} {t : ℝ} (h : lowRho ≤ |t - τ.im|) :
    ‖tpole τ t‖ ≤ 1 / (2 * Real.pi * lowRho) := by
  have hne : t ≠ τ.im := by
    intro hh
    rw [hh, sub_self, abs_zero] at h
    linarith [lowRho_pos]
  refine le_trans (norm_tpole_le_im τ t hne) ?_
  have hpos : 0 < |t - τ.im| := abs_pos.mpr (sub_ne_zero.mpr hne)
  rw [div_le_div_iff₀ hpos (by unfold lowRho; positivity : (0:ℝ) < 2 * Real.pi * lowRho)]
  have e1 : 1 / (2 * Real.pi) * (2 * Real.pi * lowRho) = lowRho := by
    field_simp
  rw [e1, one_mul]
  exact h

lemma not_mem_lowWin_iff {τ : ℍ} {t : ℝ} :
    t ∉ lowWin τ ↔ t ≤ τ.im - lowRho ∨ τ.im + lowRho ≤ t := by
  simp only [lowWin, Set.mem_Ioo, not_and, not_lt]
  constructor
  · intro h
    by_cases h1 : τ.im - lowRho < t
    · exact Or.inr (h h1)
    · exact Or.inl (not_lt.mp h1)
  · rintro (h | h) h1
    · linarith
    · linarith

/-! ## The spike-removed amplitude on the low range `(0, lowT]` -/

theorem lowBad_lowRange_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ (τ : UpperHalfPlane), lowBadSet τ →
      ∀ t : ℝ, 0 < t → t ≤ lowT →
        ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C) :
    ∀ (τ : UpperHalfPlane), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t‖
        ≤ C + 1 / (2 * Real.pi * lowRho) := by
  intro τ hτ t ht htT
  have hρ := lowRho_pos
  have hconst : (0:ℝ) ≤ 1 / (2 * Real.pi * lowRho) := by positivity
  by_cases hmem : t ∈ lowWin τ
  · rw [Set.indicator_of_mem hmem]
    exact le_trans (hdec τ hτ t ht htT) (by linarith)
  · rw [Set.indicator_of_notMem hmem, sub_zero]
    have hsep : lowRho ≤ |t - τ.im| := by
      rcases not_mem_lowWin_iff.mp hmem with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    have h1 : ‖Kaxis (Kfun ℓ d) τ t‖ ≤ ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ + ‖tpole τ t‖ := by
      have := norm_add_le (Kaxis (Kfun ℓ d) τ t - tpole τ t) (tpole τ t)
      simpa using this
    linarith [hdec τ hτ t ht htT, norm_tpole_le_off (τ := τ) (t := t) hsep]


/-! ## The scale is bounded on the bad set, and the cusp coefficients are bounded there -/

lemma scale_le_six {τ : ℍ} (hτ : lowBadSet τ) : scale τ ≤ 6 := by
  obtain ⟨hD, h1, h2, -⟩ := hτ
  obtain ⟨hre1, hre2⟩ := hD.1, hD.2.1
  have hinv : (τ.im)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ τ.im_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hnorm : ‖(τ : ℂ)‖ ≤ 3 := by
    have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hle : τ.re ^ 2 + τ.im ^ 2 ≤ 9 := by
      have h3 : τ.re ^ 2 < 1 := by nlinarith
      have h4 : τ.im ^ 2 ≤ 4 := by nlinarith
      linarith
    nlinarith [norm_nonneg (τ : ℂ)]
  unfold Work.Kernels.scale
  linarith

lemma Gcusp_bound_badSet (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (i j : Fin 2) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ τ : ℍ, lowBadSet τ → ‖Gcusp ℓ d i j τ‖ ≤ G := by
  obtain ⟨α, N, hα, hN, h⟩ :=
    (moderateGrowthOn_iff_scale DomainD (Gcusp ℓ d i j)).mp (GcuspInP ℓ d i j)
  refine ⟨α * 6 ^ N, by positivity, fun τ hτ => ?_⟩
  have hs : scale τ ≤ 6 := scale_le_six hτ
  have h1 : (Work.Kernels.scale τ) ^ N ≤ 6 ^ N :=
    Real.rpow_le_rpow (le_of_lt (Work.Kernels.scale_pos τ)) hs hN
  exact le_trans (h τ hτ.1) (mul_le_mul_of_nonneg_left h1 hα)

lemma Aexp_bound_on (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane), lowBadSet τ → ∀ t : ℝ, |t| ≤ T →
      ‖Aexp (Gcusp ℓ d) τ t‖ ≤ C := by
  obtain ⟨G00, hG00, hb00⟩ := Gcusp_bound_badSet ℓ d hd 0 0
  obtain ⟨G01, hG01, hb01⟩ := Gcusp_bound_badSet ℓ d hd 0 1
  obtain ⟨G10, hG10, hb10⟩ := Gcusp_bound_badSet ℓ d hd 1 0
  obtain ⟨G11, hG11, hb11⟩ := Gcusp_bound_badSet ℓ d hd 1 1
  refine ⟨G00 + max T 1 * G01 + Real.exp (2 * Real.pi * max T 1) * (G10 + max T 1 * G11),
    by positivity, fun τ hτ t ht => ?_⟩
  set T₁ : ℝ := max T 1 with hT₁
  have hT₁0 : 0 ≤ T₁ := le_trans zero_le_one (le_max_right T 1)
  have htT : |t| ≤ T₁ := le_trans ht (le_max_left T 1)
  have htT' : t ≤ T₁ := le_trans (le_abs_self t) htT
  have hti : ‖((t : ℂ) * Complex.I)‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hE : ‖Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))‖ ≤ Real.exp (2 * Real.pi * T₁) := by
    rw [Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * (t : ℂ)).re = 2 * Real.pi * t := by
      simp [Complex.mul_re]
    rw [hre]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h1 : ‖Gcusp ℓ d 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ‖
      ≤ G00 + T₁ * G01 := by
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ‖ ≤ T₁ * G01 := by
      rw [norm_mul, hti]
      exact mul_le_mul htT (hb01 τ hτ) (norm_nonneg _) hT₁0
    linarith [hb00 τ hτ]
  have h3 : ‖Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))
        * (Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ)‖
      ≤ Real.exp (2 * Real.pi * T₁) * (G10 + T₁ * G11) := by
    rw [norm_mul]
    refine mul_le_mul hE ?_ (norm_nonneg _) (Real.exp_pos _).le
    have h4 : ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ‖ ≤ T₁ * G11 := by
      rw [norm_mul, hti]
      exact mul_le_mul htT (hb11 τ hτ) (norm_nonneg _) hT₁0
    calc ‖Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ‖
        ≤ ‖Gcusp ℓ d 1 0 τ‖ + ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ‖ := norm_add_le _ _
      _ ≤ G10 + T₁ * G11 := by linarith [hb10 τ hτ]
  calc ‖Aexp (Gcusp ℓ d) τ t‖
      = ‖Gcusp ℓ d 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ
          + Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))
            * (Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ)‖ := rfl
    _ ≤ G00 + T₁ * G01 + Real.exp (2 * Real.pi * T₁) * (G10 + T₁ * G11) :=
        le_trans (norm_add_le _ _) (add_le_add h1 h3)

lemma one_add_mul_exp_neg_le (a : ℝ) (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) * Real.exp (-(a * t)) ≤ B := by
  refine ⟨1 + 1 / (a * Real.exp 1), by positivity, fun t ht => ?_⟩
  have h1 : a * t * Real.exp (-(a * t)) ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one (a * t)
  have h2 : a * Real.exp (-(a * t)) ≤ a := by
    have h3 : Real.exp (-(a * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    nlinarith [ha.le]
  have hkey : (1 + t) * Real.exp (-(a * t))
      = (1 / a) * (a * Real.exp (-(a * t)) + a * t * Real.exp (-(a * t))) := by
    field_simp
  have hEq : (1 / a) * (a + Real.exp (-1)) = 1 + 1 / (a * Real.exp 1) := by
    rw [show Real.exp (-1) = (Real.exp 1)⁻¹ from Real.exp_neg 1]
    field_simp
  calc (1 + t) * Real.exp (-(a * t))
      = (1 / a) * (a * Real.exp (-(a * t)) + a * t * Real.exp (-(a * t))) := hkey
    _ ≤ (1 / a) * (a + Real.exp (-1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 1 + 1 / (a * Real.exp 1) := hEq

lemma exists_exp_neg_le_pow {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x →
      Real.exp (-(c * x)) ≤ K * (1 + x) ^ (-(N : ℝ)) := by
  set a : ℝ := c / ((N : ℝ) + 1) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  obtain ⟨B, hB0, hB⟩ := one_add_mul_exp_neg_le a hapos
  refine ⟨B ^ (N + 1), by positivity, fun x hx => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + x := by linarith
  have h1 : (1 + x) ^ (N + 1) * Real.exp (-(c * x)) ≤ B ^ (N + 1) := by
    have h2 : (1 + x) * Real.exp (-(a * x)) ≤ B := hB x hx
    have h3 : ((1 + x) * Real.exp (-(a * x))) ^ (N + 1) ≤ B ^ (N + 1) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have h4 : ((1 + x) * Real.exp (-(a * x))) ^ (N + 1)
        = (1 + x) ^ (N + 1) * Real.exp (-(c * x)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have hexp : Real.exp (↑(N + 1) * (-(a * x))) = Real.exp (-(c * x)) := by
        congr 1
        have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
        rw [ha]
        push_cast
        field_simp
      rw [hexp]
    rwa [h4] at h3
  have h5 : (1 + x) ^ N * Real.exp (-(c * x)) ≤ (1 + x) ^ (N + 1) * Real.exp (-(c * x)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact pow_le_pow_right₀ hbase (by omega)
  have h6 : (1 + x) ^ N * Real.exp (-(c * x)) ≤ B ^ (N + 1) := le_trans h5 h1
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa [mul_comm] using h6

/-! ## Differentiating under the integral sign on a compact interval -/

/-- One step of differentiation under the integral sign for `y ↦ ∫_a^b g t · e^{-π y t}`, where
`g` is only assumed measurable and essentially bounded on `(a,b]`. -/
lemma hasDerivAt_intervalIntegral_exp_of_bound (g : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖g t‖ ≤ B) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in a..b, g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
      (∫ t in a..b, g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ))
      x := by
  set M : ℝ := max |a| |b| with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left |a| |b|)
  have hπM0 : 0 ≤ Real.pi * M := mul_nonneg Real.pi_pos.le hM0
  have htM : ∀ t ∈ Set.Ioc a b, |t| ≤ M := by
    intro t ht
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : |a| ≤ M := le_max_left |a| |b|
      have h2 : -M ≤ -|a| := neg_le_neg h1
      have h3 : -|a| ≤ a := neg_abs_le a
      linarith [ht.1]
    · have h1 : b ≤ M := le_trans (le_abs_self b) (le_max_right |a| |b|)
      linarith [ht.2]
  set B' : ℝ := B * max 1 (Real.pi * M) * Real.exp (Real.pi * (|x| + 1) * M) with hB'
  have hB'0 : 0 ≤ B' := by
    rw [hB']
    exact mul_nonneg (mul_nonneg hB (le_trans zero_le_one (le_max_left 1 (Real.pi * M))))
      (Real.exp_pos _).le
  have hmem : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), t ∈ Set.Ioc a b :=
    self_mem_ae_restrict measurableSet_Ioc
  have hx1 : 0 ≤ |x| + 1 := by linarith [abs_nonneg x]
  have hE0 : 0 ≤ Real.exp (Real.pi * (|x| + 1) * M) := (Real.exp_pos _).le
  have hexp_le : ∀ t y : ℝ, t ∈ Set.Ioc a b → y ∈ Metric.ball x 1 →
      Real.exp (-(Real.pi * y * t)) ≤ Real.exp (Real.pi * (|x| + 1) * M) := by
    intro t y ht hy
    apply Real.exp_le_exp.mpr
    have hy1 : |y| ≤ |x| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have h := abs_lt.mp hy
      rw [abs_le]
      exact ⟨by linarith [h.1, neg_abs_le x], by linarith [h.2, le_abs_self x]⟩
    have ht1 : |t| ≤ M := htM t ht
    have h1 : -(Real.pi * y * t) ≤ Real.pi * |y| * |t| := by
      have h := neg_le_abs (Real.pi * y * t)
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos] at h
      exact h
    have h2 : Real.pi * |y| * |t| ≤ Real.pi * (|x| + 1) * M := by
      have hπy : Real.pi * |y| ≤ Real.pi * (|x| + 1) :=
        mul_le_mul_of_nonneg_left hy1 Real.pi_pos.le
      calc Real.pi * |y| * |t| ≤ Real.pi * (|x| + 1) * |t| :=
            mul_le_mul_of_nonneg_right hπy (abs_nonneg t)
        _ ≤ Real.pi * (|x| + 1) * M :=
            mul_le_mul_of_nonneg_left ht1 (mul_nonneg Real.pi_pos.le hx1)
    linarith
  have hbd' : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ y ∈ Metric.ball x 1,
      ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ)‖ ≤ B' := by
    filter_upwards [hbd, hmem] with t hb ht y hy
    have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ)‖ = Real.pi * |t| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
    have hexp : ‖(Real.exp (-(Real.pi * y * t)) : ℂ)‖ = Real.exp (-(Real.pi * y * t)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hstep : Real.exp (-(Real.pi * y * t)) ≤ Real.exp (Real.pi * (|x| + 1) * M) :=
      hexp_le t y ht hy
    have h3 : Real.pi * |t| ≤ Real.pi * M := mul_le_mul_of_nonneg_left (htM t ht) Real.pi_pos.le
    calc ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ)‖
        = ‖g t‖ * (Real.pi * |t|) * Real.exp (-(Real.pi * y * t)) := by
          rw [norm_mul, norm_mul, hfac, hexp]
      _ ≤ B * (Real.pi * M) * Real.exp (Real.pi * (|x| + 1) * M) :=
          mul_le_mul (mul_le_mul hb h3 (mul_nonneg Real.pi_pos.le (abs_nonneg t)) hB)
            hstep (Real.exp_pos _).le (mul_nonneg hB hπM0)
      _ ≤ B * max 1 (Real.pi * M) * Real.exp (Real.pi * (|x| + 1) * M) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_right 1 (Real.pi * M)) hB) (Real.exp_pos _).le
      _ = B' := by rw [hB']
  have hbd'' : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ y ∈ Metric.ball x 1,
      HasDerivAt (fun y : ℝ => g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
        (g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ)) y := by
    filter_upwards with t y _
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(Real.pi * y * t)))
        (Real.exp (-(Real.pi * y * t)) * (-(Real.pi * t))) y := by
      have h2 : HasDerivAt (fun y : ℝ => -(Real.pi * y * t)) (-(Real.pi * t)) y := by
        have h3 : (fun y : ℝ => -(Real.pi * y * t)) = fun y : ℝ => (-(Real.pi * t)) * y := by
          funext y; ring
        rw [h3]
        simpa using (hasDerivAt_id y).const_mul (-(Real.pi * t))
      simpa using h2.exp
    have h5 := (h1.ofReal_comp).const_mul (g t)
    have heq : g t * (↑(Real.exp (-(Real.pi * y * t)) * (-(Real.pi * t))))
        = g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
      push_cast; ring
    rwa [heq] at h5
  have hIoc_lt : (volume : Measure ℝ) (Set.Ioc a b) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.Ioc_subset_Icc_self)) (isCompact_Icc.measure_lt_top)
  have hIntFx : Integrable (fun t : ℝ => g t * (Real.exp (-(Real.pi * x * t)) : ℂ))
      (volume.restrict (Set.Ioc a b)) := by
    refine IntegrableOn.of_bound hIoc_lt ?_ B' ?_
    · exact hmeas.mul (by fun_prop)
    · filter_upwards [hbd, hmem] with t hb ht
      have hexp : ‖(Real.exp (-(Real.pi * x * t)) : ℂ)‖ = Real.exp (-(Real.pi * x * t)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hle : Real.exp (-(Real.pi * x * t)) ≤ Real.exp (Real.pi * (|x| + 1) * M) := by
        apply Real.exp_le_exp.mpr
        have ht1 : |t| ≤ M := htM t ht
        have h1 : -(Real.pi * x * t) ≤ Real.pi * |x| * |t| := by
          have h := neg_le_abs (Real.pi * x * t)
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos] at h
          exact h
        have h2 : Real.pi * |x| * |t| ≤ Real.pi * (|x| + 1) * M := by
          have hπy : Real.pi * |x| ≤ Real.pi * (|x| + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [abs_nonneg x]) Real.pi_pos.le
          calc Real.pi * |x| * |t| ≤ Real.pi * (|x| + 1) * |t| :=
                mul_le_mul_of_nonneg_right hπy (abs_nonneg t)
            _ ≤ Real.pi * (|x| + 1) * M :=
                mul_le_mul_of_nonneg_left ht1 (mul_nonneg Real.pi_pos.le hx1)
        linarith
      calc ‖g t * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
          = ‖g t‖ * Real.exp (-(Real.pi * x * t)) := by rw [norm_mul, hexp]
        _ ≤ B * Real.exp (Real.pi * (|x| + 1) * M) :=
            mul_le_mul hb hle (Real.exp_pos _).le hB
        _ ≤ B * max 1 (Real.pi * M) * Real.exp (Real.pi * (|x| + 1) * M) := by
            have h1 : B ≤ B * max 1 (Real.pi * M) := by
              simpa using mul_le_mul_of_nonneg_left (le_max_left 1 (Real.pi * M)) hB
            exact mul_le_mul_of_nonneg_right h1 hE0
        _ = B' := by rw [hB']
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc a b))
    (F := fun y (t : ℝ) => g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
    (F' := fun y (t : ℝ) => g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ))
    (x₀ := x) (s := Metric.ball x 1) (bound := fun _ => B')
    (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall (fun y => hmeas.mul (by fun_prop)))
    hIntFx
    ((hmeas.mul (by fun_prop)).mul (by fun_prop))
    hbd' (integrable_const B') hbd''
  have hconv : ∀ f : ℝ → ℂ,
      (∫ t : ℝ, f t ∂(volume.restrict (Set.Ioc a b))) = ∫ t in a..b, f t := by
    intro f
    rw [intervalIntegral.integral_of_le hab]
  have hfun : (fun y : ℝ => ∫ t : ℝ, g t * (Real.exp (-(Real.pi * y * t)) : ℂ)
        ∂(volume.restrict (Set.Ioc a b)))
      = fun y : ℝ => ∫ t in a..b, g t * (Real.exp (-(Real.pi * y * t)) : ℂ) :=
    funext (fun y => hconv _)
  rw [hfun] at hmain
  rw [hconv (fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ))]
    at hmain
  exact hmain.2

/-- **Iterated differentiation under the integral sign** on `(a,b]` for a measurable, essentially
bounded amplitude. -/
theorem iteratedDeriv_intervalIntegral_exp_of_bound (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖f t‖ ≤ B) (m : ℕ) (x : ℝ) :
    iteratedDeriv m (fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ)) x
      = ∫ t in a..b, f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
          * (Real.exp (-(Real.pi * x * t)) : ℂ) := by
  induction m generalizing x with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    set M : ℝ := max |a| |b| with hM
    have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left |a| |b|)
    have hπM0 : 0 ≤ Real.pi * M := mul_nonneg Real.pi_pos.le hM0
    have htM : ∀ t ∈ Set.Ioc a b, |t| ≤ M := by
      intro t ht
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : |a| ≤ M := le_max_left |a| |b|
        have h2 : -M ≤ -|a| := neg_le_neg h1
        have h3 : -|a| ≤ a := neg_abs_le a
        linarith [ht.1]
      · have h1 : b ≤ M := le_trans (le_abs_self b) (le_max_right |a| |b|)
        linarith [ht.2]
    set g : ℝ → ℂ := fun t => f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ k with hg
    have hgmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)) :=
      hmeas.mul (by fun_prop)
    have hgbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖g t‖ ≤ B * (Real.pi * M) ^ k := by
      filter_upwards [hbd, self_mem_ae_restrict measurableSet_Ioc] with t hb ht
      have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ k‖ = (Real.pi * |t|) ^ k := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
      rw [hg, norm_mul, hfac]
      refine mul_le_mul hb (pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (abs_nonneg t))
        (mul_le_mul_of_nonneg_left (htM t ht) Real.pi_pos.le) k)
        (pow_nonneg (mul_nonneg Real.pi_pos.le (abs_nonneg t)) k) hB
    have hstep := hasDerivAt_intervalIntegral_exp_of_bound g a b hab hgmeas
      (mul_nonneg hB (pow_nonneg hπM0 k)) hgbd x
    have hIH : iteratedDeriv k (fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ))
        = fun y : ℝ => ∫ t in a..b, g t * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
      funext y
      rw [ih y, hg]
    rw [iteratedDeriv_succ, hIH, hstep.deriv]
    have hcongr : (fun t : ℝ => g t * (((-(Real.pi * t) : ℝ)) : ℂ)
          * (Real.exp (-(Real.pi * x * t)) : ℂ))
        = fun t : ℝ => f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ (k + 1)
          * (Real.exp (-(Real.pi * x * t)) : ℂ) := by
      funext t
      rw [hg, pow_succ]
      ring
    rw [hcongr]

/-! ## The derivative formula for a compact interval integral plus a tail integral -/

/-- **Iterated derivatives of a compact-interval integral plus a tail integral.** -/
private lemma iteratedDeriv_add_interval_tail (f₁ f₂ : ℝ → ℂ)
    (hmeas1 : AEStronglyMeasurable f₁ (volume.restrict (Set.Ioc (0:ℝ) 1)))
    {B₁ : ℝ} (hB₁ : 0 ≤ B₁)
    (hb₁ : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), ‖f₁ t‖ ≤ B₁)
    (hmeas2 : AEStronglyMeasurable f₂ (volume.restrict (Set.Ici (1:ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb₂ : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖f₂ t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) :
    ∀ (m : ℕ) (x : ℝ), -1 < x →
      iteratedDeriv m (fun y : ℝ =>
          (∫ t in (0:ℝ)..1, f₁ t * (Real.exp (-(Real.pi * y * t)) : ℂ)) + tailIntegral f₂ y) x
        = (∫ t in (0:ℝ)..1, f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
              * (Real.exp (-(Real.pi * x * t)) : ℂ))
          + tailIntegral (fun t : ℝ => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m) x := by
  intro m
  induction m with
  | zero =>
    intro x _
    have h1 : (∫ t in (0:ℝ)..1, f₁ t * (Real.exp (-(Real.pi * x * t)) : ℂ))
        = ∫ t in (0:ℝ)..1, f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ 0
            * (Real.exp (-(Real.pi * x * t)) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp
    have h2 : tailIntegral f₂ x
        = tailIntegral (fun t : ℝ => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ 0) x := by
      congr 1
      funext t
      simp
    rw [iteratedDeriv_zero, h1, h2]
  | succ k ih =>
    intro x hx
    set g₁ : ℝ → ℂ := fun t => f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ k with hg₁
    set g₂ : ℝ → ℂ := fun t => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ k with hg₂
    have hg1meas : AEStronglyMeasurable g₁ (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      hmeas1.mul (by fun_prop)
    have hg1bd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), ‖g₁ t‖ ≤ B₁ * Real.pi ^ k := by
      filter_upwards [hb₁, self_mem_ae_restrict measurableSet_Ioc] with t hb ht
      have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ k‖ = (Real.pi * t) ^ k := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
          abs_of_pos Real.pi_pos, abs_of_pos ht.1]
      rw [hg₁, norm_mul, hfac]
      refine mul_le_mul hb ?_ (pow_nonneg (mul_nonneg Real.pi_pos.le ht.1.le) k) hB₁
      exact pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le ht.1.le)
        (mul_le_of_le_one_right Real.pi_pos.le ht.2) k
    have hg2meas : AEStronglyMeasurable g₂ (volume.restrict (Set.Ici (1:ℝ))) :=
      hmeas2.mul (by fun_prop)
    have hg2bd : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
        ‖g₂ t‖ ≤ C * Real.pi ^ k * t ^ (M + (k : ℝ)) * Real.exp (-(Real.pi * t)) := by
      filter_upwards [tailIntegral_amp_ae_bound f₂ hb₂ k] with t ht
      simpa only [hg₂] using ht
    have hd1 := hasDerivAt_intervalIntegral_exp_of_bound g₁ 0 1 (by norm_num) hg1meas
      (mul_nonneg hB₁ (pow_nonneg Real.pi_pos.le k)) hg1bd x
    have hd2 := tailIntegral_hasDerivAt g₂ hg2meas (mul_nonneg hC (pow_nonneg Real.pi_pos.le k))
      (by positivity) hg2bd hx
    have hev : iteratedDeriv k (fun y : ℝ =>
        (∫ t in (0:ℝ)..1, f₁ t * (Real.exp (-(Real.pi * y * t)) : ℂ)) + tailIntegral f₂ y)
        =ᶠ[𝓝 x] fun y : ℝ => (∫ t in (0:ℝ)..1, g₁ t * (Real.exp (-(Real.pi * y * t)) : ℂ))
          + tailIntegral g₂ y := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      rw [ih y (Set.mem_Ioi.mp hy)]
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hfun_eq : (fun y : ℝ => (∫ t in (0:ℝ)..1, g₁ t * (Real.exp (-(Real.pi * y * t)) : ℂ))
          + tailIntegral g₂ y)
        = (fun y : ℝ => ∫ t in (0:ℝ)..1, g₁ t * (Real.exp (-(Real.pi * y * t)) : ℂ))
          + tailIntegral g₂ := by
      funext y
      simp
    rw [hfun_eq, (hd1.add hd2).deriv]
    have hcongr1 : (fun t : ℝ => g₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ))
        = fun t : ℝ => f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ (k + 1)
          * (Real.exp (-(Real.pi * x * t)) : ℂ) := by
      funext t
      rw [hg₁, pow_succ]
      ring
    have hcongr2 : tailIntegral (fun t : ℝ => g₂ t * (((-(Real.pi * t) : ℝ)) : ℂ))
        = tailIntegral (fun t : ℝ => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ (k + 1)) := by
      congr 1
      funext t
      rw [hg₂, pow_succ]
      ring
    rw [hcongr1, hcongr2]

/-! ## The main theorem -/

theorem lowBad_Phi12_deriv (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ C)
    (m N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ =>
        Work.Asymptotics.HalfFunnel.PhiOne ℓ d τ x + Work.Asymptotics.HalfFunnel.PhiTwo ℓ d τ x) x‖
        ≤ K * (1 + x) ^ (-(N : ℝ)) := by
  -- ## constants independent of `τ`
  obtain ⟨C₂, M₂, hC₂, hM₂, htail⟩ := lowBad_Aexp_tail ℓ d hd
  obtain ⟨C_A, hC_A, hAexp⟩ := Aexp_bound_on ℓ d hd 3
  obtain ⟨δ_fl, hδ_fl, c_fl, hc_fl, hflat⟩ := lowBad_flat ℓ d hd (N : ℝ) (by positivity)
  have hlow := lowBad_lowRange_bound ℓ d hd C hC hdec
  set C_low : ℝ := C + 1 / (2 * Real.pi * lowRho) with hC_low
  have hρ : 0 < 2 * Real.pi * lowRho := by rw [lowRho]; positivity
  have hC_low0 : 0 ≤ C_low := by
    rw [hC_low]; exact add_nonneg hC (le_of_lt (one_div_pos.mpr hρ))
  set δ₀ : ℝ := min δ_fl (1 / 4) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδ_fl (by norm_num)
  have hδ₀le : δ₀ ≤ δ_fl := min_le_left _ _
  have hδ₀le4 : δ₀ ≤ 1 / 4 := min_le_right _ _
  set B₁ : ℝ := max c_fl C_low with hB₁
  have hB₁0 : 0 ≤ B₁ := le_trans hc_fl.le (le_max_left _ _)
  have hB₁ge : C_low ≤ B₁ := le_max_right c_fl C_low
  set Cfl : ℝ := c_fl + B₁ / δ₀ ^ N with hCfl
  have hCfl0 : 0 ≤ Cfl := by
    rw [hCfl]; exact add_nonneg hc_fl.le (div_nonneg hB₁0 (pow_nonneg hδ₀pos.le N))
  have hCfl_ge : c_fl ≤ Cfl := by
    rw [hCfl]; exact le_add_of_nonneg_right (div_nonneg hB₁0 (pow_nonneg hδ₀pos.le N))
  have hCflδ : B₁ ≤ Cfl * δ₀ ^ N := by
    rw [hCfl]
    have h : (c_fl + B₁ / δ₀ ^ N) * δ₀ ^ N = c_fl * δ₀ ^ N + B₁ := by
      field_simp
    rw [h]; exact le_add_of_nonneg_left (mul_nonneg hc_fl.le (pow_nonneg hδ₀pos.le N))
  set B₂ : ℝ := C_low + C_A with hB₂
  have hB₂0 : 0 ≤ B₂ := by rw [hB₂]; linarith
  set M' : ℝ := max M₂ 1 with hM'
  have hM'0 : 0 ≤ M' := le_trans hM₂ (le_max_left M₂ 1)
  have hM₂le : M₂ ≤ M' := le_max_left M₂ 1
  set C' : ℝ := max (B₂ * Real.exp (3 * Real.pi)) (C₂ * 2 ^ M₂ * Real.exp (3 * Real.pi)) with hC'
  have hE3 : 0 < Real.exp (3 * Real.pi) := Real.exp_pos _
  have hC'0 : 0 ≤ C' := by
    rw [hC']; exact le_trans (mul_nonneg hB₂0 hE3.le) (le_max_left _ _)
  have hC'B₂ : B₂ * Real.exp (3 * Real.pi) ≤ C' := by rw [hC']; exact le_max_left _ _
  have hC'C₂ : C₂ * 2 ^ M₂ * Real.exp (3 * Real.pi) ≤ C' := by
    rw [hC']; exact le_max_right _ _
  have hC'C₂' : C₂ * 2 ^ M₂ ≤ C' := by
    refine le_trans ?_ hC'C₂
    have h1 : (1:ℝ) ≤ Real.exp (3 * Real.pi) := Real.one_le_exp (by positivity)
    have h2 : (0:ℝ) ≤ C₂ * 2 ^ M₂ := mul_nonneg hC₂.le (Real.rpow_nonneg (by norm_num) M₂)
    calc C₂ * 2 ^ M₂ = C₂ * 2 ^ M₂ * 1 := (mul_one _).symm
      _ ≤ C₂ * 2 ^ M₂ * Real.exp (3 * Real.pi) := mul_le_mul_of_nonneg_left h1 h2
  obtain ⟨K_e2, hK_e2_0, hK_e2⟩ := exists_exp_neg_le_pow (c := Real.pi) Real.pi_pos N
  set Kmain : ℝ := Cfl * Real.pi ^ m * ((N + m).factorial : ℝ) with hKmain
  have hKmain0 : 0 ≤ Kmain := by
    rw [hKmain]; exact mul_nonneg (mul_nonneg hCfl0 (pow_nonneg Real.pi_pos.le m)) (by positivity)
  set Ktail : ℝ := C' * Real.pi ^ m * tailDecay M' m * K_e2 with hKtail
  have hKtail0 : 0 ≤ Ktail := by
    rw [hKtail]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC'0 (pow_nonneg Real.pi_pos.le m))
      (tailDecay_nonneg M' m)) hK_e2_0
  set Ksmall : ℝ := (Cfl * Real.pi ^ m / ((N : ℝ) + m + 1) + C' * Real.pi ^ m * tailDecay M' m)
      * 2 ^ N with hKsmall
  have hKsmall0 : 0 ≤ Ksmall := by
    rw [hKsmall]
    refine mul_nonneg (add_nonneg ?_ ?_) (pow_nonneg (by norm_num) N)
    · exact div_nonneg (mul_nonneg hCfl0 (pow_nonneg Real.pi_pos.le m)) (by positivity)
    · exact mul_nonneg (mul_nonneg hC'0 (pow_nonneg Real.pi_pos.le m)) (tailDecay_nonneg M' m)
  refine ⟨max (Kmain + Ktail) Ksmall, le_trans (add_nonneg hKmain0 hKtail0) (le_max_left _ _),
    fun τ hτ x hx => ?_⟩
  -- ## the amplitude functions
  set f₁ : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t with hf₁
  set f₂ : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
      - (lowWin τ).indicator (tpole τ) t with hf₂
  have hKax : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t) := measurable_Kaxis_Kfun ℓ d hd τ
  have htp : Continuous (fun t : ℝ => tpole τ t) := by
    have hne : ∀ t : ℝ, (t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)) ≠ 0 := by
      intro t h0
      have h1 : ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ))).re = 0 := by rw [h0]; simp
      have h2 : ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ))).re = tsign τ - τ.re := by
        simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re]
      have h3 : τ.re ≠ tsign τ := by
        have h4 : |τ.re| < 1 := abs_lt.mpr ⟨hτ.1.1, hτ.1.2.1⟩
        unfold tsign
        split
        · intro hh; rw [hh] at h4; linarith [(abs_lt.mp h4).2]
        · intro hh; rw [hh] at h4; linarith [(abs_lt.mp h4).1]
      exact h3 (by linarith [h1, h2])
    exact continuous_const.div ((Continuous.mul Complex.continuous_ofReal continuous_const).sub
      continuous_const) hne
  have hAexc : Continuous (fun t : ℝ => Aexp (Gcusp ℓ d) τ t) := by
    unfold Aexp
    have h0 : Continuous fun t : ℝ => (t : ℂ) := Complex.continuous_ofReal
    exact ((continuous_const.add ((h0.mul continuous_const).mul continuous_const)).add
      ((Complex.continuous_exp.comp (continuous_const.mul h0)).mul
        (continuous_const.add ((h0.mul continuous_const).mul continuous_const))))
  have hmeas₁ : AEStronglyMeasurable f₁ (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => (lowWin τ).indicator (tpole τ) t) volume :=
      (htp.measurable.indicator measurableSet_Ioo).aestronglyMeasurable
    exact (hKax.aestronglyMeasurable.sub h1).restrict
  have hmeas₂ : AEStronglyMeasurable f₂ (volume.restrict (Set.Ici (1:ℝ))) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => (lowWin τ).indicator (tpole τ) t) volume :=
      (htp.measurable.indicator measurableSet_Ioo).aestronglyMeasurable
    exact ((hKax.aestronglyMeasurable.sub hAexc.measurable.aestronglyMeasurable).sub h1).restrict
  -- ## pointwise bounds for the two amplitudes
  have hbound₁ : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), ‖f₁ t‖ ≤ Cfl * t ^ N := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht1 : 0 < t := ht.1
    rcases le_or_gt t δ₀ with h | h
    · have hwin : t ∉ lowWin τ := by
        intro hmem
        simp only [lowWin, Set.mem_Ioo] at hmem
        have h2 : (3:ℝ)/8 < t := by
          have := hmem.1
          rw [lowRho] at this
          linarith [hτ.2.1]
        linarith [hδ₀le4, h]
      have hft : f₁ t = Kaxis (Kfun ℓ d) τ t := by
        simp only [hf₁, Set.indicator_of_notMem hwin, sub_zero]
      rw [hft]
      have hf := hflat τ t hτ ht1 (le_trans h hδ₀le)
      rw [Real.rpow_natCast t N] at hf
      exact le_trans hf (mul_le_mul_of_nonneg_right hCfl_ge (pow_nonneg ht1.le N))
    · have hft := hlow τ hτ t ht1 (by rw [lowT]; linarith [ht.2])
      refine le_trans hft ?_
      have h1 : C_low ≤ Cfl * δ₀ ^ N := le_trans hB₁ge hCflδ
      have h2 : Cfl * δ₀ ^ N ≤ Cfl * t ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ₀pos.le h.le N) hCfl0
      linarith
  have hbound₂ : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖f₂ t‖ ≤ C' * t ^ M' * Real.exp (-(Real.pi * t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with t ht
    have ht1 : 1 ≤ t := ht
    rcases le_or_gt t 3 with h3 | h3
    · have hb : ‖Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t‖ ≤ C_low :=
        hlow τ hτ t (by linarith) (by rw [lowT]; exact h3)
      have ha : ‖Aexp (Gcusp ℓ d) τ t‖ ≤ C_A := by
        refine hAexp τ hτ t ?_
        rw [abs_of_nonneg (by linarith)]
        linarith
      have hft : f₂ t = (Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
          - Aexp (Gcusp ℓ d) τ t := by
        simp only [hf₂]; ring
      rw [hft]
      refine le_trans (le_trans (norm_sub_le _ _) (add_le_add hb ha)) ?_
      have htM : (1:ℝ) ≤ t ^ M' := Real.one_le_rpow ht1 hM'0
      have hex : Real.exp (-(3 * Real.pi)) ≤ Real.exp (-(Real.pi * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have h0 : B₂ * Real.exp (3 * Real.pi) * Real.exp (-(3 * Real.pi)) = B₂ := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      calc B₂ = B₂ * Real.exp (3 * Real.pi) * Real.exp (-(3 * Real.pi)) := h0.symm
        _ ≤ C' * Real.exp (-(3 * Real.pi)) :=
            mul_le_mul_of_nonneg_right hC'B₂ (Real.exp_pos _).le
        _ ≤ C' * (t ^ M' * Real.exp (-(Real.pi * t))) := by
            refine mul_le_mul_of_nonneg_left ?_ hC'0
            simpa using mul_le_mul htM hex (Real.exp_pos _).le (by positivity)
        _ = C' * t ^ M' * Real.exp (-(Real.pi * t)) := by ring
    · have hwin : t ∉ lowWin τ := by
        intro hmem
        simp only [lowWin, Set.mem_Ioo] at hmem
        have := hmem.2
        rw [lowRho] at this
        linarith [hτ.2.2.1]
      have hft : f₂ t = Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t := by
        simp only [hf₂, Set.indicator_of_notMem hwin, sub_zero]
      rw [hft]
      refine le_trans (htail τ hτ t (by rw [lowT]; exact le_of_lt h3)) ?_
      have h1 : (1 + t) ^ M₂ ≤ (2 * t) ^ M₂ :=
        Real.rpow_le_rpow (by linarith) (by linarith) hM₂
      have h2 : (2 * t) ^ M₂ = 2 ^ M₂ * t ^ M₂ := Real.mul_rpow (by norm_num) (by linarith)
      have h4 : t ^ M₂ ≤ t ^ M' := Real.rpow_le_rpow_of_exponent_le ht1 hM₂le
      have h5 : (1 + t) ^ M₂ ≤ 2 ^ M₂ * t ^ M' := by
        rw [h2] at h1
        exact le_trans h1 (mul_le_mul_of_nonneg_left h4 (by positivity))
      have h6 : C₂ * (1 + t) ^ M₂ ≤ C' * t ^ M' := by
        calc C₂ * (1 + t) ^ M₂ ≤ C₂ * (2 ^ M₂ * t ^ M') := mul_le_mul_of_nonneg_left h5 hC₂.le
          _ = (C₂ * 2 ^ M₂) * t ^ M' := by ring
          _ ≤ C' * t ^ M' :=
              mul_le_mul_of_nonneg_right hC'C₂' (Real.rpow_nonneg (le_trans zero_le_one ht1) M')
      exact mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
  -- ## the derivative formula
  have hPhiOne : (fun y : ℝ => PhiOne ℓ d τ y)
      = fun y : ℝ => ∫ t in (0:ℝ)..1, f₁ t * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
    funext y
    rw [PhiOne, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    simp only [hf₁, Complex.ofReal_exp]
    push_cast
    ring
  have hPhiTwo : (fun y : ℝ => PhiTwo ℓ d τ y) = tailIntegral f₂ := by
    funext y
    rw [PhiTwo]
    unfold tailIntegral
    apply setIntegral_congr_fun measurableSet_Ici
    intro t _
    simp only [hf₂, Complex.ofReal_exp]
    push_cast
    ring
  have hfun : (fun y : ℝ => PhiOne ℓ d τ y + PhiTwo ℓ d τ y)
      = fun y : ℝ => (∫ t in (0:ℝ)..1, f₁ t * (Real.exp (-(Real.pi * y * t)) : ℂ))
          + tailIntegral f₂ y := by
    funext y
    rw [congrFun hPhiOne y, congrFun hPhiTwo y]
  have hbound₁c : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), ‖f₁ t‖ ≤ Cfl := by
    filter_upwards [hbound₁, self_mem_ae_restrict measurableSet_Ioc] with t hb ht
    refine le_trans hb ?_
    calc Cfl * t ^ N ≤ Cfl * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1.le ht.2) hCfl0
      _ = Cfl := mul_one Cfl
  rw [hfun,
    iteratedDeriv_add_interval_tail f₁ f₂ hmeas₁ hCfl0 hbound₁c hmeas₂ hC'0 hM'0 hbound₂ m x
      (by linarith)]
  -- ## the two estimates
  have hpt : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0:ℝ) 1 →
      ‖f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
        ≤ Cfl * Real.pi ^ m * (t ^ (N + m) * Real.exp (-(Real.pi * x * t))) := by
    have hb₁ := (ae_restrict_iff' measurableSet_Ioc).mp hbound₁
    filter_upwards [hb₁] with t hb ht
    have h1 : ‖f₁ t‖ ≤ Cfl * t ^ N := hb ht
    have h2 : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ m‖ = (Real.pi * t) ^ m := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos ht.1]
    have h3 : ‖(Real.exp (-(Real.pi * x * t)) : ℂ)‖ = Real.exp (-(Real.pi * x * t)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h4 : Cfl * t ^ N * (Real.pi * t) ^ m = Cfl * Real.pi ^ m * t ^ (N + m) := by
      rw [mul_pow, pow_add]
      ring
    calc ‖f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
        = ‖f₁ t‖ * (Real.pi * t) ^ m * Real.exp (-(Real.pi * x * t)) := by
          rw [norm_mul, norm_mul, h2, h3]
      _ ≤ (Cfl * t ^ N) * (Real.pi * t) ^ m * Real.exp (-(Real.pi * x * t)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (pow_nonneg (mul_nonneg Real.pi_pos.le ht.1.le) m))
            (Real.exp_pos _).le
      _ = Cfl * Real.pi ^ m * t ^ (N + m) * Real.exp (-(Real.pi * x * t)) := by rw [h4]
      _ = Cfl * Real.pi ^ m * (t ^ (N + m) * Real.exp (-(Real.pi * x * t))) := by ring
  have hI₁ : ‖∫ t in (0:ℝ)..1, f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
        * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
      ≤ Cfl * Real.pi ^ m * ∫ t in (0:ℝ)..1, t ^ (N + m) * Real.exp (-(Real.pi * x * t)) := by
    have hg : IntervalIntegrable (fun t : ℝ =>
        Cfl * Real.pi ^ m * (t ^ (N + m) * Real.exp (-(Real.pi * x * t)))) volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hstep := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
      (by norm_num) hpt hg
    rw [intervalIntegral.integral_const_mul] at hstep
    exact hstep
  have hI₃ : ∫ t in (0:ℝ)..1, t ^ (N + m) * Real.exp (-(Real.pi * x * t))
      ≤ 1 / ((N : ℝ) + m + 1) := by
    have hle : ∀ t ∈ Set.Icc (0:ℝ) 1,
        t ^ (N + m) * Real.exp (-(Real.pi * x * t)) ≤ t ^ (N + m) := by
      intro t ht
      have h1 : Real.exp (-(Real.pi * x * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0:ℝ) ≤ Real.pi * x * t := mul_nonneg (mul_nonneg Real.pi_pos.le hx) ht.1
        linarith
      calc t ^ (N + m) * Real.exp (-(Real.pi * x * t)) ≤ t ^ (N + m) * 1 :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg ht.1 (N + m))
        _ = t ^ (N + m) := mul_one _
    have h2 := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 1) (by norm_num)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop) hle
    rw [integral_pow] at h2
    have h3 : ((1:ℝ) ^ (N + m + 1) - (0:ℝ) ^ (N + m + 1)) / (↑(N + m) + 1)
        = 1 / ((N : ℝ) + m + 1) := by
      rw [one_pow, zero_pow (by omega)]
      push_cast
      norm_num
    rwa [h3] at h2
  have hJ : ‖tailIntegral (fun t : ℝ => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m) x‖
      ≤ C' * Real.pi ^ m * tailDecay M' m * Real.exp (-(Real.pi * x)) := by
    have hres := tailIntegral_iteratedDeriv_bound f₂ hmeas₂ hC'0 hM'0 hbound₂ m hx
    rwa [tailIntegral_iteratedDeriv f₂ hmeas₂ hC'0 hM'0 hbound₂ m x (by linarith)] at hres
  refine le_trans (norm_add_le _ _) ?_
  rcases le_or_gt 1 x with hx1 | hx1
  · -- large `x`: both terms decay like `(1+x)^{-N}`
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hI₂' : Cfl * Real.pi ^ m * ∫ t in (0:ℝ)..1, t ^ (N + m) * Real.exp (-(Real.pi * x * t))
        ≤ Kmain * (1 + x) ^ (-(N : ℝ)) := by
      have hπx0 : 0 < Real.pi * x := mul_pos Real.pi_pos hx0
      have hbase : (1:ℝ) ≤ 1 + x := by linarith
      have hle : (1 + x : ℝ) ≤ Real.pi * x := by nlinarith [Real.pi_gt_three, hx1]
      have hkey : (1 + x) ^ N ≤ (Real.pi * x) ^ (N + m + 1) := by
        calc (1 + x) ^ N ≤ (1 + x) ^ (N + m + 1) :=
              pow_le_pow_right₀ hbase (by omega)
          _ ≤ (Real.pi * x) ^ (N + m + 1) := pow_le_pow_left₀ (by linarith) hle _
      have hinv : (1 / (Real.pi * x) ^ (N + m + 1)) ≤ (1 + x) ^ (-(N : ℝ)) := by
        rw [Real.rpow_neg (by linarith), Real.rpow_natCast, one_div]
        exact inv_anti₀ (by positivity) hkey
      have hpow := intervalIntegral_pow_mul_exp_neg_le (k := N + m) (M := (1:ℝ))
        (c := Real.pi * x) (by norm_num) hπx0
      calc Cfl * Real.pi ^ m * ∫ t in (0:ℝ)..1, t ^ (N + m) * Real.exp (-(Real.pi * x * t))
          ≤ Cfl * Real.pi ^ m * (((N + m).factorial : ℝ) / (Real.pi * x) ^ (N + m + 1)) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = Cfl * Real.pi ^ m * ((N + m).factorial : ℝ) * ((Real.pi * x) ^ (N + m + 1))⁻¹ := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ Cfl * Real.pi ^ m * ((N + m).factorial : ℝ) * (1 + x) ^ (-(N : ℝ)) :=
            mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) (by positivity)
        _ = Kmain * (1 + x) ^ (-(N : ℝ)) := by rw [hKmain]
    have hJ' : ‖tailIntegral (fun t : ℝ => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m) x‖
        ≤ Ktail * (1 + x) ^ (-(N : ℝ)) := by
      refine le_trans hJ ?_
      rw [hKtail]
      have hc : (0:ℝ) ≤ C' * Real.pi ^ m * tailDecay M' m :=
        mul_nonneg (mul_nonneg hC'0 (pow_nonneg Real.pi_pos.le m)) (tailDecay_nonneg M' m)
      have := mul_le_mul_of_nonneg_left (hK_e2 x hx) hc
      simpa [mul_assoc] using this
    calc ‖∫ t in (0:ℝ)..1, f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
            * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
          + ‖tailIntegral (fun t : ℝ => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m) x‖
        ≤ Kmain * (1 + x) ^ (-(N : ℝ)) + Ktail * (1 + x) ^ (-(N : ℝ)) :=
          add_le_add (le_trans hI₁ hI₂') hJ'
      _ = (Kmain + Ktail) * (1 + x) ^ (-(N : ℝ)) := by ring
      _ ≤ max (Kmain + Ktail) Ksmall * (1 + x) ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  · -- small `x`: both terms are bounded by constants
    have hI₃' : Cfl * Real.pi ^ m * ∫ t in (0:ℝ)..1, t ^ (N + m) * Real.exp (-(Real.pi * x * t))
        ≤ Cfl * Real.pi ^ m / ((N : ℝ) + m + 1) := by
      have h3 : ∫ t in (0:ℝ)..1, t ^ (N + m) * Real.exp (-(Real.pi * x * t))
          ≤ ((↑N : ℝ) + ↑m + 1)⁻¹ := by
        rw [one_div] at hI₃
        exact hI₃
      have h := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ Cfl * Real.pi ^ m)
      simpa [div_eq_mul_inv] using h
    have hJ'' : ‖tailIntegral (fun t : ℝ => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m) x‖
        ≤ C' * Real.pi ^ m * tailDecay M' m := by
      refine le_trans hJ ?_
      have hex : Real.exp (-(Real.pi * x)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hx]
      have h2 : (0:ℝ) ≤ C' * Real.pi ^ m * tailDecay M' m :=
        mul_nonneg (mul_nonneg hC'0 (pow_nonneg Real.pi_pos.le m)) (tailDecay_nonneg M' m)
      calc C' * Real.pi ^ m * tailDecay M' m * Real.exp (-(Real.pi * x))
          ≤ C' * Real.pi ^ m * tailDecay M' m * 1 := mul_le_mul_of_nonneg_left hex h2
        _ = C' * Real.pi ^ m * tailDecay M' m := mul_one _
    calc ‖∫ t in (0:ℝ)..1, f₁ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
            * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
          + ‖tailIntegral (fun t : ℝ => f₂ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m) x‖
        ≤ Cfl * Real.pi ^ m / ((N : ℝ) + m + 1) + C' * Real.pi ^ m * tailDecay M' m :=
          add_le_add (le_trans hI₁ hI₃') hJ''
      _ = Ksmall * (2:ℝ) ^ (-(N : ℝ)) := by
          have h2N : (2:ℝ) ^ (-(N : ℝ)) = ((2:ℝ) ^ N)⁻¹ := by
            rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
          rw [hKsmall, h2N, mul_inv_cancel_right₀ (pow_ne_zero N (by norm_num : (2:ℝ) ≠ 0))]
      _ ≤ max (Kmain + Ktail) Ksmall * (1 + x) ^ (-(N : ℝ)) := by
          have h2 : (2:ℝ) ^ (-(N : ℝ)) ≤ (1 + x) ^ (-(N : ℝ)) := by
            rw [show (2:ℝ) ^ (-(N : ℝ)) = ((2:ℝ) ^ N)⁻¹ by
                rw [Real.rpow_neg (by norm_num), Real.rpow_natCast],
              show (1 + x) ^ (-(N : ℝ)) = ((1 + x) ^ N)⁻¹ by
                rw [Real.rpow_neg (by linarith), Real.rpow_natCast]]
            exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) N)
          calc Ksmall * (2:ℝ) ^ (-(N : ℝ)) ≤ Ksmall * (1 + x) ^ (-(N : ℝ)) :=
                mul_le_mul_of_nonneg_left h2 hKsmall0
            _ ≤ max (Kmain + Ktail) Ksmall * (1 + x) ^ (-(N : ℝ)) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)


end Work.HFN.HalfFunnel

