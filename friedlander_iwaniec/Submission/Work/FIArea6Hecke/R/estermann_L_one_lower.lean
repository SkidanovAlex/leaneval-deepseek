import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.S16Hecke.hecke_prod_coeff_nonneg
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.estermann_defs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

theorem estermann_coeff_facts {chi₁ chi₂ : GaussianInt → ℂ}
    (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hre₂ : ∀ z : GaussianInt, chi₂ z = star (chi₂ z))
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z * w) = chi₁ z * chi₁ w)
    (hmul₂ : ∀ z w : GaussianInt, chi₂ (z * w) = chi₂ z * chi₂ w)
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1) (hb₂ : ∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1) :
    ∃ a : ℕ → ℝ, a 1 = 1 ∧ (∀ n : ℕ, 0 ≤ a n) ∧
      LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < 2 ∧
      (∀ s : ℂ, 1 < s.re →
        (∑' n : ℕ, (a n : ℂ) * (n : ℂ) ^ (-s))
          = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) 0 s
            * Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s
            * Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s
            * Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) := by
  classical
  have htw : ∀ z : GaussianInt, ‖(fun z => chi₁ z * chi₂ z) z‖ ≤ 1 := fun z => by
    rw [norm_mul]
    exact mul_le_one₀ (hb₁ z) (norm_nonneg _) (hb₂ z)
  set a : ℕ → ℝ := fun n => (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re with ha
  have hconv_im : ∀ n : ℕ, (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).im = 0 :=
    Work.FIArea5.S16Hecke.Conv_im chi₁ chi₂ hre₁ hre₂
  have hcoe : (fun n => (a n : ℂ)) = Work.FIArea5.S16Hecke.Conv chi₁ chi₂ := by
    funext n
    apply Complex.ext
    · simp [ha]
    · simp [ha, hconv_im n]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · rw [ha]
    simp [Work.FIArea5.S16Hecke.Conv_one chi₁ chi₂ h1₁ h1₂]
  · intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [ha]
      simp [Work.FIArea5.S16Hecke.Conv, LSeries.convolution_def]
    · rw [ha]
      exact Work.FIArea5.S16Hecke.Conv_re_nonneg chi₁ chi₂ h1₁ h1₂ hre₁ hre₂ hmul₁ hmul₂
        hb₁ hb₂ n h
  · rw [hcoe]
    have hmul_le : ∀ {f g : ℕ → ℂ},
        LSeries.abscissaOfAbsConv f ≤ (1 : EReal) → LSeries.abscissaOfAbsConv g ≤ (1 : EReal) →
        LSeries.abscissaOfAbsConv (LSeries.convolution f g) ≤ (1 : EReal) := by
      intro f g hf hg
      exact le_trans (LSeries.abscissaOfAbsConv_convolution_le f g) (max_le hf hg)
    have hA : LSeries.abscissaOfAbsConv
        (Work.FIArea5.S16Hecke.heckeLam (fun _ => (1 : ℂ)) 0) ≤ (1 : EReal) :=
      Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one _ 0 (by intro z; simp)
    have hB : LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi₁ 0) ≤ (1 : EReal) :=
      Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one _ 0 hb₁
    have hC : LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi₂ 0) ≤ (1 : EReal) :=
      Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one _ 0 hb₂
    have hD : LSeries.abscissaOfAbsConv
        (Work.FIArea5.S16Hecke.heckeLam (fun z => chi₁ z * chi₂ z) 0) ≤ (1 : EReal) :=
      Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one _ 0 htw
    have hConv : Work.FIArea5.S16Hecke.Conv chi₁ chi₂ = LSeries.convolution (LSeries.convolution
        (LSeries.convolution (Work.FIArea5.S16Hecke.heckeLam (fun _ => (1 : ℂ)) 0)
          (Work.FIArea5.S16Hecke.heckeLam chi₁ 0))
          (Work.FIArea5.S16Hecke.heckeLam chi₂ 0))
          (Work.FIArea5.S16Hecke.heckeLam (fun z => chi₁ z * chi₂ z) 0) := rfl
    rw [hConv]
    exact lt_of_le_of_lt (hmul_le (hmul_le (hmul_le hA hB) hC) hD) (by norm_num)
  · intro s hs
    rw [ha]
    have hConv0 : Work.FIArea5.S16Hecke.Conv chi₁ chi₂ 0 = 0 := by
      simp [Work.FIArea5.S16Hecke.Conv, LSeries.convolution_def]
    have hterm : (∑' n : ℕ, ((Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re : ℂ) * (n : ℂ) ^ (-s))
        = LSeries (Work.FIArea5.S16Hecke.Conv chi₁ chi₂) s := by
      rw [show LSeries (Work.FIArea5.S16Hecke.Conv chi₁ chi₂) s
          = ∑' n, Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n * (n : ℂ) ^ (-s) from by
            rw [LSeries]
            exact tsum_congr (fun n => LSeries.term_def₀ hConv0 s n)]
      exact tsum_congr (fun n => by rw [show (((Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re : ℂ)) = Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n from Complex.ext rfl (by rw [Complex.ofReal_im, hconv_im n])])
    rw [hterm]
    have hsumm0 : LSeriesSummable (Work.FIArea5.S16Hecke.heckeLam (fun _ => (1 : ℂ)) 0) s :=
      Work.FIArea5.S16Hecke.summable_heckeLam _ (by intro z; simp) hs
    have hsumm1 : LSeriesSummable (Work.FIArea5.S16Hecke.heckeLam chi₁ 0) s :=
      Work.FIArea5.S16Hecke.summable_heckeLam _ hb₁ hs
    have hsumm2 : LSeriesSummable (Work.FIArea5.S16Hecke.heckeLam chi₂ 0) s :=
      Work.FIArea5.S16Hecke.summable_heckeLam _ hb₂ hs
    have hsumm3 : LSeriesSummable (Work.FIArea5.S16Hecke.heckeLam (fun z => chi₁ z * chi₂ z) 0) s :=
      Work.FIArea5.S16Hecke.summable_heckeLam _ htw hs
    have e1 := LSeries_convolution' hsumm0 hsumm1
    have e2 := LSeries_convolution' (hsumm0.convolution hsumm1) hsumm2
    have e3 := LSeries_convolution' ((hsumm0.convolution hsumm1).convolution hsumm2) hsumm3
    rw [Work.FIArea5.S16Hecke.Conv, e3, e2, e1]
    simp only [Work.FIArea5.S16Hecke.heckeLSeries]

/-- **The real-arithmetic step of the Goldfeld/Estermann lower bound.** -/
theorem estermann_L_one_arith {β₁ C maxd Y : ℝ} (hC : 1 ≤ C) (hβ₁lo : 19 / 20 ≤ β₁)
    (hβ₁hi : β₁ < 1) (hmaxd : 1 ≤ maxd)
    (h : (1 / 4) * (1 - β₁) * (C ^ 5 * maxd ^ 40) ^ (-(3 * (1 - β₁)))
          ≤ (C ^ 4 * maxd ^ 30) * Y) :
    ((1 / 4) * C ^ (-(19 : ℝ))) * (1 - β₁) * maxd ^ (-(60 : ℝ)) ≤ Y := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hmaxdpos : 0 < maxd := lt_of_lt_of_le zero_lt_one hmaxd
  have hCnn : (0 : ℝ) ≤ C ^ 5 := by positivity
  have hmaxdnn : (0 : ℝ) ≤ maxd ^ 40 := by positivity
  have hkey : C ^ (-(15 : ℝ)) * maxd ^ (-(6 : ℝ)) ≤ (C ^ 5 * maxd ^ 40) ^ (-(3 * (1 - β₁))) := by
    rw [Real.mul_rpow hCnn hmaxdnn]
    have e1 : (C ^ 5) ^ (-(3 * (1 - β₁))) = C ^ (-(15 * (1 - β₁))) := by
      rw [← Real.rpow_natCast C 5, ← Real.rpow_mul hCpos.le]
      congr 1
      push_cast
      ring
    have e2 : (maxd ^ 40) ^ (-(3 * (1 - β₁))) = maxd ^ (-(120 * (1 - β₁))) := by
      rw [← Real.rpow_natCast maxd 40, ← Real.rpow_mul hmaxdpos.le]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    refine mul_le_mul ?_ ?_ (Real.rpow_nonneg hmaxdpos.le _) (Real.rpow_nonneg hCpos.le _)
    · exact Real.rpow_le_rpow_of_exponent_le hC (by linarith)
    · exact Real.rpow_le_rpow_of_exponent_le hmaxd (by linarith)
  have hstep : C ^ (-(19 : ℝ)) * maxd ^ (-(60 : ℝ)) * (C ^ 4 * maxd ^ 30)
      ≤ (C ^ 5 * maxd ^ 40) ^ (-(3 * (1 - β₁))) := by
    have h1 : C ^ (-(19 : ℝ)) * C ^ 4 = C ^ (-(15 : ℝ)) := by
      rw [← Real.rpow_natCast C 4, ← Real.rpow_add hCpos]
      norm_num
    have h2 : maxd ^ (-(60 : ℝ)) * maxd ^ 30 = maxd ^ (-(30 : ℝ)) := by
      rw [← Real.rpow_natCast maxd 30, ← Real.rpow_add hmaxdpos]
      norm_num
    have h3 : maxd ^ (-(30 : ℝ)) ≤ maxd ^ (-(6 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hmaxd (by norm_num)
    calc C ^ (-(19 : ℝ)) * maxd ^ (-(60 : ℝ)) * (C ^ 4 * maxd ^ 30)
        = (C ^ (-(19 : ℝ)) * C ^ 4) * (maxd ^ (-(60 : ℝ)) * maxd ^ 30) := by ring
      _ = C ^ (-(15 : ℝ)) * maxd ^ (-(30 : ℝ)) := by rw [h1, h2]
      _ ≤ C ^ (-(15 : ℝ)) * maxd ^ (-(6 : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hCpos.le _)
      _ ≤ (C ^ 5 * maxd ^ 40) ^ (-(3 * (1 - β₁))) := hkey
  have hdiv : (1 / 4) * (1 - β₁) * (C ^ 5 * maxd ^ 40) ^ (-(3 * (1 - β₁))) / (C ^ 4 * maxd ^ 30)
      ≤ Y := by
    rw [div_le_iff₀ (by positivity)]
    exact le_trans h (le_of_eq (by ring))
  refine le_trans ?_ hdiv
  have hfac : (0 : ℝ) ≤ (1 / 4) * (1 - β₁) := by linarith
  have hgoal : (1 / 4) * C ^ (-(19 : ℝ)) * (1 - β₁) * maxd ^ (-(60 : ℝ))
      ≤ (1 / 4) * (1 - β₁) * (C ^ 5 * maxd ^ 40) ^ (-(3 * (1 - β₁))) / (C ^ 4 * maxd ^ 30) := by
    rw [le_div_iff₀ (by positivity)]
    calc (1 / 4) * C ^ (-(19 : ℝ)) * (1 - β₁) * maxd ^ (-(60 : ℝ)) * (C ^ 4 * maxd ^ 30)
        = ((1 / 4) * (1 - β₁)) * (C ^ (-(19 : ℝ)) * maxd ^ (-(60 : ℝ)) * (C ^ 4 * maxd ^ 30)) := by
          ring
      _ ≤ ((1 / 4) * (1 - β₁)) * (C ^ 5 * maxd ^ 40) ^ (-(3 * (1 - β₁))) :=
          mul_le_mul_of_nonneg_left hstep hfac
      _ = (1 / 4) * (1 - β₁) * (C ^ 5 * maxd ^ 40) ^ (-(3 * (1 - β₁))) := by ring
  exact hgoal

/-- **The Goldfeld/Estermann step of *FI* Lemma 16.1**: a lower bound for `L(1,χ₂)` in terms of an
exceptional real zero `β₁` of `L(·,χ₁)`. -/
theorem estermann_L_one_lower
    {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ}
    (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hre₂ : ∀ z : GaussianInt, chi₂ z = star (chi₂ z))
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z * w) = chi₁ z * chi₁ w)
    (hmul₂ : ∀ z w : GaussianInt, chi₂ (z * w) = chi₂ z * chi₂ w)
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1) (hb₂ : ∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1)
    {Lam₁ Lam₂ : ℂ → ℂ} (hAn₁ : AnalyticOn ℂ Lam₁ Set.univ)
    (hAgr₁ : ∀ s : ℂ, 1 < s.re →
      Lam₁ s = Work.FITop4.Bridge.heckeArch d₁ 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s)
    (hAn₂ : AnalyticOn ℂ Lam₂ Set.univ)
    (hAgr₂ : ∀ s : ℂ, 1 < s.re →
      Lam₂ s = Work.FITop4.Bridge.heckeArch d₂ 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s)
    {F : ℂ → ℂ} (hFan : AnalyticOn ℂ F Set.univ)
    (hFagr : ∀ s : ℂ, 1 < s.re →
      F s = Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s)
    (hζK : ∀ s : ℂ, 1 < s.re →
      Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) 0 s
        = riemannZeta s * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s
            * (1 - (2 : ℂ) ^ (-s)))
    {β₁ : ℝ} (hβ₁lo : 19 / 20 ≤ β₁) (hβ₁hi : β₁ < 1) (hzero : Lam₁ (β₁ : ℂ) = 0)
    {C : ℝ} (hC : 1 ≤ C)
    (hbnd₁ : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s‖ ≤ C * (d₁ : ℝ) ^ (10 : ℕ))
    (hbnd₂ : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s‖ ≤ C * (d₂ : ℝ) ^ (10 : ℕ))
    (hbndF : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖F s‖ ≤ C * ((d₁ * d₂ : ℕ) : ℝ) ^ (10 : ℕ))
    (hbndL4 : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s‖ ≤ C)
    (hbnd2s : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖1 - (2 : ℂ) ^ (-s)‖ ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      c * (1 - β₁) * (max (d₁ : ℝ) (d₂ : ℝ)) ^ (-(60 : ℝ))
        ≤ ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by
  classical
  obtain ⟨a, ha1, hanonneg, habsc, hser⟩ :=
    estermann_coeff_facts h1₁ h1₂ hre₁ hre₂ hmul₁ hmul₂ hb₁ hb₂
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hmax1 : (1 : ℝ) ≤ max (d₁ : ℝ) (d₂ : ℝ) :=
    le_trans (by exact_mod_cast h₁) (le_max_left _ _)
  have hmaxpos : (0 : ℝ) < max (d₁ : ℝ) (d₂ : ℝ) := lt_of_lt_of_le zero_lt_one hmax1
  set f : ℂ → ℂ := fun s => (1 - (2 : ℂ) ^ (-s)) * DirichletCharacter.LFunction chi4C s *
      Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s * Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s * F s with hf
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall (2 : ℂ) (3 / 2)) := by
    intro z hz
    have hsub : AnalyticAt ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (-s)) z := by
      have h1 : Differentiable ℂ (fun s : ℂ => (2 : ℂ) ^ (-s)) :=
        Differentiable.const_cpow (Differentiable.neg differentiable_id) (Or.inl (by norm_num))
      exact ((differentiable_const (c := (1 : ℂ))).sub h1).analyticAt z
    have hL : AnalyticAt ℂ (DirichletCharacter.LFunction chi4C) z :=
      (DirichletCharacter.differentiable_LFunction chi4C_ne_one).analyticAt z
    have hL1 : AnalyticAt ℂ (fun s => Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s) z :=
      analyticAt_Lval_of_mem_ball h₁ hAn₁ hz
    have hL2 : AnalyticAt ℂ (fun s => Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s) z :=
      analyticAt_Lval_of_mem_ball h₂ hAn₂ hz
    have hF' : AnalyticAt ℂ F z := AnalyticOn.analyticAt (s := Set.univ) Filter.univ_mem hFan
    simp only [hf]
    exact (((hsub.mul hL).mul hL1).mul hL2).mul hF'
  have hfb : ∀ z ∈ Metric.closedBall (2 : ℂ) (3 / 2),
      ‖f z‖ ≤ C ^ 5 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 40 := by
    intro z hz
    have b1 := hbnd2s z hz
    have b2 := hbndL4 z hz
    have b3 := hbnd₁ z hz
    have b4 := hbnd₂ z hz
    have b5 := hbndF z hz
    simp only [hf, norm_mul]
    have hAB : ‖1 - (2 : ℂ) ^ (-z)‖ * ‖DirichletCharacter.LFunction chi4C z‖ *
          ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ z‖ * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ z‖ * ‖F z‖
        ≤ (C ^ 5 * (d₁ : ℝ) ^ 20) * (d₂ : ℝ) ^ 20 := by
      calc ‖1 - (2 : ℂ) ^ (-z)‖ * ‖DirichletCharacter.LFunction chi4C z‖ *
            ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ z‖ * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ z‖ * ‖F z‖
          ≤ C * C * (C * (d₁ : ℝ) ^ 10) * (C * (d₂ : ℝ) ^ 10)
              * (C * ((d₁ * d₂ : ℕ) : ℝ) ^ 10) := by gcongr
        _ = (C ^ 5 * (d₁ : ℝ) ^ 20) * (d₂ : ℝ) ^ 20 := by push_cast; ring
    refine le_trans hAB ?_
    have e1 : (d₁ : ℝ) ^ 20 ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 20 :=
      pow_le_pow_left₀ (by positivity) (le_max_left _ _) 20
    have e2 : (d₂ : ℝ) ^ 20 ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 20 :=
      pow_le_pow_left₀ (by positivity) (le_max_right _ _) 20
    have e3 : (d₁ : ℝ) ^ 20 * (d₂ : ℝ) ^ 20 ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 40 := by
      calc (d₁ : ℝ) ^ 20 * (d₂ : ℝ) ^ 20
          ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 20 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 20 :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = (max (d₁ : ℝ) (d₂ : ℝ)) ^ 40 := by ring
    rw [show C ^ 5 * (d₁ : ℝ) ^ 20 * (d₂ : ℝ) ^ 20
        = C ^ 5 * ((d₁ : ℝ) ^ 20 * (d₂ : ℝ) ^ 20) from by ring]
    exact mul_le_mul_of_nonneg_left e3 (by positivity)
  have hMbound1 : (1 : ℝ) ≤ C ^ 5 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 40 := by
    have h1 : (1 : ℝ) ≤ C ^ 5 := one_le_pow₀ hC
    have h2 : (1 : ℝ) ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 40 := one_le_pow₀ hmax1
    nlinarith
  have hζσ : ∃ c : ℝ, c < 0 ∧ riemannZeta (β₁ : ℂ) = (c : ℂ) :=
    Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one (by linarith) hβ₁hi
  have hfσ : 0 ≤ (f (β₁ : ℂ)).re := by
    have hL1z : Work.FIArea6Hecke.Lval d₁ 0 Lam₁ (β₁ : ℂ) = 0 := by
      rw [Work.FIArea6Hecke.Lval, hzero, zero_div]
    have hz0 : f (β₁ : ℂ) = 0 := by
      simp only [hf, hL1z, mul_zero, zero_mul]
    rw [hz0]
    simp
  have hseries : ∀ s : ℂ, 1 < s.re → riemannZeta s * f s = ∑' n : ℕ, (a n : ℂ) * (n : ℂ) ^ (-s) := by
    intro s hs
    have hs0 : 0 < s.re := lt_trans zero_lt_one hs
    have harch₁ : Work.FITop4.Bridge.heckeArch d₁ 0 s ≠ 0 :=
      Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re h₁ 0 hs0
    have harch₂ : Work.FITop4.Bridge.heckeArch d₂ 0 s ≠ 0 :=
      Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re h₂ 0 hs0
    have hlv₁ : Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s
        = Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s := by
      rw [Work.FIArea6Hecke.Lval, hAgr₁ s hs, mul_div_cancel_left₀ _ harch₁]
    have hlv₂ : Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s
        = Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s := by
      rw [Work.FIArea6Hecke.Lval, hAgr₂ s hs, mul_div_cancel_left₀ _ harch₂]
    have hlvF : F s = Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s :=
      hFagr s hs
    rw [hser s hs]
    simp only [hf, hlv₁, hlv₂, hlvF]
    rw [hζK s hs]
    ring
  have hE := Commons.NumberTheory.DirichletCharacter.estermann_positivity
      (f := f) (r := a) (M := C ^ 5 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 40) (σ := β₁) (K := 10)
      (by norm_num) hMbound1 hβ₁lo hβ₁hi hfa hfb
      (fun z hz => Commons.NumberTheory.DirichletCharacter.norm_riemannZeta_le_ten_of_mem_sphere hz)
      hζσ hanonneg ha1 habsc hseries hfσ
  have h1mem : (1 : ℂ) ∈ Metric.closedBall (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    norm_num
  have hf1 : ‖f 1‖ = ‖1 - (2 : ℂ) ^ (-(1 : ℂ))‖ * ‖DirichletCharacter.LFunction chi4C 1‖ *
      ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * ‖F 1‖ := by
    simp only [hf, norm_mul]
  have hAB1 : ‖1 - (2 : ℂ) ^ (-(1 : ℂ))‖ * ‖DirichletCharacter.LFunction chi4C 1‖ *
      ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ * ‖F 1‖
      ≤ C ^ 4 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 30 := by
    have b1 := hbnd2s 1 h1mem
    have b2 := hbndL4 1 h1mem
    have b3 := hbnd₁ 1 h1mem
    have b5 := hbndF 1 h1mem
    calc ‖1 - (2 : ℂ) ^ (-(1 : ℂ))‖ * ‖DirichletCharacter.LFunction chi4C 1‖ *
          ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ * ‖F 1‖
        ≤ C * C * (C * (d₁ : ℝ) ^ 10) * (C * ((d₁ * d₂ : ℕ) : ℝ) ^ 10) := by gcongr
      _ = C ^ 4 * ((d₁ : ℝ) ^ 20 * (d₂ : ℝ) ^ 10) := by push_cast; ring
      _ ≤ C ^ 4 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 30 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have e1 : (d₁ : ℝ) ^ 20 ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 20 :=
            pow_le_pow_left₀ (by positivity) (le_max_left _ _) 20
          have e2 : (d₂ : ℝ) ^ 10 ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 10 :=
            pow_le_pow_left₀ (by positivity) (le_max_right _ _) 10
          calc (d₁ : ℝ) ^ 20 * (d₂ : ℝ) ^ 10
              ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 20 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 10 :=
                mul_le_mul e1 e2 (by positivity) (by positivity)
            _ = (max (d₁ : ℝ) (d₂ : ℝ)) ^ 30 := by ring
  have hre_le : (1 / 4) * (1 - β₁) * (C ^ 5 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 40) ^ (-(3 * (1 - β₁)))
      ≤ (C ^ 4 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 30) * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by
    refine le_trans hE (le_trans (Complex.re_le_norm (f 1)) ?_)
    rw [hf1]
    calc ‖1 - (2 : ℂ) ^ (-(1 : ℂ))‖ * ‖DirichletCharacter.LFunction chi4C 1‖ *
          ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * ‖F 1‖
        = (‖1 - (2 : ℂ) ^ (-(1 : ℂ))‖ * ‖DirichletCharacter.LFunction chi4C 1‖ *
            ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ * ‖F 1‖)
            * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by ring
      _ ≤ (C ^ 4 * (max (d₁ : ℝ) (d₂ : ℝ)) ^ 30) * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ :=
          mul_le_mul_of_nonneg_right hAB1 (norm_nonneg _)
  exact ⟨(1 / 4) * C ^ (-(19 : ℝ)),
    by positivity, estermann_L_one_arith hC hβ₁lo hβ₁hi hmax1 hre_le⟩

end

end Work.FIArea6Hecke.R
