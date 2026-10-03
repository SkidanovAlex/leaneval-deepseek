import Mathlib
import Submission.Work.FIArea6Hecke.R.estermann_L_one_lower_scaled
import Submission.Work.FIArea6Hecke.R.estermannF_analyticOnNhd
import Submission.Work.FIArea6Hecke.R.estermann_defs

namespace Work.FIArea6Hecke.R

open scoped BigOperators


/-- `estermannF d₁ d₂ Lam₁ Lam₂ F` is analytic on a neighbourhood of the closed disc
`|s - 2| ≤ 3/2` when `Lam₁, Lam₂` are entire and `F` is analytic on that disc (rather than
entire): each of its five factors is analytic there, the two quotients
`Lval d 0 Lam = Lam / heckeArch d 0` because `heckeArch d 0` is non-vanishing and analytic for
`re s > 0`, and `LFunction chi4C` because a Dirichlet `L`-function is entire. -/
theorem estermannF_analyticOnNhd_ball {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {Lam₁ Lam₂ F : ℂ → ℂ} (hAn₁ : AnalyticOn ℂ Lam₁ Set.univ) (hAn₂ : AnalyticOn ℂ Lam₂ Set.univ)
    (hFan : AnalyticOnNhd ℂ F (Metric.closedBall (2 : ℂ) (3 / 2))) :
    AnalyticOnNhd ℂ (estermannF d₁ d₂ Lam₁ Lam₂ F) (Metric.closedBall (2 : ℂ) (3 / 2)) := by
  intro z hz
  have hfac1 : AnalyticAt ℂ (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (-s)) z :=
    analyticAt_one_sub_two_cpow z
  have hfac2 : AnalyticAt ℂ (DirichletCharacter.LFunction chi4C) z :=
    (DirichletCharacter.differentiable_LFunction chi4C_ne_one).analyticAt z
  have hfac3 : AnalyticAt ℂ (fun s : ℂ => Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s) z :=
    analyticAt_Lval_of_mem_ball h₁ hAn₁ hz
  have hfac4 : AnalyticAt ℂ (fun s : ℂ => Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s) z :=
    analyticAt_Lval_of_mem_ball h₂ hAn₂ hz
  have hfac5 : AnalyticAt ℂ F z := hFan z hz
  have hprod : AnalyticAt ℂ
      (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (-s)) * DirichletCharacter.LFunction chi4C s *
        Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s * Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s * F s) z :=
    (((hfac1.mul hfac2).mul hfac3).mul hfac4).mul hfac5
  unfold estermannF
  exact hprod

theorem estermannBall
    {d₁ : ℕ} (h₁ : 1 ≤ d₁) {chi₁ : GaussianInt → ℂ}
    (h1₁ : chi₁ 1 = 1)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z * w) = chi₁ z * chi₁ w)
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1)
    {Lam₁ : ℂ → ℂ} (hAn₁ : AnalyticOn ℂ Lam₁ Set.univ)
    (hAgr₁ : ∀ s : ℂ, 1 < s.re →
      Lam₁ s = Work.FITop4.Bridge.heckeArch d₁ 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s)
    (hζK : ∀ s : ℂ, 1 < s.re →
      Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) 0 s
        = riemannZeta s * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s
            * (1 - (2 : ℂ) ^ (-s)))
    {β₁ : ℝ} (hβ₁lo : 19 / 20 ≤ β₁) (hβ₁hi : β₁ < 1) (hzero : Lam₁ (β₁ : ℂ) = 0)
    {C : ℝ} (hC : 1 ≤ C)
    (hbnd₁ : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s‖ ≤ C * (d₁ : ℝ) ^ (10 : ℕ))
    (hL4 : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s‖ ≤ C)
    (h2s : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖1 - (2 : ℂ) ^ (-s)‖ ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d₂ : ℕ), 1 ≤ d₂ → ∀ (chi₂ : GaussianInt → ℂ),
        (chi₂ 1 = 1) →
        (∀ z : GaussianInt, chi₂ z = star (chi₂ z)) →
        (∀ z w : GaussianInt, chi₂ (z * w) = chi₂ z * chi₂ w) →
        (∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1) →
        ∀ (Lam₂ : ℂ → ℂ), AnalyticOn ℂ Lam₂ Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam₂ s = Work.FITop4.Bridge.heckeArch d₂ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s) →
        ∀ (F : ℂ → ℂ), AnalyticOnNhd ℂ F (Metric.closedBall (2 : ℂ) (3 / 2)) →
        (∀ s : ℂ, 1 < s.re →
          F s = Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) →
        ∀ (K : ℝ), 1 ≤ K → ‖F 1‖ ≤ K →
        (∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
          ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s‖ ≤ C * (d₂ : ℝ) ^ (10 : ℕ)) →
        (∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
          ‖F s‖ ≤ C * ((d₁ * d₂ : ℕ) : ℝ) ^ (10 : ℕ)) →
        c * (1 - β₁) * K ^ (-(200 : ℝ))
            * (max (d₁ : ℝ) (d₂ : ℝ)) ^ (-(200 * (1 - β₁)))
          ≤ ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by
  classical
  set A : ℝ := (1 / 2) * ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C 1‖ *
      ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hcpos : 0 < (1 / 4) * C ^ (-(15 : ℝ)) / (A + 1) := by
    have h1 : 0 < C ^ (-(15 : ℝ)) := Real.rpow_pos_of_pos hCpos _
    have h2 : 0 < A + 1 := by linarith
    positivity
  refine ⟨(1 / 4) * C ^ (-(15 : ℝ)) / (A + 1), hcpos, ?_⟩
  intro d₂ h₂ chi₂ h1₂ hre₂ hmul₂ hb₂ Lam₂ hAn₂ hAgr₂ F hFan hFagr K hK hF1 hbnd₂ hbndF
  obtain ⟨Kz, hKzpos, hKzbd⟩ := Commons.NumberTheory.Zeta.riemannZeta_bound_sphere_two
  obtain ⟨hc1, hcnonneg, hcabs, hcid⟩ :=
    estermann_conv_facts h1₁ h1₂ hre₁ hre₂ hmul₁ hmul₂ hb₁ hb₂
  have hFser : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * estermannF d₁ d₂ Lam₁ Lam₂ F s
        = ∑' n : ℕ, (((Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
    intro s hs
    have hs0 : 0 < s.re := by linarith
    have harch₁ : Work.FITop4.Bridge.heckeArch d₁ 0 s ≠ 0 := (heckeArch_facts h₁).1 s hs0
    have hL₁ : Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s
        = Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s := by
      rw [Work.FIArea6Hecke.Lval, hAgr₁ s hs]
      exact mul_div_cancel_left₀ _ harch₁
    have harch₂ : Work.FITop4.Bridge.heckeArch d₂ 0 s ≠ 0 := (heckeArch_facts h₂).1 s hs0
    have hL₂ : Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s
        = Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s := by
      rw [Work.FIArea6Hecke.Lval, hAgr₂ s hs]
      exact mul_div_cancel_left₀ _ harch₂
    have hkey : riemannZeta s *
          ((1 - (2:ℂ) ^ (-s)) * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s)
        = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1:ℂ)) 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := by
      calc riemannZeta s *
            ((1 - (2:ℂ) ^ (-s)) * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s)
          = (riemannZeta s * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s *
              (1 - (2:ℂ) ^ (-s))) *
            (Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) := by ring
        _ = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1:ℂ)) 0 s *
            (Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) := by
              rw [← hζK s hs]
        _ = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1:ℂ)) 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := by ring
    calc riemannZeta s * estermannF d₁ d₂ Lam₁ Lam₂ F s
        = riemannZeta s *
            ((1 - (2:ℂ) ^ (-s)) * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) := by
          simp only [estermannF]
          rw [hL₁, hL₂, hFagr s hs]
      _ = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1:ℂ)) 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := hkey
      _ = ∑' n : ℕ, (((Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re : ℝ) : ℂ) * (n : ℂ) ^ (-s) :=
          (hcid s hs).symm
  have hfa := estermannF_analyticOnNhd_ball h₁ h₂ hAn₁ hAn₂ hFan
  have hfnb := estermannF_ball_bound_aux (le_trans zero_le_one hC) hbnd₁ hbnd₂ hbndF hL4 h2s
  have hD1 : (1:ℝ) ≤ ((d₁ * d₂ : ℕ) : ℝ) := by
    have h12 : (1:ℕ) ≤ d₁ * d₂ := by
      have := Nat.mul_le_mul h₁ h₂
      simpa using this
    exact_mod_cast h12
  have h5p : (1:ℝ) ≤ C ^ 5 := one_le_pow₀ hC
  have h20p : (1:ℝ) ≤ (((d₁ * d₂ : ℕ) : ℝ)) ^ (20:ℕ) := one_le_pow₀ hD1
  have hM1 : (1:ℝ) ≤ C ^ 5 * (((d₁ * d₂ : ℕ) : ℝ)) ^ (20:ℕ) := by
    simpa using (mul_le_mul h5p h20p (zero_le_one) (le_trans zero_le_one h5p))
  have hzetaσ : ∃ c : ℝ, c < 0 ∧ riemannZeta (β₁ : ℂ) = (c : ℂ) :=
    Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one (by linarith) hβ₁hi
  have hfσ : (0:ℝ) ≤ (estermannF d₁ d₂ Lam₁ Lam₂ F (β₁ : ℂ)).re := by
    have hz : estermannF d₁ d₂ Lam₁ Lam₂ F (β₁ : ℂ) = 0 := by
      simp [estermannF, Work.FIArea6Hecke.Lval, hzero]
    rw [hz]; simp
  have hr0 : ∀ n : ℕ, 0 ≤ (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : Work.FIArea5.S16Hecke.Conv chi₁ chi₂ 0 = 0 := by
        simp [Work.FIArea5.S16Hecke.Conv, LSeries.convolution_def]
      rw [h0]; simp
    · exact hcnonneg n hn
  have hc1r : (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ 1).re = 1 := by rw [hc1]; simp
  have hpos := Commons.NumberTheory.DirichletCharacter.estermann_positivity
    (f := estermannF d₁ d₂ Lam₁ Lam₂ F)
    (r := fun n => (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re)
    (M := C ^ 5 * (((d₁ * d₂ : ℕ) : ℝ)) ^ (20:ℕ)) (σ := β₁) (K := Kz)
    hKzpos hM1 hβ₁lo hβ₁hi hfa hfnb (fun z hz => hKzbd z hz) hzetaσ hr0 hc1r hcabs hFser hfσ
  have h1val : ‖(1:ℂ) - (2:ℂ) ^ (-(1:ℂ))‖ = 1/2 := by
    rw [show (-(1:ℂ)) = ((-1:ℤ):ℂ) by simp, Complex.cpow_intCast]
    norm_num
  have hnorm1 : ‖estermannF d₁ d₂ Lam₁ Lam₂ F 1‖
      = A * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * ‖F 1‖ := by
    rw [hAdef]
    show ‖(1 - (2:ℂ) ^ (-(1:ℂ))) * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C 1 *
        Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1 * Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1 * F 1‖
      = 1 / 2 * ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C 1‖ *
        ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * ‖F 1‖
    simp only [norm_mul, h1val]
  have hf1le : (estermannF d₁ d₂ Lam₁ Lam₂ F 1).re
      ≤ A * K * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by
    have hstep1 : (estermannF d₁ d₂ Lam₁ Lam₂ F 1).re
        ≤ ‖estermannF d₁ d₂ Lam₁ Lam₂ F 1‖ := Complex.re_le_norm _
    rw [hnorm1] at hstep1
    refine le_trans hstep1 ?_
    have hx0 : (0:ℝ) ≤ ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := norm_nonneg _
    have hAA : (0:ℝ) ≤ A * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by positivity
    calc A * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * ‖F 1‖
        ≤ A * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * K := mul_le_mul_of_nonneg_left hF1 hAA
      _ = A * K * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by ring
  have hmain : (1 / 4) * (1 - β₁) * (C ^ 5 * (((d₁ * d₂ : ℕ) : ℝ)) ^ (20:ℕ)) ^ (-(3 * (1 - β₁)))
      ≤ A * K * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := le_trans hpos hf1le
  have hm1 : (1:ℝ) ≤ max (d₁ : ℝ) (d₂ : ℝ) :=
    le_trans (by exact_mod_cast h₂) (le_max_right _ _)
  have hDm : (((d₁ * d₂ : ℕ) : ℝ)) ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 2 := by
    have hle1 : (d₁:ℝ) ≤ max (d₁:ℝ) (d₂:ℝ) := le_max_left _ _
    have hle2 : (d₂:ℝ) ≤ max (d₁:ℝ) (d₂:ℝ) := le_max_right _ _
    have h1' : (0:ℝ) ≤ (d₁:ℝ) := by positivity
    have h2' : (0:ℝ) ≤ (d₂:ℝ) := by positivity
    have hm0 : (0:ℝ) ≤ max (d₁:ℝ) (d₂:ℝ) := le_trans h1' hle1
    calc (((d₁ * d₂ : ℕ) : ℝ)) = (d₁:ℝ) * (d₂:ℝ) := by push_cast; ring
      _ ≤ max (d₁:ℝ) (d₂:ℝ) * max (d₁:ℝ) (d₂:ℝ) := mul_le_mul hle1 hle2 h2' hm0
      _ = (max (d₁ : ℝ) (d₂ : ℝ)) ^ 2 := by ring
  exact estermann_scaled_arith_aux hC hβ₁lo hβ₁hi hK hA0 (norm_nonneg _) hD1 hm1 hDm hmain




end Work.FIArea6Hecke.R
