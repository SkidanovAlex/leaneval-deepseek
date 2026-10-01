/-
# Area 4 / HB §12 — Condition 2 (`Re F ≥ 0` on the closed right half-plane) for the §7 test function
-/
import Mathlib
import Submission.Commons.Analysis.Complex.re_ge_norm_of_boundary
import Submission.Commons.Analysis.Complex.laplace_bound_two_sided
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.testfun_basic
import Submission.Work.LinnikAreas.Density4.testfun_conv
import Submission.Work.LinnikAreas.Density4.testfun_lapl_pos
import Submission.Work.LinnikAreas.Density4.testfun_laplace
import Submission.Work.LinnikAreas.Density4.fTregular
import Submission.Work.LinnikAreas.Density4.laplace_interval_differentiable
import Submission.Work.LinnikAreas.Density4.fT_laplace_axis_nonneg
import Submission.Work.LinnikAreas.Density4.fT_laplace_regularity

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Work.LinnikAreas.Density4

theorem fT_laplace_decay {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖∫ t in (0:ℝ)..(2 * gammaT θ lam),
        Complex.exp (-(z * (t : ℂ))) * ((fT θ lam t : ℝ) : ℂ)‖ < ε := by
  intro ε hε
  have hεne : ε ≠ 0 := ne_of_gt hε
  obtain ⟨hcont, hcd, B, hBnn, hBnd⟩ := fT_laplace_regularity (θ := θ) (lam := lam) hθ1 hθ2 hlam
  have h2γ : 0 < 2 * gammaT θ lam := by have h := gammaT_pos hθ1 hθ2 hlam; linarith
  set G : ℝ → ℂ := fun t => ((fT θ lam t : ℝ) : ℂ) with hGdef
  have hcontG : ContinuousOn G (Set.Icc 0 (2 * gammaT θ lam)) := by simpa [hGdef] using hcont
  have hcdG : ContDiffOn ℝ 2 G (Set.Ioo 0 (2 * gammaT θ lam)) := by simpa [hGdef] using hcd
  have hBndG : ∀ t ∈ Set.Ioo (0:ℝ) (2 * gammaT θ lam), ‖iteratedDeriv 2 G t‖ ≤ B := by
    intro t ht; simpa [hGdef] using hBnd t ht
  have hvan : ∀ t : ℝ, 2 * gammaT θ lam ≤ t → G t = 0 := by
    intro t ht
    simp only [hGdef]
    rw [fT_eq_zero_of_two_gammaT_le θ lam hθ1 hθ2 hlam t ht, Complex.ofReal_zero]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := G) hcontG
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, h2γ.le⟩)
  set D : ℝ := 2 * ‖derivWithin G (Set.Ioi 0) 0‖ + 2 * B * (2 * gammaT θ lam) with hDdef
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  have hb2 : ∀ z : ℂ, z ≠ 0 →
      ‖∫ t in (0:ℝ)..(2 * gammaT θ lam), Complex.exp (-(z * (t : ℂ))) * G t‖ ≤
        ‖G 0‖ / ‖z‖ + D * Real.exp ((2 * gammaT θ lam) * |z.re|) / ‖z‖ ^ 2 := by
    intro z hz
    have h := Commons.Analysis.Complex.laplace_bound_two_sided (x₀ := 2 * gammaT θ lam)
      (B := B) (f := G) h2γ hBnn hcontG hcdG hBndG hvan hz
    simpa only [hDdef] using h
  have hb1 : ∀ z : ℂ, 0 < z.re →
      ‖∫ t in (0:ℝ)..(2 * gammaT θ lam), Complex.exp (-(z * (t : ℂ))) * G t‖ ≤ M / z.re := by
    intro z hz
    have hbnd_cont : Continuous fun t : ℝ => M * Real.exp (-(z.re * t)) := by fun_prop
    have hbound_int : IntervalIntegrable (fun t : ℝ => M * Real.exp (-(z.re * t)))
        volume 0 (2 * gammaT θ lam) := hbnd_cont.intervalIntegrable _ _
    have hab : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0:ℝ) (2 * gammaT θ lam) →
        ‖Complex.exp (-(z * (t : ℂ))) * G t‖ ≤ M * Real.exp (-(z.re * t)) := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(z * (t : ℂ))).re = -(z.re * t) := by
        rw [Complex.neg_re, Complex.mul_re]; simp
      rw [hre]
      have hgt : ‖G t‖ ≤ M := hM t ⟨le_of_lt ht.1, ht.2⟩
      calc Real.exp (-(z.re * t)) * ‖G t‖ ≤ Real.exp (-(z.re * t)) * M :=
            mul_le_mul_of_nonneg_left hgt (Real.exp_nonneg _)
        _ = M * Real.exp (-(z.re * t)) := by ring
    have hmain := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (f := fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * G t)
      (g := fun t : ℝ => M * Real.exp (-(z.re * t))) h2γ.le hab hbound_int
    refine hmain.trans ?_
    have hI : (∫ t in (0:ℝ)..(2 * gammaT θ lam), M * Real.exp (-(z.re * t)))
        = M * ((1 - Real.exp (-(z.re * (2 * gammaT θ lam)))) / z.re) := by
      rw [intervalIntegral.integral_const_mul,
          integral_exp_neg_zero_T z.re (2 * gammaT θ lam) (ne_of_gt hz)]
    rw [hI]
    have hone : (1 - Real.exp (-(z.re * (2 * gammaT θ lam)))) ≤ 1 := by
      linarith [Real.exp_pos (-(z.re * (2 * gammaT θ lam)))]
    calc M * ((1 - Real.exp (-(z.re * (2 * gammaT θ lam)))) / z.re)
        ≤ M * (1 / z.re) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hone hz.le) hMnn
      _ = M / z.re := by ring
  set σ₁ : ℝ := M / ε + 1 with hσ₁def
  have hσ₁pos : 0 < σ₁ := by rw [hσ₁def]; have : 0 ≤ M / ε := div_nonneg hMnn hε.le; linarith
  set K : ℝ := Real.exp ((2 * gammaT θ lam) * σ₁) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; exact Real.exp_pos _
  set C : ℝ := ‖G 0‖ + D * K with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  refine ⟨max σ₁ (C / ε + 1), ?_⟩
  intro z hz hRz
  rcases le_total σ₁ z.re with h1 | h1
  · have hzpos : 0 < z.re := lt_of_lt_of_le hσ₁pos h1
    have hb := hb1 z hzpos
    have hMdiv : M / z.re ≤ M / σ₁ := div_le_div_of_nonneg_left hMnn hσ₁pos h1
    have hlt : M / σ₁ < ε := by
      rw [hσ₁def, div_lt_iff₀ (by have : 0 ≤ M / ε := div_nonneg hMnn hε.le; linarith)]
      have hsplit : ε * (M / ε + 1) = M + ε := by
        rw [mul_add, mul_one, mul_comm ε (M / ε), div_mul_cancel₀ M hεne]
      rw [hsplit]; linarith
    exact lt_of_le_of_lt (hMdiv.trans' hb) hlt
  · have hRpos : 0 < max σ₁ (C / ε + 1) := lt_of_lt_of_le hσ₁pos (le_max_left _ _)
    have hznorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hRz
    have hz0 : z ≠ 0 := norm_pos_iff.mp hznorm_pos
    have hRge : C / ε + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hRz
    have hnorm_ge_one : 1 ≤ ‖z‖ := by
      have h2 : (1:ℝ) ≤ C / ε + 1 := by have : 0 ≤ C / ε := div_nonneg hCnn hε.le; linarith
      linarith
    have hb := hb2 z hz0
    have hσabs : |z.re| = z.re := abs_of_nonneg hz
    have hexp : Real.exp ((2 * gammaT θ lam) * |z.re|) ≤ K := by
      rw [hKdef, hσabs]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1 h2γ.le)
    have hstep : ‖∫ t in (0:ℝ)..(2 * gammaT θ lam), Complex.exp (-(z * (t : ℂ))) * G t‖
        ≤ C / ‖z‖ := by
      have h2' : D * Real.exp ((2 * gammaT θ lam) * |z.re|) / ‖z‖ ^ 2 ≤ D * K / ‖z‖ ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hDnn) (by positivity)
      have h3' : D * K / ‖z‖ ^ 2 ≤ D * K / ‖z‖ := by
        refine div_le_div_of_nonneg_left (by positivity) hznorm_pos ?_
        nlinarith [hnorm_ge_one]
      have h4' : ‖G 0‖ / ‖z‖ + D * K / ‖z‖ = C / ‖z‖ := by rw [hCdef]; ring
      linarith
    have hfinal : C / ‖z‖ < ε := by
      have hden : 0 < C / ε + 1 := by have : 0 ≤ C / ε := div_nonneg hCnn hε.le; linarith
      have hle : C / ‖z‖ ≤ C / (C / ε + 1) := div_le_div_of_nonneg_left hCnn hden hRge
      have hlt : C / (C / ε + 1) < ε := by
        rw [div_lt_iff₀ hden]
        have hsplit : ε * (C / ε + 1) = C + ε := by
          rw [mul_add, mul_one, mul_comm ε (C / ε), div_mul_cancel₀ C hεne]
        rw [hsplit]; linarith
      linarith
    linarith [hstep, hfinal]

theorem fTcond2 {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..(2 * gammaT θ lam),
            Complex.exp (-(z * (t : ℂ))) * ((fT θ lam t : ℝ) : ℂ)).re := by
  intro z hz
  have h2γ : 0 < 2 * gammaT θ lam := by have h := gammaT_pos hθ1 hθ2 hlam; linarith
  set L : ℂ → ℂ := fun w => ∫ t in (0:ℝ)..(2 * gammaT θ lam),
      Complex.exp (-(w * (t : ℂ))) * ((fT θ lam t : ℝ) : ℂ) with hLdef
  have hgc : ContinuousOn (fun t : ℝ => ((fT θ lam t : ℝ) : ℂ)) (Set.uIcc 0 (2 * gammaT θ lam)) := by
    obtain ⟨hcont, -, -, -⟩ := fT_laplace_regularity (θ := θ) (lam := lam) hθ1 hθ2 hlam
    rw [Set.uIcc_of_le h2γ.le]
    exact hcont
  have hdL : Differentiable ℂ L := by
    have h := laplace_interval_differentiable (a := (0:ℝ)) (b := 2 * gammaT θ lam)
      (g := fun t : ℝ => ((fT θ lam t : ℝ) : ℂ)) hgc
    simpa only [hLdef] using h
  have hbd : ∀ t : ℝ, 0 ≤ (L (Complex.I * (t : ℂ))).re := by
    intro t
    simp only [hLdef]
    exact fT_laplace_axis_nonneg (θ := θ) (lam := lam) hθ1 hθ2 hlam t
  have hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, 0 ≤ w.re → R ≤ ‖w‖ →
      ‖L w‖ < ε ∧ ‖(0:ℂ)‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := fT_laplace_decay (θ := θ) (lam := lam) hθ1 hθ2 hlam ε hε
    refine ⟨R, fun w hw hRw => ⟨?_, ?_⟩⟩
    · simp only [hLdef]; exact hR w hw hRw
    · rw [norm_zero]; exact hε
  have hmain := Commons.Analysis.Complex.re_ge_norm_of_boundary (F1 := L) (F2 := fun _ : ℂ => 0)
    hdL.differentiableOn (differentiableOn_const 0)
    hdL.continuous.continuousOn continuous_const.continuousOn
    (fun t => by simpa using hbd t) hdec z hz
  rw [norm_zero] at hmain
  simpa only [hLdef] using hmain

end Work.LinnikAreas.Density4
