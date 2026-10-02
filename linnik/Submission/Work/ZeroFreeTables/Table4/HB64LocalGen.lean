import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.dhTrianglePtLocal
import Submission.Work.ZeroFreeTables.Table4.windowSumGe

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

namespace Work.ZeroFreeTables.Table4

open Commons.NumberTheory.Linnik

theorem HB64LocalGen (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ * χ = 1) [NeZero χ.conductor]
        {β₁ β' : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ' : |1 - β'| ≤ δ) (hβ'β₁ : β' ≤ β₁)
        (hβ₁le : β₁ ≤ 1) (hβ'le : β' ≤ 1)
        (hβ'pt : |1 - β'| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hne : (β' : ℂ) ≠ (β₁ : ℂ))
        (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 2)) (β₁ : ℂ) ≠ 0)
        (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 2)) (β' : ℂ) ≠ 0)
        (hmult' : (1 : ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 2)) (β' : ℂ))
        (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
            |u.im| ≤ 1 → u = (β₁ : ℂ) ∨ u.re ≤ β')
        (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (2 * c + 4 * ε) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn ε hε δ hδ0 hδ1
  obtain ⟨q₀p, hq₀p⟩ := (Ksum_principal_le_complex x₀ B hx₀ hB) hcont hsupp hf2 hBnd
    (by positivity : (0:ℝ) < ε/2) hf0
  obtain ⟨q₀χ, hq₀χ⟩ := (lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨max (max q₀p q₀χ) 6, ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ β' hβ₁ hβ' hβ'β₁ hβ₁le hβ'le hβ'pt hne
    hdiv₁ hdiv' hmult' hmax H
  have hqp : q₀p ≤ q := by omega
  have hqχ : q₀χ ≤ q := by omega
  have hlogq : (0 : ℝ) < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) := le_of_lt hlogq
  have hlogq1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < q))]
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 3 ≤ q)
    linarith [Real.exp_one_lt_three]
  have Hraw : ∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
      (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
            (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
        ≤ (c + ε/4) * Real.log (q : ℝ) := H
  have hramβ' : |β' - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_sub_comm]
    exact hβ'pt
  have hloβ' : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ β' := by
    have h : 1 - β' ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      (abs_le.mp hβ'pt).2
    linarith
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hrad : (|((β' : ℂ)).im| : ℝ) + 2 = 2 := by simp
  have hintF : ∀ z : ℂ, IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)) volume (0:ℝ) x₀ := by
    intro z
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx₀.le]
    have h1 : Continuous (fun t : ℝ => Complex.exp (-(z * (t : ℂ)))) :=
      Complex.continuous_exp.comp (((continuous_const : Continuous fun _ : ℝ => z).mul
        Complex.continuous_ofReal).neg)
    have h2 : ContinuousOn (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Icc 0 x₀) :=
      Complex.continuous_ofReal.comp_continuousOn (hcont.mono Set.Icc_subset_Ici_self)
    exact h1.continuousOn.mul h2
  -- ### the (6.13)-sharpened two-term window bound at `s = β'`
  have hwinρ : ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ := by
    have h1 : (1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ) = ((1 - β₁ : ℝ) : ℂ) := by
      simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    exact hβ₁
  have hwinσ : ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β' : ℂ)‖ ≤ δ := by
    have h1 : (1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β' : ℂ) = ((1 - β' : ℝ) : ℂ) := by
      simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    exact hβ'
  have hρnn : 0 ≤ ((∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
        ((f t : ℝ) : ℂ)).re) := by
    have hpt : ∀ t : ℝ, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)
        = ((Real.exp (-(((β' - β₁) * Real.log (q : ℝ)) * t)) * f t : ℝ) : ℂ) := by
      intro t
      have h1 : -((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))
          = ((-(((β' - β₁) * Real.log (q : ℝ)) * t) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    simp only [hpt]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    apply intervalIntegral.integral_nonneg hx₀.le
    intro t _
    exact mul_nonneg (Real.exp_nonneg _) (hfnn t)
  have hzero' : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u ≠ (β' : ℂ) →
      u.re ≤ (β' : ℂ).re := by
    have hwin1 : |((β' : ℂ)).im| + δ ≤ 1 := by
      have him0 : ((β' : ℂ)).im = 0 := by simp
      rw [him0, abs_zero, zero_add]
      linarith [hδ1]
    have h := window_hzero_of_Lzero_local χ.primitiveCharacter hχ' (K := 1)
      (A := β') (δ := δ) (s := (β' : ℂ)) (σ := (β₁ : ℂ)) hδ1 hwin1 (le_of_eq rfl) hmax
    intro u hu hw hne1 _
    exact h u hu hw hne1
  have hσint : (∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β' : ℂ) - (β' : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
        ((f t : ℝ) : ℂ)).re = ∫ t in (0:ℝ)..x₀, f t := by
    simp only [sub_self, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have hσnn : 0 ≤ (∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β' : ℂ) - (β' : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
        ((f t : ℝ) : ℂ)).re := by
    rw [hσint]
    exact intervalIntegral.integral_nonneg hx₀.le (fun t _ => hfnn t)
  have hkey : ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re)
      + (∫ t in (0:ℝ)..x₀, f t)
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀,
            Complex.exp (-((((β' : ℂ) - u) * (Real.log (q : ℝ))) * (t : ℂ))) *
              ((f t : ℝ) : ℂ)).re) else 0) := by
    have h := windowSumGe (χ := χ.primitiveCharacter) hχ' (f := f) (x₀ := x₀)
      (L := Real.log (q : ℝ)) (C := 0) (s := (β' : ℂ)) (ρ := (β₁ : ℂ)) (σ := (β' : ℂ))
      (δ := δ) hLnn hFnn (fun h => hne h.symm) le_rfl
      (by rw [hrad]; exact hdiv₁) hwinρ hρnn
      (by rw [hrad]; exact hmult') hσnn (Or.inl hwinσ) hzero'
    rw [hσint] at h
    linarith [h]
  -- ### the two K-sum bounds
  have hbχ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (β' : ℂ)).re) * f (Real.log n / Real.log (q : ℝ)))
      ≤ -(Real.log (q : ℝ)) * (((∫ t in (0:ℝ)..x₀,
            Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
              ((f t : ℝ) : ℂ)).re)
          + (∫ t in (0:ℝ)..x₀, f t))
        + f 0 * (c + ε) * Real.log (q : ℝ) := by
    have h := hq₀χ hqχ χ hχ Hraw (β' : ℂ)
      (by simp only [Complex.ofReal_re]; exact hramβ')
      (by simp only [Complex.ofReal_im, abs_zero]; linarith [hlogq])
      (by simp only [Complex.ofReal_re]; exact hloβ')
    have h3 := mul_le_mul_of_nonneg_left hkey hLnn
    linarith only [h, h3]
  have hp : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β' : ℂ)).re *
        f (Real.log n / Real.log (q : ℝ)))
      ≤ (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((β' : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re + f 0 * (ε/2) * Real.log (q : ℝ) := by
    have h := hq₀p hqp (β := β') (γ := 0) hramβ'
      (by simp only [abs_zero]; exact hLnn)
    simpa using h
  have hpos := Ksum_positivity_real (q := q) (f := f) (β := β') (γ := 0)
    hfnn hx₀ hlogq hsupp χ hreal
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hpos
  have hAeq : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β' : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re
      = (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t) := by
    rw [re_laplace_eq (hintF (((β' : ℂ) - 1) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : (((β' : ℂ) - 1)).im = 0 := by simp
    have hr : (((β' : ℂ) - 1)).re = β' - 1 := by simp
    rw [re_mul_log ((β' : ℂ) - 1) q, im_mul_log ((β' : ℂ) - 1) q, hr, ha]
    simp only [zero_mul, Real.cos_zero, mul_one]
    congr 1
    ring
  have hCeq : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re
      = (∫ t in (0:ℝ)..x₀,
          Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t) := by
    rw [re_laplace_eq (hintF (((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : (((β' : ℂ) - (β₁ : ℂ))).im = 0 := by simp
    have hr : (((β' : ℂ) - (β₁ : ℂ))).re = β' - β₁ := by simp
    rw [re_mul_log ((β' : ℂ) - (β₁ : ℂ)) q, im_mul_log ((β' : ℂ) - (β₁ : ℂ)) q, hr, ha]
    simp only [zero_mul, Real.cos_zero, mul_one]
    congr 1
    ring
  rw [hAeq] at hp
  rw [hCeq] at hbχ
  have hsum : 0 ≤ (Real.log (q : ℝ)) *
        ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
          - (∫ t in (0:ℝ)..x₀,
              Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
          - (∫ t in (0:ℝ)..x₀, f t)
          + f 0 * (c + 3*ε/2)) := by
    have h0 : (0:ℝ) ≤ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β' : ℂ)).re
          * f (Real.log n / Real.log (q : ℝ)))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ (n : ZMod q) / (n : ℂ) ^ (β' : ℂ)).re * f (Real.log n / Real.log (q : ℝ))) := by
      linarith only [hpos]
    have key : (0:ℝ) ≤ (Real.log (q : ℝ)) *
          ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
            - (∫ t in (0:ℝ)..x₀,
                Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
            - (∫ t in (0:ℝ)..x₀, f t))
        + f 0 * (c + 3*ε/2) * Real.log (q : ℝ) := by
      linarith only [h0, hp, hbχ]
    have hfac : (Real.log (q : ℝ)) *
          ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
            - (∫ t in (0:ℝ)..x₀,
                Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
            - (∫ t in (0:ℝ)..x₀, f t))
        + f 0 * (c + 3*ε/2) * Real.log (q : ℝ)
        = (Real.log (q : ℝ)) *
          ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
            - (∫ t in (0:ℝ)..x₀,
                Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
            - (∫ t in (0:ℝ)..x₀, f t)
            + f 0 * (c + 3*ε/2)) := by ring
    rwa [hfac] at key
  have hres : 0 ≤ (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
        - (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 3*ε/2) :=
    (mul_nonneg_iff_of_pos_left hlogq).mp hsum
  nlinarith [hres, hf0, hε]

end Work.ZeroFreeTables.Table4
