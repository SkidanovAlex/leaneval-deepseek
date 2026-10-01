import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l63
import Submission.Work.NumberTheory.Linnik.scratch_l52phi_imprim
import Submission.Work.NumberTheory.Linnik.scratch_kpos_real
import Submission.Work.LinnikAreas.lemma6_3_wide
import Submission.Work.LinnikAreas.principalKsumWide

open scoped BigOperators
open MeasureTheory

namespace Work.ZeroFreeTables

/-- **HB §6/§8, repeated-zero case.**  With HB's Conditions 1–2 on the test function `f`,
a real non-principal character `χ`, a real `β₁` in the §6 region, and the window-sum
hypothesis `winSum χ* ≥ 2F(0)` encoding that the window at `β₁` carries a zero of
multiplicity `≥ 2`, one has
`2F(−λ₁) − 4F(0) + f(0)(2c + 3ε) ≥ 0`, `λ₁ = (1 − β₁) log q`.

Proof (HB §6, "`ρ⁰ = ρ₁` repeated"): Lemma 5.2 at `s = β₁` gives
`K(β₁,χ) ≤ −L·winSum(β₁) + f(0)(c+ε)L` and the window hypothesis bounds
`winSum(β₁) ≥ 2F(0)`; Lemma 5.3 (the principal character, `Ksum_principal_le_complex`)
gives `K(β₁,χ₀) ≤ L·F(−λ₁) + f(0)(ε/2)L`; and (6.11)
(`Ksum_positivity_real`) says `K(β₁,χ₀) + K(β₁,χ) ≥ 0`.  Adding and dividing by
`L = log q > 0` yields `F(−λ₁) − 2F(0) + f(0)(c + 3ε/2) ≥ 0`; doubling gives the claim. -/
theorem hb6Repeated {x₀ B c ε δ : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ * χ = 1) [NeZero χ.conductor]
        {β₁ : ℝ} (hβ₁ : |1 - β₁| ≤ δ)
        (hpt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ)
        (hwin : 2 * (∫ t in (0:ℝ)..x₀, f t) ≤
            Commons.NumberTheory.Linnik.winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (β₁ : ℂ)),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
          - 4 * (∫ t in (0:ℝ)..x₀, f t)
          + f 0 * (2 * c + 3 * ε) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn
  obtain ⟨q₀p, hq₀p⟩ := (Commons.NumberTheory.Linnik.Ksum_principal_le_complex x₀ B hx₀ hB)
    hcont hsupp hf2 hBnd (show (0:ℝ) < ε/2 by linarith) hf0
  obtain ⟨q₀χ, hq₀χ⟩ :=
    (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
      hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨max (max q₀p q₀χ) 6, ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ hβ₁ hpt H hwin
  have hq6 : 6 ≤ q := le_trans (le_max_right _ _) hq
  have hqp : q₀p ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqχ : q₀χ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hlogq : (0 : ℝ) < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) := le_of_lt hlogq
  have Hraw : ∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
      (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
            (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
        ≤ (c + ε/4) * Real.log (q : ℝ) := H
  have hβ₁rad : |β₁ - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_sub_comm]; exact hpt
  have hβ₁lo : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ β₁ := by
    have h : 1 - β₁ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      (abs_le.mp hpt).2
    linarith
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
  -- ### Lemma 5.2 at `s = β₁`, using the repeated-zero window hypothesis
  have hbχ_raw := hq₀χ hqχ χ hχ Hraw (β₁ : ℂ)
      (by simpa using hβ₁rad)
      (by simp only [Complex.ofReal_im, abs_zero]; linarith [hlogq])
      (by simpa using hβ₁lo)
  have hbχ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re) * f (Real.log n / Real.log (q : ℝ)))
      ≤ -(Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t))
        + f 0 * (c + ε) * Real.log (q : ℝ) := by
    have h2 : (2 : ℝ) * (∫ t in (0:ℝ)..x₀, f t) ≤
        Commons.NumberTheory.Linnik.winSum χ.primitiveCharacter f x₀
          (Real.log (q : ℝ)) δ (β₁ : ℂ) := hwin
    have h3 := mul_le_mul_of_nonneg_left h2 hLnn
    simp only [Commons.NumberTheory.Linnik.winSum] at h3
    linarith only [hbχ_raw, h3]
  -- ### the principal-character bound of Lemma 5.3 at `s = β₁`
  have hp : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re *
        f (Real.log n / Real.log (q : ℝ)))
      ≤ (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((β₁ : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re
        + f 0 * (ε/2) * Real.log (q : ℝ) := by
    have h := hq₀p hqp (β := β₁) (γ := 0) hβ₁rad (by simp only [abs_zero]; exact hLnn)
    simpa using h
  -- ### positivity (6.11)
  have hpos := Commons.NumberTheory.Linnik.Ksum_positivity_real (q := q) (f := f)
    (β := β₁) (γ := 0) hfnn hx₀ hlogq hsupp χ hreal
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hpos
  have h0 : (0 : ℝ) ≤ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re *
        f (Real.log n / Real.log (q : ℝ)))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re * f (Real.log n / Real.log (q : ℝ))) := by
    linarith only [hpos]
  -- ### combine
  have hsum : 0 ≤ (Real.log (q : ℝ)) *
      ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((β₁ : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re
        - 2 * (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (c + 3*ε/2)) := by
    have key : (0 : ℝ) ≤ (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((β₁ : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re
        + f 0 * (ε/2) * Real.log (q : ℝ)
        - (Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t))
        + f 0 * (c + ε) * Real.log (q : ℝ) := by
      linarith only [h0, hp, hbχ]
    have hfac : (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((β₁ : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re
        + f 0 * (ε/2) * Real.log (q : ℝ)
        - (Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t))
        + f 0 * (c + ε) * Real.log (q : ℝ)
        = (Real.log (q : ℝ)) *
          ((∫ t in (0:ℝ)..x₀,
              Complex.exp (-((((β₁ : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
                ((f t : ℝ) : ℂ)).re
            - 2 * (∫ t in (0:ℝ)..x₀, f t)
            + f 0 * (c + 3*ε/2)) := by ring
    rw [hfac] at key
    exact key
  have hres : 0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β₁ : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re
      - 2 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 3*ε/2) :=
    (mul_nonneg_iff_of_pos_left hlogq).mp hsum
  -- ### identify the real part of the Laplace integral
  have hAeq : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β₁ : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re
      = (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t) := by
    rw [Commons.NumberTheory.Linnik.re_laplace_eq
      (hintF (((β₁ : ℂ) - 1) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : (((β₁ : ℂ) - 1)).im = 0 := by simp
    have hr : (((β₁ : ℂ) - 1)).re = β₁ - 1 := by simp
    rw [Commons.NumberTheory.Linnik.re_mul_log ((β₁ : ℂ) - 1) q,
      Commons.NumberTheory.Linnik.im_mul_log ((β₁ : ℂ) - 1) q, hr, ha]
    simp only [zero_mul, Real.cos_zero, mul_one]
    congr 1
    ring
  rw [hAeq] at hres
  have h2 : 0 ≤ 2 * ((∫ t in (0:ℝ)..x₀,
        Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
      - 2 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 3*ε/2)) := by linarith [hres]
  have h3 : 2 * ((∫ t in (0:ℝ)..x₀,
        Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
      - 2 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 3*ε/2))
      = 2 * (∫ t in (0:ℝ)..x₀,
          Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
        - 4 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (2 * c + 3 * ε) := by ring
  linarith [h2, h3]

end Work.ZeroFreeTables
