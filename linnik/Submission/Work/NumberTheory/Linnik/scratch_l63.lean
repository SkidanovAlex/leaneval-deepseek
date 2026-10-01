import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.NumberTheory.Linnik.scratch_kprinc_c
import Submission.Work.NumberTheory.Linnik.scratch_kpos_real
import Submission.Work.NumberTheory.Linnik.scratch_cosint
import Submission.Work.NumberTheory.Linnik.scratch_reF

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Linnik

/-- The window sum of Heath-Brown §6 for a character `χ`, at the point `s`, with radius `δ` and
scale `L`. -/
noncomputable def winSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ)
    (x₀ L δ : ℝ) (s : ℂ) : ℝ :=
  ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
    (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
      ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      else 0)

/-- `∫₀^{x₀} e^{-(a t)} f(t) dt` for real `a`, as the real part of the complex Laplace integral. -/
theorem re_laplace_real {x₀ a : ℝ} {f : ℝ → ℝ}
    (hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(((a : ℂ)) * (t : ℂ))) * ((f t : ℝ) : ℂ)) volume (0:ℝ) x₀) :
    (∫ t in (0:ℝ)..x₀, Complex.exp (-(((a : ℂ)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..x₀, Real.exp (-(a * t)) * f t := by
  rw [re_laplace_eq hint]
  apply intervalIntegral.integral_congr
  intro t _
  simp

/-- Real part of `a * log q`. -/
lemma re_mul_log (a : ℂ) (q : ℕ) :
    (a * (Real.log (q : ℝ))).re = a.re * Real.log (q : ℝ) := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Imaginary part of `a * log q`. -/
lemma im_mul_log (a : ℂ) (q : ℕ) :
    (a * (Real.log (q : ℝ))).im = a.im * Real.log (q : ℝ) := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

/-- **Heath-Brown Lemma 6.3** (§6), in the form in which it is used in §8.

For a **real** character `χ` (i.e. `χ * χ = 1`) and a real zero `ρ₁ = β₁` and a zero
`ρ' = β' + iγ'` of `L(·,χ)` with `β'` maximal, and `f` satisfying Conditions 1 and 2,

`2F(-λ') - 2F(λ₁-λ') - F(0) + f(0)(2c + 4ε) ≥ 0`

where `c` is the constant of Lemma 5.2 for `χ` (i.e. the hypothesis bound `(c+ε/4)log q`) — for a
real `χ` one takes `c = 1/8`, so `2c = 1/4` as in the paper.

The two hypotheses `hw13` and `hw15` are the two window-sum lower bounds of the paper:
`hw13` is (6.13) (the single contribution of `ρ₁`, which follows from
`le_windowSum_of_mem_ne` + `laplace_re_nonneg`), and `hw15` is (6.14)+(6.15) (the joint
contribution of `ρ'` and `ρ₁`, with the `O(L^{-1})` slack of (6.14) written as `f(0)εL`; the
`O(L^{-1})` bound itself is `laplace_bound_two_sided`). -/
theorem lemma6_3 (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ * χ = 1) [NeZero χ.conductor]
        {β₁ β' γ' : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ' : |1 - β'| ≤ δ) (hβ'β₁ : β' ≤ β₁)
        (hβ₁le : β₁ ≤ 1) (hβ'le : β' ≤ 1)
        (hγ' : |γ'| ≤ Real.log (q : ℝ))
        (hδle : δ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hzero₁ : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0)
        (hzero' : DirichletCharacter.LFunction χ ((β' : ℂ) + (γ' : ℂ) * Complex.I) = 0)
        (H : L52Hyp χ c ε δ)
        (hw13 : ((∫ t in (0:ℝ)..x₀,
              Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
                ((f t : ℝ) : ℂ)).re)
            ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (β' : ℂ))
        (hw15 : ((∫ t in (0:ℝ)..x₀,
                Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
                  ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
                  ((f t : ℝ) : ℂ)).re)
              + ((∫ t in (0:ℝ)..x₀,
                Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
                  (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
              - f 0 * ε
            ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ
                ((β' : ℂ) + (γ' : ℂ) * Complex.I)),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (2 * c + 4 * ε) := by

  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn ε hε δ hδ0 hδ1
  obtain ⟨q₀p, hq₀p⟩ := (Ksum_principal_le_complex x₀ B hx₀ hB) hcont hsupp hf2 hBnd
    (by positivity : (0:ℝ) < ε/2) hf0
  obtain ⟨q₀χ, hq₀χ⟩ := (lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨max (max q₀p q₀χ) 6, ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ β' γ' hβ₁ hβ' hβ'β₁ hβ₁le hβ'le hγ' hδle hzero₁ hzero' H hw13 hw15
  have hqp : q₀p ≤ q := by omega
  have hqχ : q₀χ ≤ q := by omega
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
  have hs₁re : ((β' : ℂ)).re = β' := by simp
  have hs₁im : ((β' : ℂ)).im = 0 := by simp
  have hs₂re : (((β' : ℂ) + (γ' : ℂ) * Complex.I)).re = β' := by simp
  have hs₂im : (((β' : ℂ) + (γ' : ℂ) * Complex.I)).im = γ' := by simp
  have hranβ' : |β' - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h : |1 - β'| ≤ δ := hβ'
    rw [abs_sub_comm] at h ⊢
    linarith [h, hδle]
  have hlowβ' : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ β' := by
    have h : 1 - β' ≤ δ := (abs_le.mp hβ').2
    linarith [h, hδle]
  have him2 : |γ'| ≤ 10 * Real.log (q : ℝ) := by linarith [hγ', hlogq]
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
  -- (a) the two Lemma 5.2 applications
  have hbχ₁ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (β' : ℂ)).re) * f (Real.log n / Real.log (q : ℝ)))
      ≤ -(Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + f 0 * (c + ε) * Real.log (q : ℝ) := by
    have h := hq₀χ hqχ χ hχ Hraw (β' : ℂ)
      (by rw [hs₁re]; exact hranβ')
      (by rw [hs₁im]; simp only [abs_zero]; linarith [hlogq])
      (by rw [hs₁re]; exact hlowβ')
    have h2 : (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (β' : ℂ) := hw13
    have h3 := mul_le_mul_of_nonneg_left h2 hLnn
    simp only [winSum] at h3
    linarith only [h, h3]
  have hbχ₂ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (((β' : ℂ) + (γ' : ℂ) * Complex.I))).re) * f (Real.log n / Real.log (q : ℝ)))
      ≤ -(Real.log (q : ℝ)) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) + f 0 * (c + 2*ε) * Real.log (q : ℝ) := by
    have h := hq₀χ hqχ χ hχ Hraw (((β' : ℂ) + (γ' : ℂ) * Complex.I))
      (by rw [hs₂re]; exact hranβ')
      (by rw [hs₂im]; exact him2)
      (by rw [hs₂re]; exact hlowβ')
    have hh : (∫ t in (0:ℝ)..x₀, Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - f 0 * ε ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (((β' : ℂ) + (γ' : ℂ) * Complex.I)) := by
      simpa only [sub_self, zero_mul, neg_zero, Complex.exp_zero, one_mul] using hw15
    have h3 := mul_le_mul_of_nonneg_left hh hLnn
    simp only [winSum] at h3
    linarith only [h, h3]
  -- (b) the principal character via Lemma 5.3
  have hp₁ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β' : ℂ)).re *
        f (Real.log n / Real.log (q : ℝ)))
      ≤ (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + f 0 * (ε/2) * Real.log (q : ℝ) := by
    have h := hq₀p hqp (β := β') (γ := 0) hranβ'
      (by simp only [abs_zero]; exact hLnn)
    simpa using h
  have hp₂ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (((β' : ℂ) + (γ' : ℂ) * Complex.I))).re *
        f (Real.log n / Real.log (q : ℝ)))
      ≤ (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + f 0 * (ε/2) * Real.log (q : ℝ) := by
    have h := hq₀p hqp (β := β') (γ := γ') hranβ' hγ'
    simpa using h
  have hpos := Ksum_positivity_real (q := q) (f := f) (β := β') (γ := γ') hfnn hx₀ hlogq hsupp χ hreal
  -- (c) the sum
  have hZkey : 0 ≤ (Real.log (q : ℝ)) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      + f 0 * (2 * c + 4 * ε) * Real.log (q : ℝ) := by
    linarith only [hpos, hbχ₁, hbχ₂, hp₁, hp₂]
  have hdiv : 0 ≤ ((∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) + f 0 * (2 * c + 4 * ε) := by
    have hfac : (Real.log (q : ℝ)) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        + f 0 * (2 * c + 4 * ε) * Real.log (q : ℝ)
        = (Real.log (q : ℝ)) * (((∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re + (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) + f 0 * (2 * c + 4 * ε)) := by
      ring
    rw [hfac] at hZkey
    exact (mul_nonneg_iff_of_pos_left hlogq).mp hZkey
  -- (d) convert the five integrals
  have hA : (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re = (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t) := by
    rw [re_laplace_eq (hintF (((β' : ℂ) - 1) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : (((β' : ℂ) - 1)).im = 0 := by simp
    have hr : (((β' : ℂ) - 1)).re = β' - 1 := by simp
    rw [re_mul_log ((β' : ℂ) - 1) q, im_mul_log ((β' : ℂ) - 1) q, hr, ha]
    simp only [zero_mul, Real.cos_zero, mul_one]
    congr 1
    · congr 1
      ring
  have hC : (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re = (∫ t in (0:ℝ)..x₀, Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t) := by
    rw [re_laplace_eq (hintF (((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : (((β' : ℂ) - (β₁ : ℂ))).im = 0 := by simp
    have hr : (((β' : ℂ) - (β₁ : ℂ))).re = β' - β₁ := by simp
    rw [re_mul_log ((β' : ℂ) - (β₁ : ℂ)) q, im_mul_log ((β' : ℂ) - (β₁ : ℂ)) q, hr, ha]
    simp only [zero_mul, Real.cos_zero, mul_one]
    congr 1
    · congr 1
      ring
  have hD : (∫ t in (0:ℝ)..x₀, Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re = ∫ t in (0:ℝ)..x₀, f t := by
    simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have hB : (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re = (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * Real.cos ((γ' * Real.log (q : ℝ)) * t) * f t) := by
    rw [re_laplace_eq (hintF ((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : ((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1)).im = γ' := by simp
    have hr : ((((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1)).re = β' - 1 := by simp
    rw [re_mul_log (((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) q, im_mul_log (((β' : ℂ) + (γ' : ℂ) * Complex.I) - 1) q, hr, ha]
    congr 2
    · congr 1
      ring
  have hE : (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re = (∫ t in (0:ℝ)..x₀, Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * Real.cos ((γ' * Real.log (q : ℝ)) * t) * f t) := by
    rw [re_laplace_eq (hintF ((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : ((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ))).im = γ' := by simp
    have hr : ((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ))).re = β' - β₁ := by simp
    rw [re_mul_log (((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) q, im_mul_log (((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) q, hr, ha]
    congr 2
    · congr 1
      ring
  rw [hA, hB, hC, hD, hE] at hdiv
  -- (e) the cos inequality and the final assembly
  have hcosle : (∫ t in (0:ℝ)..x₀,
            Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) *
              Real.cos ((γ' * Real.log (q : ℝ)) * t) * f t) - (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) *
              Real.cos ((γ' * Real.log (q : ℝ)) * t) * f t) ≤ ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t) - (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)) := by
    have hlim : (0:ℝ) ≤ Real.log (q : ℝ) * (1 - β₁) := mul_nonneg hLnn (by linarith)
    have hc1 : ContinuousOn (fun t : ℝ => Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
        (Set.Icc 0 x₀) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul (hcont.mono Set.Icc_subset_Ici_self)
    have hc2 : ContinuousOn (fun t : ℝ =>
        Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
        (Set.Icc 0 x₀) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul (hcont.mono Set.Icc_subset_Ici_self)
    have hn1 : ∀ t ∈ Set.Icc (0:ℝ) x₀,
        0 ≤ Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t :=
      fun t _ => mul_nonneg (Real.exp_nonneg _) (hfnn t)
    have hn2 : ∀ t ∈ Set.Icc (0:ℝ) x₀,
        0 ≤ Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t :=
      fun t _ => mul_nonneg (Real.exp_nonneg _) (hfnn t)
    have hle : ∀ t ∈ Set.Icc (0:ℝ) x₀,
        Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t
          ≤ Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t := by
      intro t ht
      have hexp : Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t)
          ≤ Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) := by
        apply Real.exp_le_exp.mpr
        nlinarith [ht.1, hlim]
      exact mul_le_mul_of_nonneg_right hexp (hfnn t)
    have h := integral_cos_sub_le (x₀ := x₀) (c := γ' * Real.log (q : ℝ)) hx₀ hc1 hc2 hn1 hn2 hle
    have e1 : (∫ t in (0:ℝ)..x₀,
          (fun t : ℝ => Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t) t *
            Real.cos ((γ' * Real.log (q : ℝ)) * t))
        = (∫ t in (0:ℝ)..x₀,
            Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) *
              Real.cos ((γ' * Real.log (q : ℝ)) * t) * f t) := by
      apply intervalIntegral.integral_congr
      intro t _; ring
    have e2 : (∫ t in (0:ℝ)..x₀,
          (fun t : ℝ => Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t)
              * f t) t * Real.cos ((γ' * Real.log (q : ℝ)) * t))
        = (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) *
              Real.cos ((γ' * Real.log (q : ℝ)) * t) * f t) := by
      apply intervalIntegral.integral_congr
      intro t _; ring
    rw [e1, e2] at h
    exact h
  linarith only [hdiv, hcosle]

end Commons.NumberTheory.Linnik
