/-
# The `§6` point-condition triangle inequality with a *free* height parameter

This file provides `Work.LinnikAreas.DhRepel.dhTrianglePtH`, a variant of
`Work.LinnikAreas.DhRepel.dhTrianglePt` (and of `Work.LinnikAreas.OtherCharRepel.dhTrianglePtLocal`)
in which the height cut-off of the maximality hypothesis is a **free parameter** `Hb`:

* the test zero `ρ'` is only required to satisfy `|ρ'.im| + δ ≤ Hb` (the window containment) and
  `|ρ'.im| ≤ 10 log q` (the range of the log-derivative input `L52Hyp` and of the principal-
  character Lemma 5.3), while
* the maximality hypothesis `hmax` is assumed only for zeros of height `≤ Hb`.

The point of the free parameter is that a `λ`-minimiser over a box of height `H` is automatically
maximal over every *sub*-box, so the height of the box and the height of the test zero can be
decoupled (the `10 log q` of the existing statements forces them to agree).

The proof is the one of `lemma6_3_fullLocal` (itself the point-condition copy of the wide Lemma 6.3)
with the window radius `K := |γ'| + 1` replaced by `K := Hb`; this is a pure restriction of the
existing argument: the principal-character input `principalKsumWide` and the log-derivative input
`L52Hyp` are used only at the two points `β'` and `β' + iγ'`, whose heights are bounded by
`|γ'| ≤ 10 log q`.

We also record the versions of `lemma6_3_widePt` and `windowSum_ge_single_real` with the
(provably unused) hypothesis `β' ≤ β₁` removed, so that the triangle below does not need the
inequality `λ(ρ') ≥ λ(ρ₀)` between the test zero and the exceptional zero.
-/
import Mathlib
import Submission.Work.LinnikAreas.DhRepel.dhTrianglePt
import Submission.Work.LinnikAreas.OtherCharRepel.dhTrianglePtLocal
import Submission.Work.NumberTheory.Linnik.scratch_ws13
import Submission.Work.NumberTheory.Linnik.scratch_ws15

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Linnik

theorem windowSum_ge_single_realNB {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfnn : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ f t)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    {L δ β₁ β' : ℝ} (hL : 0 ≤ L)
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) (β₁ : ℂ) ≠ 0)
    (hwin : ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ)
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u.re ≤ β') :
    ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀,
            Complex.exp (-((((β' : ℂ) - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0) := by
  have hρnn : 0 ≤ ((∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) := by
    have hpt : ∀ t : ℝ, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)
        = ((Real.exp (-(((β' - β₁) * L) * t)) * f t : ℝ) : ℂ) := by
      intro t
      have h1 : -((((β' : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ)) = ((-(((β' - β₁) * L) * t) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    simp only [hpt]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    apply intervalIntegral.integral_nonneg hx₀.le
    intro t ht
    exact mul_nonneg (Real.exp_nonneg _) (hfnn t ht)
  have hzero' : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u.re ≤ (β' : ℂ).re := by
    intro u hu hw hne
    simpa using hzero u hu hw hne
  exact le_windowSum_of_mem_ne χ hχ hL hF hdiv hwin hρnn hzero'


theorem lemma6_3_widePtNB (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
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
        (hβ₁ : |1 - β₁| ≤ δ) (hβ' : |1 - β'| ≤ δ)
        (hβ₁le : β₁ ≤ 1) (hβ'le : β' ≤ 1)
        (hγ' : |γ'| ≤ 10 * Real.log (q : ℝ))
        (hβ₁pt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hβ'pt : |1 - β'| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
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
  obtain ⟨q₀p, hq₀p⟩ := (Work.LinnikAreas.principalKsumWide x₀ B hx₀ hB) hcont hsupp hf2 hBnd
    (by positivity : (0:ℝ) < ε/2) hf0
  obtain ⟨q₀χ, hq₀χ⟩ := (lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨max (max q₀p q₀χ) 6, ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ β' γ' hβ₁ hβ' hβ₁le hβ'le hγ' hβ₁pt hβ'pt hzero₁ hzero' H hw13 hw15
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
    simpa only [abs_sub_comm] using hβ'pt
  have hlowβ' : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ β' := by
    have h : 1 - β' ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := (abs_le.mp hβ'pt).2
    linarith only [h]
  have him2 : |γ'| ≤ 10 * Real.log (q : ℝ) := hγ'
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
      (by simp only [abs_zero]; linarith [hLnn])
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


theorem lemma6_3_fullH (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ * χ = 1) [NeZero χ.conductor]
        {β₁ β' γ' : ℝ} {Hh : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ' : |1 - β'| ≤ δ)
        (hβ₁le : β₁ ≤ 1) (hβ'le : β' ≤ 1)
        (hγH : |γ'| + δ ≤ Hh) (hγ10 : |γ'| ≤ 10 * Real.log (q : ℝ))
        (hβ₁pt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hβ'pt : |1 - β'| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) ≠ 0)
        (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
        (hne : ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ (β₁ : ℂ))
        (hmult₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) = 1)
        (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
            |u.im| ≤ Hh → u = (β₁ : ℂ) ∨ u.re ≤ β')
        (hrect₁ : Real.log (q : ℝ) * (1 - β₁) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
        (hrect' : Real.log (q : ℝ) * (1 - β') ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
        (H : L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (2 * c + 4 * ε) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn ε hε δ hδ0 hδ1
  -- the far-decay threshold
  obtain ⟨Lfar, hLfar1, hfar⟩ := far_term_le_real (x₀ := x₀) (B := B) (δ := δ) hx₀ hB hδ0
    (hcont.mono Set.Icc_subset_Ici_self) (contDiffOn_ofReal_comp hf2)
    (fun t ht => by rw [iteratedDeriv_ofReal_comp]; exact_mod_cast hBnd t ht)
    (fun t ht => hsupp t ht) (ε := f 0 * ε) (mul_pos hf0 hε)
  -- the threshold making `loglog L ≤ (3δ/2) L`
  obtain ⟨Lthr, hLthr1, hthr⟩ := exists_loglog_le_mul (c := 3 * δ / 2) (by positivity)
  obtain ⟨q₀, hq₀⟩ := lemma6_3_widePtNB x₀ B c hx₀ hB (f := f) hcont hsupp hf2 hBnd hf0 hfnn hFnn hε hδ0 hδ1
  refine ⟨max (max (max q₀ 3) (Nat.ceil (Real.exp Lfar) + 1))
      (Nat.ceil (Real.exp Lthr) + 1), ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ β' γ' Hh hβ₁ hβ' hβ₁le hβ'le hγH hγ10 hβ₁pt hβ'pt
    hdiv₁ hdiv' hne hmult₁ hmax hrect₁ hrect' H
  have hqq₀ : q₀ ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hqfar : Nat.ceil (Real.exp Lfar) + 1 ≤ q := by omega
  have hqthr : Nat.ceil (Real.exp Lthr) + 1 ≤ q := by omega
  have hqpos : 0 < q := by omega
  have hlogq : (0 : ℝ) < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) := le_of_lt hlogq
  have hlogq1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    linarith [Real.exp_one_lt_three]
  have hLfar_le : Lfar ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp Lfar]
    refine Real.log_le_log (Real.exp_pos Lfar) ?_
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : Nat.ceil (Real.exp Lfar) ≤ q)
  have hLthr_le : Lthr ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp Lthr]
    refine Real.log_le_log (Real.exp_pos Lthr) ?_
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : Nat.ceil (Real.exp Lthr) ≤ q)
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hβ₁lo : 1 - δ ≤ β₁ := by have := (abs_le.mp hβ₁).2; linarith
  have hβ₁hi : β₁ ≤ 1 + δ := by have := (abs_le.mp hβ₁).1; linarith
  have hβ'lo : 1 - δ ≤ β' := by have := (abs_le.mp hβ').2; linarith
  have hβ'hi : β' ≤ 1 + δ := by have := (abs_le.mp hβ').1; linarith
  have hβ₁pos : 0 < β₁ := by linarith
  have hβ'pos : 0 < β' := by linarith
  have himρ : (((β' : ℂ) + (γ' : ℂ) * Complex.I)).im = γ' := by simp
  have hmem₂ : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|((β' : ℂ)).im| + 2) := by
    have him0 : ((β' : ℂ)).im = 0 := by simp
    rw [Metric.mem_closedBall, dist_zero_right, him0, abs_zero, zero_add,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hmemR : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|γ'| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [abs_nonneg γ'], by linarith [abs_nonneg γ']⟩
  have han : ∀ z : ℂ, AnalyticAt ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter) z :=
    fun z => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
  have hdiv₁₂ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) (β₁ : ℂ) ≠ 0 := by
    have heq : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) (β₁ : ℂ)
        = (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) :=
      divisor_closedBall_congr han hmem₂ hmemR
    intro h0
    exact hdiv₁ (by rw [← heq]; exact h0)
  have hmemρ : ((β' : ℂ) + (γ' : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) (|γ'| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖(β' : ℂ) + (γ' : ℂ) * Complex.I‖
        ≤ ‖(β' : ℂ)‖ + ‖(γ' : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |β'| + |γ'| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |γ'| + 2 := by
          have h2 : |β'| ≤ 2 := by
            rw [abs_le]; exact ⟨by linarith, by linarith⟩
          linarith [abs_nonneg γ']
  have hzero₁' : DirichletCharacter.LFunction χ.primitiveCharacter (β₁ : ℂ) = 0 :=
    LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' (a := 0) (ρ := |γ'| + 2) hmemR (by simpa using hβ₁pos) hdiv₁
  have hzero₁ : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 := by
    simp only [Commons.NumberTheory.DirichletCharacter.LFunction_eq_primitiveCharacter_mul χ hχ,
      hzero₁', zero_mul]
  have hzero'' : DirichletCharacter.LFunction χ.primitiveCharacter
      ((β' : ℂ) + (γ' : ℂ) * Complex.I) = 0 :=
    LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' (a := 0) (ρ := |γ'| + 2) hmemρ (by simpa using hβ'pos) hdiv'
  have hzero' : DirichletCharacter.LFunction χ ((β' : ℂ) + (γ' : ℂ) * Complex.I) = 0 := by
    simp only [Commons.NumberTheory.DirichletCharacter.LFunction_eq_primitiveCharacter_mul χ hχ,
      hzero'', zero_mul]
  have hwinK₁ : |((β' : ℂ)).im| + δ ≤ Hh := by
    have him0 : ((β' : ℂ)).im = 0 := by simp
    rw [him0, abs_zero, zero_add]
    linarith [hγH, abs_nonneg γ']
  have hwinK' : |(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + δ ≤ Hh := by
    rw [himρ]
    exact hγH
  have hzw1 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u.re ≤ β' := by
    intro u hu hw hne'
    have h := window_hzero_of_Lzero_local χ.primitiveCharacter hχ' (K := Hh)
      (A := β') (δ := δ) (s := (β' : ℂ)) (σ := (β₁ : ℂ)) hδ1 hwinK₁ (le_of_eq rfl) hmax
    simpa using h u hu hw hne'
  have hzw2 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((β' : ℂ) + (γ' : ℂ) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ →
      u ≠ ((β' : ℂ) + (γ' : ℂ) * Complex.I) → u ≠ (β₁ : ℂ) → u.re ≤ β' := by
    intro u hu hw _ hne'
    have h := window_hzero_of_Lzero_local χ.primitiveCharacter hχ' (K := Hh)
      (A := β') (δ := δ) (s := ((β' : ℂ) + (γ' : ℂ) * Complex.I)) (σ := (β₁ : ℂ))
      hδ1 hwinK' (by simp) hmax
    simpa [himρ] using h u hu hw hne'
  have hfnn' : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ f t := fun t _ => hfnn t
  have hRρ : |(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2 = |γ'| + 2 := by rw [himρ]
  have hdiv₁q : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) (β₁ : ℂ) ≠ 0 := by
    rw [hRρ]; exact hdiv₁
  have hdivq : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2)))
      ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0 := by
    rw [hRρ]; exact hdiv'
  have hmult₁q : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) (β₁ : ℂ) = 1 := by
    rw [hRρ]; exact hmult₁
  have hw13 : ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re)
      ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (β' : ℂ) := by
    have hwin₁ : ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ := by
      have h1 : (1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ) = ((1 - β₁ : ℝ) : ℂ) := by
        simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs]
      exact hβ₁
    simpa only [winSum] using windowSum_ge_single_realNB χ.primitiveCharacter hχ'
      (f := f) (x₀ := x₀) hx₀ hfnn' hFnn (L := Real.log (q : ℝ)) (δ := δ) hLnn
      hdiv₁₂ hwin₁ hzw1
  have h614 : ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ ∨
      (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
          (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re ≤ f 0 * ε := by
    by_cases hnear : ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ
    · exact Or.inl hnear
    · push Not at hnear
      right
      have hfar1 : δ / 2 < |γ'| := by
        refine gt_half_delta_of_far (δ := δ) (β₁ := β₁) (γ' := γ')
          (lam₁ := Real.log (q : ℝ) * (1 - β₁)) (L := Real.log (q : ℝ)) hlogq ?_ ?_ ?_
        · have h1 : Real.log (q : ℝ) * (1 - β₁) / Real.log (q : ℝ) = 1 - β₁ := by
            field_simp
          rw [h1, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - β₁)]
        · refine le_trans hrect₁ ?_
          have h := hthr (Real.log (q : ℝ)) hLthr_le
          linarith
        · have h' : (1:ℂ) - (β₁ : ℂ) + (γ' : ℂ) * Complex.I
              = (1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ) := by
            rw [himρ]; ring
          rw [h']
          exact hnear
      have hfar_apply := hfar (L := Real.log (q : ℝ))
        (a := (β' - β₁) * Real.log (q : ℝ)) (η := γ' * Real.log (q : ℝ))
        hLfar_le hlogq1
        (by
          rw [abs_mul, abs_of_pos hlogq]
          rcases le_total β' β₁ with hle | hge
          · -- `β' ≤ β₁`
            have h2 : β₁ - β' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 / Real.log (q : ℝ) := by
              rw [le_div_iff₀ hlogq]
              nlinarith [hrect', hrect₁]
            rw [abs_of_nonpos (by linarith)]
            nlinarith [h2, hlogq]
          · -- `β₁ ≤ β'`
            have h2 : β' - β₁ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 / Real.log (q : ℝ) := by
              rw [le_div_iff₀ hlogq]
              nlinarith [hrect', hrect₁]
            rw [abs_of_nonneg (by linarith)]
            nlinarith [h2, hlogq])
        (by
          rw [abs_mul, abs_of_pos hlogq]
          nlinarith [hfar1, hlogq])
      have heqint : (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
              (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ))
          = ∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((β' - β₁) * Real.log (q : ℝ) : ℝ) : ℂ) +
              (((γ' * Real.log (q : ℝ) : ℝ)) : ℂ) * Complex.I) * (t : ℂ))) *
              ((f t : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t _
        congr 2
        push_cast
        ring
      rw [heqint]
      exact le_trans (Complex.re_le_norm _) hfar_apply
  have hw15 : ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
          ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re)
      + (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
          (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - f 0 * ε
      ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ
          ((β' : ℂ) + (γ' : ℂ) * Complex.I) := by
    have h0nn : 0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
          ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re := by
      have hpt : ∀ t : ℝ, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
            ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ) = ((f t : ℝ) : ℂ) := by
        intro t; simp
      simp only [hpt]
      rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
      exact intervalIntegral.integral_nonneg hx₀.le (fun t _ => hfnn t)
    simpa only [winSum] using windowSum_ge_pair χ.primitiveCharacter hχ'
      (f := f) (x₀ := x₀) hx₀ hfnn' hFnn (L := Real.log (q : ℝ)) hLnn hε.le hβ' hne hf0.le
      hdiv₁q hdivq hmult₁q h0nn h614 hzw2

  exact hq₀ hqq₀ χ hχ hreal hβ₁ hβ' hβ₁le hβ'le hγ10 hβ₁pt hβ'pt hzero₁ hzero'
    H hw13 hw15


end Commons.NumberTheory.Linnik

namespace Work.LinnikAreas.DhRepel

open DirichletCharacter Complex
open scoped Classical

/-- The primitive character inducing a non-principal character is non-principal. -/
private lemma dhH_primitiveCharacter_ne_one' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  refine hχ ?_
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- A zero of the ordinary `L`-function of a non-principal character has real part `< 1`. -/
private lemma dhH_re_lt_one_of_LFunction_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {u : ℂ} (hu : DirichletCharacter.LFunction χ u = 0) : u.re < 1 := by
  by_contra h
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h)) hu

/-- On `(0,x)` the triangle `t ↦ max (x-t) 0` agrees with the affine function `x - t`. -/
private lemma dhH_iteratedDeriv_two_tent {x t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) x) :
    iteratedDeriv 2 (fun s : ℝ => max (x - s) 0) t = 0 := by
  have hcongr : Set.EqOn (fun s : ℝ => max (x - s) 0) (fun s : ℝ => x - s)
      (Set.Ioo (0:ℝ) x) :=
    fun s hs => max_eq_left (by linarith [hs.2])
  have h1 := Set.EqOn.iteratedDeriv_of_isOpen hcongr isOpen_Ioo 2 ht
  rw [h1]
  simp [iteratedDeriv_succ, iteratedDeriv_const, iteratedDeriv_id]

/-- The integral of the triangle `t ↦ max (x-t) 0` over `[0,x]` is `x²/2`. -/
private lemma dhH_integral_tent (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in (0:ℝ)..x, max (x - t) 0) = x ^ 2 / 2 := by
  have hcongr : (∫ t in (0:ℝ)..x, max (x - t) 0) = ∫ t in (0:ℝ)..x, (x - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact max_eq_left (by linarith [ht.2])
  rw [hcongr]
  have hsub : (∫ t in (0:ℝ)..x, (x - t))
      = (∫ t in (0:ℝ)..x, (fun _ : ℝ => x) t) - ∫ t in (0:ℝ)..x, t :=
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)
  rw [hsub, intervalIntegral.integral_const, integral_id]
  ring

/-- **The `§6` triangle inequality with a free height parameter.**  Same statement as
`Work.LinnikAreas.DhRepel.dhTrianglePt`, with the two roles of `10 log q` split: the maximality
hypothesis `hmax` is taken over the box `|Im u| ≤ Hb` for a free `Hb ≥ |ρ'.im| + δ`, while the
test zero is only assumed to satisfy `|ρ'.im| ≤ 10 log q`.

Note that neither the hypothesis `ρ'.re ≤ β₁` of `dhTrianglePt` nor the bound `Hb ≤ 10 log q`
is needed. -/
theorem dhTrianglePtH :
    ∀ x : ℝ, 0 < x → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ c : ℝ,
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      (hχ : χ ≠ 1) (hreal : χ ^ 2 = 1) [NeZero χ.conductor] {β₁ : ℝ} {ρ' : ℂ}
      (hβ₁ : |1 - β₁| ≤ δ)
      (hβ' : |1 - ρ'.re| ≤ δ)
      {Hb : ℝ} (hHb : |ρ'.im| + δ ≤ Hb)
      (hγ10 : |ρ'.im| ≤ 10 * Real.log (q : ℝ))
      (hβ₁pt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
      (hρ'pt : |1 - ρ'.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
      (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) (β₁ : ℂ) ≠ 0)
      (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) ρ' ≠ 0)
      (hne : ρ' ≠ (β₁ : ℂ))
      (hmult₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) (β₁ : ℂ) = 1)
      (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
          |u.im| ≤ Hb → u = (β₁ : ℂ) ∨ u.re ≤ ρ'.re)
      (hrect₁ : Work.LinnikContract.lamOf q (β₁ : ℂ)
          ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
      (hrect' : Work.LinnikContract.lamOf q ρ'
          ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
      (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x, Real.exp ((Work.LinnikContract.lamOf q ρ') * t) * (x - t))
        - 2 * (∫ t in (0:ℝ)..x, Real.exp ((Work.LinnikContract.lamOf q ρ'
            - Work.LinnikContract.lamOf q (β₁ : ℂ)) * t) * (x - t))
        - x ^ 2 / 2 + (2 * c + 4 * ε) * x := by
  intro x hx ε hε δ hδ0 hδ1 c
  obtain ⟨q₀, hq₀⟩ := Commons.NumberTheory.Linnik.lemma6_3_fullH x 0 c hx le_rfl
    (f := fun t : ℝ => max (x - t) 0)
    (by fun_prop)
    (fun t ht => max_eq_right (by linarith [ht]))
    (by
      have haff : ContDiffOn ℝ 2 (fun t : ℝ => x - t) (Set.Ioo 0 x) :=
        (contDiffOn_const (c := x)).sub contDiffOn_id
      exact haff.congr (fun t ht => max_eq_left (by linarith [ht.2])))
    (fun t ht => by rw [dhH_iteratedDeriv_two_tent ht]; norm_num)
    (by rw [sub_zero, max_eq_left hx.le]; exact hx)
    (fun t => le_max_right _ _)
    (triangle_hFnn hx)
    (ε := ε) hε (δ := δ) hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q hq inst χ hχ hreal instc β₁ ρ' hβ₁ hβ' Hb hHb hγ10 hβ₁pt hρ'pt hdiv₁ hdiv' hne hmult₁ hmax
    hrect₁ hrect' H
  have hχ' : χ.primitiveCharacter ≠ 1 := dhH_primitiveCharacter_ne_one' hχ
  -- the two `re < 1` facts for the zeros, via the critical strip
  have hβ₁lo : 1 - δ ≤ β₁ := by have := (abs_le.mp hβ₁).2; linarith
  have hβ₁hi : β₁ ≤ 1 + δ := by have := (abs_le.mp hβ₁).1; linarith
  have hβ₁pos : 0 < β₁ := by linarith
  have hβ'lo : 1 - δ ≤ ρ'.re := by have := (abs_le.mp hβ').2; linarith
  have hρ'pos : 0 < ρ'.re := by linarith
  have hmem₁ : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> [linarith [abs_nonneg ρ'.im]; linarith [abs_nonneg ρ'.im]]
  have hmem' : ρ' ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ') ?_
    have h1 : |ρ'.re| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hβ'lo], by linarith [(abs_le.mp hβ').1, hδ1]⟩
    linarith [abs_nonneg ρ'.im]
  have hL₁ : DirichletCharacter.LFunction χ.primitiveCharacter (β₁ : ℂ) = 0 :=
    Commons.NumberTheory.Linnik.LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' hmem₁ (by simpa using hβ₁pos) hdiv₁
  have hL' : DirichletCharacter.LFunction χ.primitiveCharacter ρ' = 0 :=
    Commons.NumberTheory.Linnik.LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' hmem' (by simpa using hρ'pos) hdiv'
  have hβ₁le : β₁ ≤ 1 := (dhH_re_lt_one_of_LFunction_zero hχ' hL₁).le
  have hβ'le : ρ'.re ≤ 1 := (dhH_re_lt_one_of_LFunction_zero hχ' hL').le
  -- the `λ`-form of the rectangle hypotheses
  have hrect₁' : Real.log (q : ℝ) * (1 - β₁)
      ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    rw [Work.LinnikContract.lamOf, Complex.ofReal_re] at hrect₁
    rw [mul_comm]; exact hrect₁
  have hrect'' : Real.log (q : ℝ) * (1 - ρ'.re)
      ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    rw [Work.LinnikContract.lamOf] at hrect'
    rw [mul_comm]; exact hrect'
  have h := hq₀ hq χ hχ (by simpa only [pow_two] using hreal) hβ₁ hβ' hβ₁le hβ'le
    (Hh := Hb) hHb hγ10 hβ₁pt hρ'pt
    hdiv₁ (by rw [Complex.re_add_im]; exact hdiv') (by rw [Complex.re_add_im]; exact hne)
    hmult₁ hmax hrect₁' hrect'' H
  -- rewrite the conclusion of Lemma 6.3 into the shape of the statement
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) x, max (x - t) 0 = x - t := by
    intro t ht
    rw [Set.uIcc_of_le hx.le] at ht
    exact max_eq_left (by linarith [ht.2])
  have heq1 : (∫ t in (0:ℝ)..x,
        Real.exp (Real.log (q : ℝ) * (1 - ρ'.re) * t) * max (x - t) 0)
      = ∫ t in (0:ℝ)..x, Real.exp ((Work.LinnikContract.lamOf q ρ') * t) * (x - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [hF t ht, Work.LinnikContract.lamOf]
    congr 2
    ring
  have heq2 : (∫ t in (0:ℝ)..x,
        Real.exp (-(Real.log (q : ℝ) * (1 - β₁) - Real.log (q : ℝ) * (1 - ρ'.re)) * t)
          * max (x - t) 0)
      = ∫ t in (0:ℝ)..x,
          Real.exp ((Work.LinnikContract.lamOf q ρ' - Work.LinnikContract.lamOf q (β₁ : ℂ)) * t)
            * (x - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [hF t ht, Work.LinnikContract.lamOf, Work.LinnikContract.lamOf, Complex.ofReal_re]
    congr 2
    ring
  have heq4 : max (x - 0) 0 * (2 * c + 4 * ε) = (2 * c + 4 * ε) * x := by
    rw [sub_zero, max_eq_left hx.le, mul_comm]
  rw [heq1, heq2, dhH_integral_tent x hx.le, heq4] at h
  linarith only [h]

end Work.LinnikAreas.DhRepel
