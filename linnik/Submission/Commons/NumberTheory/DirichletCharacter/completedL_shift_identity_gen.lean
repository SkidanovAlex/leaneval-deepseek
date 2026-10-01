import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_completed_tentF_eq
import Submission.Commons.NumberTheory.DirichletCharacter.goodHeight_separated
import Submission.Commons.NumberTheory.DirichletCharacter.horizontal_logDeriv_completedL_tendsto_gen
import Submission.Commons.NumberTheory.DirichletCharacter.leftEdge_logDeriv_bound
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.Analysis.Complex.rectInt_tendsto_vertical_gen
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- Expand the rectangle integral over `[A - iT, B + iT]` into its four boundary pieces. -/
lemma rectInt_strip_expand (A B T : ℝ) (F : ℂ → ℂ) :
    rectInt ((A : ℂ) - (T : ℂ) * Complex.I) ((B : ℂ) + (T : ℂ) * Complex.I) F =
      (∫ x : ℝ in A..B, F ((x : ℂ) - (T : ℂ) * Complex.I)) -
      (∫ x : ℝ in A..B, F ((x : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-T)..T, F ((B : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ in (-T)..T, F ((A : ℂ) + (y : ℂ) * Complex.I)) := by
  have hzre : (((A : ℂ) - (T : ℂ) * Complex.I)).re = A := by simp
  have hzim : (((A : ℂ) - (T : ℂ) * Complex.I)).im = -T := by simp
  have hwre : (((B : ℂ) + (T : ℂ) * Complex.I)).re = B := by simp
  have hwim : (((B : ℂ) + (T : ℂ) * Complex.I)).im = T := by simp
  rw [rectInt_eq_def, hzre, hwre, hzim, hwim]
  simp only [Complex.ofReal_neg, neg_mul]
  congr 2

/-- The rectangle integral over `[A - i·Tf, B + i·Tf]` tends to `i(∫_B − ∫_A)` along any
height function `Tf → ∞`, provided the horizontal pieces vanish and the two vertical
integrals converge. -/
lemma rectInt_tendsto_vertical_gen_comp {F : ℂ → ℂ} {A B : ℝ} (_hAB : A < B)
    {Tf : ℝ → ℝ} (hTf : Filter.Tendsto Tf Filter.atTop Filter.atTop)
    (hBint : MeasureTheory.Integrable (fun t : ℝ => F ((B : ℂ) + (t : ℂ) * Complex.I)))
    (hAint : MeasureTheory.Integrable (fun t : ℝ => F ((A : ℂ) + (t : ℂ) * Complex.I)))
    (hu : Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in A..B, F ((x : ℂ) + (Tf T : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hd : Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in A..B, F ((x : ℂ) - (Tf T : ℂ) * Complex.I))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun T : ℝ =>
        rectInt ((A : ℂ) - (Tf T : ℂ) * Complex.I) ((B : ℂ) + (Tf T : ℂ) * Complex.I) F)
      Filter.atTop
      (nhds (Complex.I * ((∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * Complex.I))))) := by
  have hnegtop : Tendsto (fun T : ℝ => -Tf T) atTop atBot := by
    rw [Filter.tendsto_atBot]
    intro a
    filter_upwards [hTf.eventually (eventually_ge_atTop (-a))] with T hT
    linarith
  have hC : Tendsto (fun T : ℝ => ∫ y : ℝ in (-(Tf T))..(Tf T), F ((B : ℂ) + (y : ℂ) * Complex.I))
      atTop (nhds (∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hBint hnegtop hTf
  have hD : Tendsto (fun T : ℝ => ∫ y : ℝ in (-(Tf T))..(Tf T), F ((A : ℂ) + (y : ℂ) * Complex.I))
      atTop (nhds (∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hAint hnegtop hTf
  have hcomb := ((hd.sub hu).add (hC.const_mul Complex.I)).sub (hD.const_mul Complex.I)
  simp only [sub_zero, zero_add] at hcomb
  have hlim : Complex.I * ((∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * Complex.I)))
      = Complex.I * (∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I * (∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * Complex.I)) := by ring
  rw [hlim]
  refine hcomb.congr' ?_
  filter_upwards with T
  exact (rectInt_strip_expand A B (Tf T) F).symm

theorem completedL_shift_identity_gen {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {Φ : ℂ → ℂ}
    (hΦdiff : Differentiable ℂ Φ) {M : ℝ} (hM : 0 < M)
    (hΦb : ∀ u : ℂ, u.re ≤ α → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2))
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (hIAα : MeasureTheory.Integrable (fun t : ℝ => logDeriv (DirichletCharacter.completedLFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) * Φ ((α : ℂ) + (t : ℂ) * Complex.I)))
    (hIAl : MeasureTheory.Integrable (fun t : ℝ => logDeriv (DirichletCharacter.completedLFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) * Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)))
    {Z : ℂ} (hZ : Filter.Tendsto (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
        (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ u) else 0))
      Filter.atTop (nhds Z)) :
    (1 / (2 * (Real.pi : ℂ))) *
      ((∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) * Φ ((α : ℂ) + (t : ℂ) * Complex.I)) -
       (∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) * Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)))
      = Z := by
  obtain ⟨c, hc0, hgood⟩ := goodHeight_separated χ hχ hχprim
  have hex : ∀ T : ℝ, ∃ T' : ℝ, 1 ≤ T → T + 1 ≤ T' ∧ T' ≤ T + 2 ∧
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        c / Real.log ((N : ℝ) * (T' + 3)) ≤ |ρ.im - T'|) ∧
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        c / Real.log ((N : ℝ) * (T' + 3)) ≤ |ρ.im + T'|) := by
    intro T
    by_cases hT : 1 ≤ T
    · obtain ⟨T', h1, h2, h3, h4⟩ := hgood T hT
      exact ⟨T', fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨1, fun hh => absurd hh hT⟩
  choose T' hT' using hex
  have hT'tend : Tendsto T' atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (b - 1)] with T h1 h2
    exact le_trans (by linarith) ((hT' T h1).1)
  set F : ℂ → ℂ := fun u => logDeriv (DirichletCharacter.completedLFunction χ) u * Φ u with hF
  have hFα : Integrable (fun t : ℝ => F ((α : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa [hF] using hIAα
  have hFl : Integrable (fun t : ℝ => F (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) := by
    simpa [hF] using hIAl
  obtain ⟨hhu, hhd⟩ := horizontal_logDeriv_completedL_tendsto_gen (N := N) χ hχ hχprim
    (A := -1/2) (B := α) (by norm_num) (by linarith [hα1]) (le_of_lt hα2) hΦdiff (le_of_lt hM)
    (fun u hu => hΦb u hu) hc0 (fun T hT => (hT' T hT).1)
    (fun T hT ρ hρ => (hT' T hT).2.2.1 ρ hρ)
    (fun T hT ρ hρ => (hT' T hT).2.2.2 ρ hρ)
  have hu : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..α,
      F ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)) atTop (nhds 0) := by
    simpa [hF] using hhu
  have hd : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..α,
      F ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)) atTop (nhds 0) := by
    simpa [hF] using hhd
  have hlimrect : Tendsto (fun T : ℝ =>
      rectInt (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)
        ((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) F) atTop
      (nhds (Complex.I * ((∫ t : ℝ, F ((α : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I))))) :=
    rectInt_tendsto_vertical_gen_comp (A := -1/2) (B := α) (by linarith) hT'tend hFα hFl hu hd
  -- the residue identity at the good heights
  have hres : ∀ T : ℝ, 1 ≤ T → rectInt (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)
      ((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) F
      = 2 * (Real.pi : ℂ) * Complex.I * (∑ᶠ ρ : ℂ, (if |ρ.im| < T' T then
          (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
            Φ ρ) else 0)) := by
    intro T hT
    have hsep1 := (hT' T hT).2.2.1
    have hsep2 := (hT' T hT).2.2.2
    have hpos : 0 < T' T := by linarith [(hT' T hT).1]
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
    have hlogNpos : 0 < Real.log ((N : ℝ) * (T' T + 3)) := by
      apply Real.log_pos
      nlinarith
    have hδpos : 0 < c / Real.log ((N : ℝ) * (T' T + 3)) := div_pos hc0 hlogNpos
    have hMb : ∀ s ∈ rectSet (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)
        ((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I), ‖Φ s‖ ≤ M := by
      intro s hs
      obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
      rw [show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re = -1/2 by simp,
        show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re = α by simp,
        Set.uIcc_of_le (by linarith : (-1/2:ℝ) ≤ α)] at hre
      calc ‖Φ s‖ ≤ M / (1 + ‖s‖ ^ 2) := hΦb s hre.2
        _ ≤ M := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + ‖s‖ ^ 2)]
            nlinarith [hM, sq_nonneg ‖s‖]
    have hzre : (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re <
        (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re := by
      rw [show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re = -1/2 by simp,
        show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re = α by simp]
      linarith
    have hzim : (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).im <
        (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).im := by
      rw [show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).im = -T' T by simp,
        show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).im = T' T by simp]
      linarith
    have h0in : (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re < 0 ∧
        0 < (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re ∧
        (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).im < 0 ∧
        0 < (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).im := by
      rw [show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re = -1/2 by simp,
        show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re = α by simp,
        show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).im = -T' T by simp,
        show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).im = T' T by simp]
      exact ⟨by norm_num, by linarith, by linarith, by linarith⟩
    have hins : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re < ρ.re ∧
        ρ.re < (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re := by
      intro ρ hρ
      have hs := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hρ
      rw [show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re = -1/2 by simp,
        show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re = α by simp]
      exact ⟨by linarith [hs.1], by linarith [hs.2, hα1]⟩
    have hnz : ∀ s ∈ rectBoundary (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)
        ((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I),
        DirichletCharacter.completedLFunction χ s ≠ 0 := by
      intro s hs h0
      rcases hs with ⟨hre, him | him⟩ | ⟨him, hre | hre⟩
      · have h2 := hsep2 s h0
        rw [show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).im = -T' T by simp] at him
        rw [him] at h2
        have hz0 : |-(T' T) + T' T| = 0 := by rw [neg_add_cancel, abs_zero]
        rw [hz0] at h2
        linarith
      · have h2 := hsep1 s h0
        rw [show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).im = T' T by simp] at him
        rw [him] at h2
        have hz0 : |T' T - T' T| = 0 := by rw [sub_self, abs_zero]
        rw [hz0] at h2
        linarith
      · have hre' : s.re = -1/2 := by rw [hre]; simp
        have hsform : s = (((-1/2 : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) := by
          apply Complex.ext
          · rw [hre']; simp
          · simp
        rw [hsform] at h0
        have hs0 : (((-1/2:ℝ):ℂ) + (s.im:ℂ)*Complex.I) ≠ 0 := by
          intro hh
          have h2 := congrArg Complex.re hh
          simp at h2
        have hγ : DirichletCharacter.gammaFactor χ (((-1/2:ℝ):ℂ) + (s.im:ℂ)*Complex.I) ≠ 0 :=
          gammaFactor_ne_zero_of_re_gt_neg_one χ (by norm_num) hs0
        have hmul := completedL_eq_gammaFactor_mul_L χ
          (s := (((-1/2:ℝ):ℂ) + (s.im:ℂ)*Complex.I)) hs0 (by norm_num)
        rw [hmul] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · exact hγ h
        · exact LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim s.im h
      · have hre' : s.re = α := by rw [hre]; simp
        exact absurd h0 (completedLFunction_ne_zero_of_one_lt_re χ (by rw [hre']; exact hα1))
    have h := rectInt_logDeriv_completed_entire_mul_eq χ hχ hχprim hΦdiff
      hzre hzim h0in hins hnz hMb
    rw [h]
    congr 1
    refine finsum_congr (fun ρ => ?_)
    by_cases hz : DirichletCharacter.completedLFunction χ ρ = 0
    · have hcond : ((((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re < ρ.re ∧
          ρ.re < (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re ∧
          (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).im < ρ.im ∧
          ρ.im < (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).im) ↔ |ρ.im| < T' T := by
        rw [show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).re = -1/2 by simp,
          show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).re = α by simp,
          show (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I).im = -T' T by simp,
          show (((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)).im = T' T by simp]
        have hs := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hz
        constructor
        · intro hc
          exact abs_lt.mpr ⟨hc.2.2.1, hc.2.2.2⟩
        · intro hc
          exact ⟨by linarith [hs.1], by linarith [hs.2, hα1],
            (abs_lt.mp hc).1, (abs_lt.mp hc).2⟩
      exact if_congr hcond rfl rfl
    · have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ = 0 := by
        simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
      rw [hord]
      simp
  have hreslim : Tendsto (fun T : ℝ => rectInt (((-1/2:ℝ):ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)
      ((α : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) F) atTop
      (nhds (2 * (Real.pi : ℂ) * Complex.I * Z)) := by
    have h1 : Tendsto (fun T : ℝ => 2 * (Real.pi : ℂ) * Complex.I * (∑ᶠ ρ : ℂ,
        (if |ρ.im| < T' T then
          (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
            Φ ρ) else 0))) atTop (nhds (2 * (Real.pi : ℂ) * Complex.I * Z)) :=
      (hZ.comp hT'tend).const_mul (2 * (Real.pi : ℂ) * Complex.I)
    refine Tendsto.congr' ?_ h1
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    exact (hres T hT).symm
  have huniq : Complex.I * ((∫ t : ℝ, F ((α : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)))
      = 2 * (Real.pi : ℂ) * Complex.I * Z :=
    tendsto_nhds_unique hlimrect hreslim
  have hAB : (∫ t : ℝ, F ((α : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) = 2 * (Real.pi : ℂ) * Z := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [huniq]
    ring
  change (1 / (2 * (Real.pi : ℂ))) * ((∫ t : ℝ, F ((α : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I))) = Z
  rw [hAB]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    exact_mod_cast Real.pi_ne_zero
  field_simp

end

end Commons.NumberTheory.DirichletCharacter
