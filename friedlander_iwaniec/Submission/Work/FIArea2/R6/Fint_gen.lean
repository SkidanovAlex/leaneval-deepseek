/-
# Lemma 7.1 of Friedlander–Iwaniec for the general round-6 majorant

`Work.FIArea2.lemma_7_1` is *FI* (7.5) for a majorant supported in `[M/4, 4M]`.  Round 6's
`IsMajorant6` (see `Submission/Work/FITop4/Defs6.lean`) only assumes support in `[A,B]` with
`M/64 ≤ A`, `B ≤ 64 M` and `|F^{(j)}| ≤ Cder·M^{-j}` — the support may spread over the four
dyadic scales `[M/64, 64 M]` and the derivative constant `Cder ≥ 1` is arbitrary.

This module proves the same estimate for that general majorant, with the same *shape*

  `‖F(u₁,u₂)‖ ≤ C·Cder·(1 + u₁²δ√M)^{−1}(1 + u₂²δ√M)^{−1}·√M·log(2 + δ^{−2})`, `δ² = 1 − γ²`,

but with an unspecified absolute constant `C` (the whole point of the round-6 general form: the
per-pair bound of §9 is then applied with a constant that is absorbed by the `∃ K` of
`Work.FIArea2.R6.sec9_error_of_pair_H_gen`).  The two analytic inputs are delegated:

* `Work.FIArea2.R6.vol_regG_le` — the volume of the general region is
  `≤ 2000√M log(2+δ^{−2})` (used by the trivial bound);
* `Work.FIArea2.R6.deriv4_pointwise_gen` — the Faà di Bruno bound
  `|∂₁⁴(F∘g)| ≤ 10^11·Cder·M^{−1}(1−γ²)^{−1}` on the general region (used by the four-fold
  integration by parts in `t₁`).

The three lemmas below are the ingredients; `Work.FIArea2.R6.lemma_7_1_gen` (a separate module,
so that this one builds before the two analytic inputs land) assembles them.
-/
import Mathlib
import Submission.Work.FIArea2.lemma_7_1_aux
import Submission.Work.FIArea2.lemma_7_1
import Submission.Work.FIArea2.R6.GenRegion

set_option autoImplicit false

namespace Work.FIArea2.R6

open MeasureTheory
open scoped BigOperators
open scoped Topology

noncomputable section

/-- **(i) the trivial bound** of the generalised Lemma 7.1: the Fourier integral (7.1) of a
majorant supported in `[A,B]` with `|f| ≤ Cder` is bounded by `Cder · vol(regG A B γ)`. -/
lemma Fint_le_trivial_gen (M γ A B Cder : ℝ) (f : ℝ → ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hC0 : 0 ≤ Cder)
    (hb : ∀ u : ℝ, |f u| ≤ Cder) (hfsupp : ∀ u : ℝ, f u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hf : Continuous f)
    (hvol : volume (regG A B γ) < ⊤)
    (hvolb : (volume (regG A B γ)).toReal ≤ 2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))
    (u₁ u₂ : ℝ) :
    ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ 2000 * Cder * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have hint := integrable_FintInt_gen γ A B Cder f hvol hf hC0 hb hfsupp u₁ u₂
  have hFeq : Work.FIArea2.Fint f γ u₁ u₂
      = ∫ p : ℝ × ℝ, Work.FIArea2.FintInt f γ u₁ u₂ p := by
    rw [Work.FIArea2.Fint]; rfl
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      Cder * Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) p) :=
    (integrable_indicator_regG A B γ hvol).const_mul Cder
  have hInt : ∫ p : ℝ × ℝ, Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) p
      = (volume (regG A B γ)).toReal := by
    rw [MeasureTheory.integral_indicator_const (1 : ℝ) (measurableSet_regG A B γ), smul_eq_mul,
      mul_one, MeasureTheory.measureReal_def]
  calc ‖Work.FIArea2.Fint f γ u₁ u₂‖
      = ‖∫ p : ℝ × ℝ, Work.FIArea2.FintInt f γ u₁ u₂ p‖ := by rw [hFeq]
    _ ≤ ∫ p : ℝ × ℝ, ‖Work.FIArea2.FintInt f γ u₁ u₂ p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, Cder * Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) p := by
        refine integral_mono hint.norm hmaj (fun p => ?_)
        exact norm_FintInt_le_indicator_gen γ A B Cder f hC0 hb hfsupp u₁ u₂ p
    _ = Cder * ∫ p : ℝ × ℝ, Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) p := by
        rw [integral_const_mul]
    _ = Cder * (volume (regG A B γ)).toReal := by rw [hInt]
    _ ≤ Cder * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) :=
        mul_le_mul_of_nonneg_left hvolb hC0
    _ = 2000 * Cder * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by ring

/-- **(ii) the four-fold integration by parts in `t₁`** of the generalised Lemma 7.1, from the
pointwise Faà di Bruno bound `hpt` on the general region. -/
lemma Fint_le_deriv_gen (M γ A B Cder : ℝ) (f : ℝ → ℝ)
    (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hB0 : 0 ≤ B)
    (hC0 : 0 ≤ Cder) (hf : ContDiff ℝ 4 f)
    (hfsupp : ∀ u : ℝ, f u ≠ 0 → A ≤ u ∧ u ≤ B) (hb : ∀ u : ℝ, |f u| ≤ Cder)
    (hvol : volume (regG A B γ) < ⊤)
    (hvolb : (volume (regG A B γ)).toReal ≤ 2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))
    (hpt : ∀ t₁ t₂ : ℝ, ‖iteratedDeriv 4 (fun s : ℝ => (f (Work.FIArea2.gq γ s t₂) : ℂ)) t₁‖
      ≤ 10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹
        * Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂))
    (u₁ u₂ : ℝ) (hu₁ : u₁ ≠ 0) :
    ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ (2 * Real.pi * |u₁|)⁻¹ ^ 4
      * (10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
      * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
  have hM0 : 0 < M := by linarith
  have h1γ : 0 < 1 - γ ^ 2 := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
  have hCpt0 : 0 ≤ 10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹ := by positivity
  have hint := integrable_FintInt_gen γ A B Cder f hvol hf.continuous hC0 hb hfsupp u₁ u₂
  have hFint := Work.FIArea2.Fint_eq_iterated f γ u₁ u₂ hint
  have hInt : ∫ p : ℝ × ℝ, Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) p
      = (volume (regG A B γ)).toReal := by
    rw [MeasureTheory.integral_indicator_const (1 : ℝ) (measurableSet_regG A B γ), smul_eq_mul,
      mul_one, MeasureTheory.measureReal_def]
  have hinner : ∀ t₂ : ℝ, ‖∫ t₁ : ℝ, ((f (Work.FIArea2.gq γ t₁ t₂) : ℝ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂))‖
      ≤ (2 * Real.pi * |u₁|)⁻¹ ^ 4
        * ((10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹) * ∫ t₁ : ℝ,
            Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂)) := by
    intro t₂
    obtain ⟨hcd, hintd⟩ := contDiff_integrable_hfun_gen A B γ f hγ0 hγ1 hB0 hf hfsupp t₂
    have hsplit : (∫ t₁ : ℝ, ((f (Work.FIArea2.gq γ t₁ t₂) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂)))
        = (∫ t₁ : ℝ, ((f (Work.FIArea2.gq γ t₁ t₂) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁)))
          * Complex.exp (2 * Real.pi * Complex.I * (u₂ * t₂)) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with t₁
      rw [show Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂))
          = Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁))
            * Complex.exp (2 * Real.pi * Complex.I * (u₂ * t₂)) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
      ring
    have hexp2 : ‖Complex.exp (2 * Real.pi * Complex.I * (u₂ * t₂))‖ = 1 := by
      rw [show (2 * Real.pi * Complex.I * (u₂ * t₂) : ℂ)
          = ((2 * Real.pi * (u₂ * t₂) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hsplit, norm_mul, hexp2, mul_one]
    refine (Work.FIArea2.fourier_decay _ u₁ hu₁ hcd hintd).trans ?_
    gcongr
    refine (integral_mono (hintd 4 (le_refl 4)).norm
      ((integrable_indicator_regG_slice A B γ hγ0 hγ1 hB0 t₂).const_mul
        (10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)) ?_).trans (le_of_eq ?_)
    · intro t₁
      exact hpt t₁ t₂
    · rw [integral_const_mul]
  have hmaj : Integrable (fun t₂ : ℝ => (2 * Real.pi * |u₁|)⁻¹ ^ 4
      * ((10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
        * ∫ t₁ : ℝ, Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂))) := by
    have hsec : Integrable (fun t₂ : ℝ => ∫ t₁ : ℝ,
        Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂)) :=
      Integrable.integral_prod_right (integrable_indicator_regG A B γ hvol)
    exact (hsec.const_mul _).const_mul _
  calc ‖Work.FIArea2.Fint f γ u₁ u₂‖
      = ‖∫ t₂ : ℝ, ∫ t₁ : ℝ, ((f (Work.FIArea2.gq γ t₁ t₂) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂))‖ := by rw [hFint]
    _ ≤ ∫ t₂ : ℝ, ‖∫ t₁ : ℝ, ((f (Work.FIArea2.gq γ t₁ t₂) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t₂ : ℝ, (2 * Real.pi * |u₁|)⁻¹ ^ 4
          * ((10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
            * ∫ t₁ : ℝ, Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hmaj
          (Filter.Eventually.of_forall fun t₂ => hinner t₂)
    _ = (2 * Real.pi * |u₁|)⁻¹ ^ 4
          * ((10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
            * ∫ t₂ : ℝ, ∫ t₁ : ℝ, Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂)) := by
        rw [integral_const_mul, integral_const_mul]
    _ = (2 * Real.pi * |u₁|)⁻¹ ^ 4
          * ((10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
            * ∫ p : ℝ × ℝ, Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) p) := by
        congr 2
        exact (integral_prod_symm (fun p : ℝ × ℝ =>
          Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) p)
          (integrable_indicator_regG A B γ hvol)).symm
    _ = (2 * Real.pi * |u₁|)⁻¹ ^ 4
          * ((10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹) * (volume (regG A B γ)).toReal) := by
        rw [hInt]
    _ ≤ (2 * Real.pi * |u₁|)⁻¹ ^ 4
          * ((10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
            * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvolb hCpt0) ?_
        positivity
    _ = (2 * Real.pi * |u₁|)⁻¹ ^ 4 * (10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by ring

/-- The algebra converting the integration-by-parts bound into the shape `B/x²`: multiplying the
bound by `(u²√(1−γ²)√M)²` turns `(2π|u|)^{-4}M^{-1}(1−γ²)^{-1}` into `(2π)^{-4}`. -/
lemma sq_mul_le_gen (M γ u F Cder : ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hu : u ≠ 0)
    (h : F ≤ (2 * Real.pi * |u|)⁻¹ ^ 4 * (10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
        * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))) :
    (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2 * F
      ≤ (2 * Real.pi)⁻¹ ^ 4 * (10 ^ 11 * 2000) * Cder * Real.sqrt M
          * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have hM0 : 0 < M := by linarith
  have h1γ : 0 < 1 - γ ^ 2 := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
  have hsq : (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2 = u ^ 4 * (1 - γ ^ 2) * M := by
    rw [mul_pow, mul_pow, Real.sq_sqrt h1γ.le, Real.sq_sqrt hM0.le]
    ring
  have habs : (|u| : ℝ) ^ 4 = u ^ 4 := by
    rw [show (|u| : ℝ) ^ 4 = ((|u| : ℝ) ^ 2) ^ 2 by ring,
      show u ^ 4 = (u ^ 2) ^ 2 by ring, sq_abs]
  have hkey : (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2
      * ((2 * Real.pi * |u|)⁻¹ ^ 4 * (10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹))
      = (2 * Real.pi)⁻¹ ^ 4 * 10 ^ 11 * Cder := by
    rw [hsq, inv_pow, mul_pow, habs, inv_pow]
    field_simp
  have hnonneg : 0 ≤ (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2 := sq_nonneg _
  calc (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2 * F
      ≤ (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2
        * ((2 * Real.pi * |u|)⁻¹ ^ 4 * (10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))) :=
        mul_le_mul_of_nonneg_left h hnonneg
    _ = ((u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2
          * ((2 * Real.pi * |u|)⁻¹ ^ 4 * (10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)))
        * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by ring
    _ = ((2 * Real.pi)⁻¹ ^ 4 * 10 ^ 11 * Cder)
        * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by rw [hkey]
    _ = (2 * Real.pi)⁻¹ ^ 4 * (10 ^ 11 * 2000) * Cder * Real.sqrt M
          * Real.log (2 + 1 / (1 - γ ^ 2)) := by ring

/-- **The generalised Lemma 7.1**, assembled from the three ingredients above (the volume bound and
the pointwise Faà di Bruno bound enter as the two hypotheses `hvolb`, `hpt`, which
`Work.FIArea2.R6.lemma_7_1_gen` discharges from `vol_regG_le` and `deriv4_pointwise_gen`).

The final constant `10^13` is deliberately generous: `4·(2π)^{−4}·10^11·2000 ≈ 5.1·10^11`, and
only the *shape* of the bound matters downstream. -/
theorem lemma_7_1_gen_core (M : ℝ) (hM : 1 ≤ M) (A B Cder : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hB : B ≤ 64 * M) (hCder : 1 ≤ Cder)
    (f : ℝ → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ContDiff ℝ 4 f) (hfsupp : ∀ u : ℝ, f u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j f u| ≤ Cder * M ^ (-(j : ℝ)))
    (hvol : volume (regG A B γ) < ⊤)
    (hvolb : (volume (regG A B γ)).toReal ≤ 2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))
    (hpt : ∀ t₁ t₂ : ℝ, ‖iteratedDeriv 4 (fun s : ℝ => (f (Work.FIArea2.gq γ s t₂) : ℂ)) t₁‖
      ≤ 10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹
        * Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂))
    (u₁ u₂ : ℝ) :
    ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ 10 ^ 13 * Cder
      * (1 + u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M)⁻¹
      * (1 + u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M)⁻¹
      * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have hM0 : 0 < M := by linarith
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have h1γ : 0 < 1 - γ ^ 2 := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
  set L : ℝ := Real.log (2 + 1 / (1 - γ ^ 2)) with hL
  have hLpos : 0 < L := by
    rw [hL]
    apply Real.log_pos
    have h1 : 0 < 1 / (1 - γ ^ 2) := by positivity
    linarith
  set x : ℝ := u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M with hx
  set y : ℝ := u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M with hy
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  set A' : ℝ := 2000 * Cder * Real.sqrt M * L with hAdef
  set B' : ℝ := (2 * Real.pi)⁻¹ ^ 4 * (10 ^ 11 * 2000) * Cder * Real.sqrt M * L with hBdef
  have hC0 : 0 ≤ Cder := le_trans zero_le_one hCder
  have hL0 : 0 ≤ L := hLpos.le
  have hCL : 0 ≤ Cder * Real.sqrt M * L :=
    mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg M)) hL0
  have hA0 : 0 ≤ A' := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B' := by rw [hBdef]; positivity
  have hb : ∀ u : ℝ, |f u| ≤ Cder := by
    intro u
    have h0 := hfd 0 (by norm_num) u
    simpa using h0
  have hF0 : 0 ≤ ‖Work.FIArea2.Fint f γ u₁ u₂‖ := norm_nonneg _
  have hAbound : ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ A' := by
    rw [hAdef, hL]
    exact Fint_le_trivial_gen M γ A B Cder f hγ0 hγ1 hC0 hb hfsupp hf.continuous hvol hvolb u₁ u₂
  have hBbound : x ^ 2 * ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ B' := by
    rcases eq_or_ne u₁ 0 with h0 | h0
    · have hx0' : x = 0 := by rw [hx, h0]; ring
      have hzero : x ^ 2 * ‖Work.FIArea2.Fint f γ u₁ u₂‖ = 0 := by rw [hx0']; ring
      rw [hzero]
      exact hB0
    · have h1 := Fint_le_deriv_gen M γ A B Cder f hM hγ0 hγ1 (le_trans hA.le hAB) hC0 hf
        hfsupp hb hvol hvolb hpt u₁ u₂ h0
      rw [hx, hBdef, hL]
      exact sq_mul_le_gen M γ u₁ _ Cder hM hγ0 hγ1 h0 h1
  have hCbound : y ^ 2 * ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ B' := by
    rcases eq_or_ne u₂ 0 with h0 | h0
    · have hy0' : y = 0 := by rw [hy, h0]; ring
      have hzero : y ^ 2 * ‖Work.FIArea2.Fint f γ u₁ u₂‖ = 0 := by rw [hy0']; ring
      rw [hzero]
      exact hB0
    · have h1 := Fint_le_deriv_gen M γ A B Cder f hM hγ0 hγ1 (le_trans hA.le hAB) hC0 hf
        hfsupp hb hvol hvolb hpt u₂ u₁ h0
      have h2 : ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ (2 * Real.pi * |u₂|)⁻¹ ^ 4
          * (10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
        rw [Work.FIArea2.Fint_swap f γ u₁ u₂]
        exact h1
      rw [hy, hBdef, hL]
      exact sq_mul_le_gen M γ u₂ _ Cder hM hγ0 hγ1 h0 h2
  have hcomb := Work.FIArea2.combine_bounds x y A' B' B' ‖Work.FIArea2.Fint f γ u₁ u₂‖
    hx0 hy0 hA0 hB0 hB0 hF0 hAbound hBbound hCbound
  have hden : 0 < (1 + x) * (1 + y) := by positivity
  have h1296 : (1296 : ℝ) ≤ (2 * Real.pi) ^ 4 := by
    have h1 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) h1 4
    norm_num at h2
    linarith
  have hscale : (2 * Real.pi)⁻¹ ^ 4 * (10 ^ 11 * 2000) ≤ 10 ^ 12 := by
    rw [inv_pow]
    have hpos : (0 : ℝ) < (2 * Real.pi) ^ 4 := by positivity
    rw [inv_mul_le_iff₀ hpos]
    nlinarith [h1296]
  have hBs : B' ≤ 10 ^ 12 * Cder * Real.sqrt M * L := by
    rw [hBdef]
    calc (2 * Real.pi)⁻¹ ^ 4 * (10 ^ 11 * 2000) * Cder * Real.sqrt M * L
        = ((2 * Real.pi)⁻¹ ^ 4 * (10 ^ 11 * 2000)) * (Cder * Real.sqrt M * L) := by ring
      _ ≤ 10 ^ 12 * (Cder * Real.sqrt M * L) := mul_le_mul_of_nonneg_right hscale hCL
      _ = 10 ^ 12 * Cder * Real.sqrt M * L := by ring
  have hAs : A' ≤ 10 ^ 12 * Cder * Real.sqrt M * L := by
    rw [hAdef]
    calc 2000 * Cder * Real.sqrt M * L = 2000 * (Cder * Real.sqrt M * L) := by ring
      _ ≤ 10 ^ 12 * (Cder * Real.sqrt M * L) :=
          mul_le_mul_of_nonneg_right (by norm_num : (2000 : ℝ) ≤ 10 ^ 12) hCL
      _ = 10 ^ 12 * Cder * Real.sqrt M * L := by ring
  have hmax : 4 * max A' (max B' B') ≤ 10 ^ 13 * Cder * Real.sqrt M * L := by
    have h1 : max B' B' ≤ 10 ^ 12 * Cder * Real.sqrt M * L := le_of_eq_of_le (max_self B') hBs
    have h2 : max A' (max B' B') ≤ 10 ^ 12 * Cder * Real.sqrt M * L := max_le hAs h1
    have h3 : 4 * (10 ^ 12 * Cder * Real.sqrt M * L) ≤ 10 ^ 13 * Cder * Real.sqrt M * L := by
      have h4 : (4 : ℝ) * 10 ^ 12 ≤ 10 ^ 13 := by norm_num
      calc 4 * (10 ^ 12 * Cder * Real.sqrt M * L)
          = (4 * 10 ^ 12) * (Cder * Real.sqrt M * L) := by ring
        _ ≤ 10 ^ 13 * (Cder * Real.sqrt M * L) := mul_le_mul_of_nonneg_right h4 hCL
        _ = 10 ^ 13 * Cder * Real.sqrt M * L := by ring
    calc 4 * max A' (max B' B') ≤ 4 * (10 ^ 12 * Cder * Real.sqrt M * L) := by linarith
      _ ≤ 10 ^ 13 * Cder * Real.sqrt M * L := h3
  calc ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ 4 * max A' (max B' B') / ((1 + x) * (1 + y)) := hcomb
    _ ≤ 10 ^ 13 * Cder * Real.sqrt M * L / ((1 + x) * (1 + y)) :=
        div_le_div_of_nonneg_right hmax hden.le
    _ = 10 ^ 13 * Cder * (1 + x)⁻¹ * (1 + y)⁻¹ * Real.sqrt M * L := by
        rw [div_eq_mul_inv, mul_inv]
        ring
    _ = 10 ^ 13 * Cder
        * (1 + u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M)⁻¹
        * (1 + u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M)⁻¹
        * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
        rw [hx, hy, hL]

end

end Work.FIArea2.R6
