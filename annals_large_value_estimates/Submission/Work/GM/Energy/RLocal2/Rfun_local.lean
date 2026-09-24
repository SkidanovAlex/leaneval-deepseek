import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.RLocal.Bump
import Submission.Work.GM.Energy.RLocal.Identity
import Submission.Work.GM.Energy.RLocal.Estimate

namespace Work.GM.Energy.RLocal2

open Complex Finset MeasureTheory
open scoped BigOperators Interval FourierTransform
set_option autoImplicit false

open Work.GM.Energy.RLocal
open Submission.GM (Rfun)

/-!
## Auxiliary lemmas for the assembly of GM Lemma 11.7

The proof splits into two regimes.

* `K ≤ 3T/2` ("small window"): use the Fourier identity `cutoff_bound` with truncation
  `L = K/100`; the image of `[-L,L]` under `ξ ↦ v e^{2πξ/T}` lies in the window (because
  `2πL/T ≤ 3/25`) and the tail costs `O(K^{-m})`.

* `K ≥ 3T/2` ("large window"): the window contains the interval `[e^{-1/(2T)}, e^{1/(2T)}]`
  around `1`, on which `‖R‖ ≥ |W|/2` (every phase moves by less than `1/2`), so the window
  integral is at least `|W|/(4T)`.
-/

/-- The mass of `‖𝓕ψ‖` beyond `|ξ| = L` is bounded by `C / L^m` for **every** positive `L`
(the range `0 < L < 1` being absorbed into the constant). -/
theorem fourierTail_bound_pos (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → fourierTail L ≤ C / L ^ m := by
  obtain ⟨Ct, hCt0, hCt⟩ := fourierTail_bound m hm
  set B : ℝ := ∫ ξ : ℝ, ‖𝓕 PsiBump ξ‖ with hB
  have hB0 : 0 ≤ B := integral_nonneg fun ξ => norm_nonneg _
  have htailB : ∀ L : ℝ, fourierTail L ≤ B := by
    intro L
    have haesm : AEStronglyMeasurable
        (fun ξ : ℝ => if L < |ξ| then ‖𝓕 PsiBump ξ‖ else 0) volume :=
      (continuous_fourier_PsiBump.norm).aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const measurable_abs)
    have hint : Integrable (fun ξ : ℝ => if L < |ξ| then ‖𝓕 PsiBump ξ‖ else 0) :=
      Integrable.mono' PsiBump_fourier_integrable.norm haesm (by
        filter_upwards with ξ
        by_cases h : L < |ξ| <;> simp [h, norm_nonneg])
    rw [fourierTail, hB]
    exact integral_mono_ae hint PsiBump_fourier_integrable.norm (by
      filter_upwards with ξ
      by_cases h : L < |ξ| <;> simp [h, norm_nonneg])
  refine ⟨max (Ct + 1) (B + 1), lt_max_of_lt_left (by linarith), fun L hL => ?_⟩
  have hm0 : 0 < L ^ m := pow_pos hL m
  rcases le_or_gt 1 L with h1 | h1
  · refine (hCt L h1).trans ?_
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hm0)
    linarith [le_max_left (Ct + 1) (B + 1)]
  · have h1L : (1 : ℝ) ≤ 1 / L ^ m := by
      rw [le_div_iff₀ hm0, one_mul]
      exact pow_le_one₀ (le_of_lt hL) (le_of_lt h1)
    calc fourierTail L ≤ B := htailB L
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * (1 / L ^ m) := mul_le_mul_of_nonneg_left h1L hB0
      _ ≤ max (Ct + 1) (B + 1) * (1 / L ^ m) :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_right (Ct + 1) (B + 1)]) (by positivity)
      _ = max (Ct + 1) (B + 1) / L ^ m := by rw [mul_one_div]

/-- `‖Rfun W ·‖` is interval integrable on every interval (measurable and bounded). -/
theorem intervalIntegrable_norm_Rfun (W : Finset ℝ) (c d : ℝ) :
    IntervalIntegrable (fun u : ℝ => ‖Rfun W u‖) volume c d := by
  set g : ℝ → ℂ := fun u => ∑ t ∈ W, Complex.exp (Complex.I * ((t * Real.log |u| : ℝ) : ℂ))
    with hg
  have hgm : Measurable g := by
    rw [hg]
    refine Finset.measurable_sum W fun t ht => ?_
    refine Complex.continuous_exp.measurable.comp ?_
    refine measurable_const.mul ?_
    exact Complex.continuous_ofReal.measurable.comp
      ((Real.measurable_log.comp measurable_abs).const_mul t)
  have hbounded : ∀ u, ‖g u‖ ≤ (W.card : ℝ) := by
    intro u
    have h1 : ‖g u‖ ≤ ∑ t ∈ W,
        ‖Complex.exp (Complex.I * ((t * Real.log |u| : ℝ) : ℂ))‖ := by
      rw [hg]; exact norm_sum_le _ _
    have h2 : ∑ t ∈ W, ‖Complex.exp (Complex.I * ((t * Real.log |u| : ℝ) : ℂ))‖
        ≤ ∑ t ∈ W, (1 : ℝ) := by
      refine Finset.sum_le_sum fun t ht => ?_
      rw [mul_comm]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
    calc ‖g u‖ ≤ ∑ t ∈ W,
          ‖Complex.exp (Complex.I * ((t * Real.log |u| : ℝ) : ℂ))‖ := h1
      _ ≤ ∑ t ∈ W, (1 : ℝ) := h2
      _ = (W.card : ℝ) := by simp
  have hIntG : IntegrableOn (fun u : ℝ => ‖g u‖) (Ι c d) volume := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ hgm.norm.aestronglyMeasurable (W.card : ℝ) ?_
    · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
    · filter_upwards with u
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hbounded u
  have hglob : (fun u : ℝ => Rfun W u) =ᵐ[volume] g := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (Real.volume_singleton (a := 0))
    intro u hu
    by_contra h0
    have hne : u ≠ 0 := fun h => h0 (by simp [h])
    exact hu (by
      have hpos : 0 < |u| := abs_pos.mpr hne
      rw [hg]
      simp only []
      unfold Submission.GM.Rfun
      exact Finset.sum_congr rfl fun t ht => ofReal_cpow_pureImag |u| hpos t)
  have hae : (fun u : ℝ => ‖Rfun W u‖) =ᵐ[volume.restrict (Ι c d)] (fun u : ℝ => ‖g u‖) := by
    have h1 : ∀ᵐ u ∂(volume : Measure ℝ), ‖Rfun W u‖ = ‖g u‖ :=
      hglob.mono fun u hu => by simpa using congrArg (fun z : ℂ => ‖z‖) hu
    exact MeasureTheory.ae_restrict_of_ae (s := (Ι c d)) h1
  rw [intervalIntegrable_iff]
  exact hIntG.congr hae.symm

/-- `Rfun W 1 = |W|`: all the phases vanish at `v = 1`. -/
theorem Rfun_one (W : Finset ℝ) : Rfun W 1 = (W.card : ℂ) := by
  rw [Rfun_pos_eq_sum W zero_lt_one]
  simp [Complex.one_cpow]

/-- Every summand `|u|^{it}` has modulus `1` and differs from `|1|^{it} = 1` in phase by at
most `|t log u|`. -/
theorem Rfun_sub_one_norm_le {W : Finset ℝ} {T : ℝ} (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T)
    {u : ℝ} (hu : 0 < u) :
    ‖Rfun W u - Rfun W 1‖ ≤ T * (W.card : ℝ) * |Real.log u| := by
  have h1 : Rfun W u = ∑ t ∈ W, Complex.exp (Complex.I * ((t * Real.log u : ℝ) : ℂ)) := by
    rw [Rfun_pos_eq_sum W hu]
    exact Finset.sum_congr rfl fun t _ => ofReal_cpow_pureImag u hu t
  have h2 : Rfun W 1 = ∑ t ∈ W, (1 : ℂ) := by
    rw [Rfun_one]
    simp
  rw [h1, h2, ← Finset.sum_sub_distrib]
  calc ‖∑ t ∈ W, (Complex.exp (Complex.I * ((t * Real.log u : ℝ) : ℂ)) - 1)‖
      ≤ ∑ t ∈ W, ‖Complex.exp (Complex.I * ((t * Real.log u : ℝ) : ℂ)) - 1‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ W, |t * Real.log u| := by
        refine Finset.sum_le_sum fun t ht => ?_
        simpa [Real.norm_eq_abs] using
          Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * Real.log u)
    _ = ∑ t ∈ W, |t| * |Real.log u| :=
        Finset.sum_congr rfl fun t _ => abs_mul t (Real.log u)
    _ = (∑ t ∈ W, |t|) * |Real.log u| := by rw [Finset.sum_mul]
    _ ≤ (T * (W.card : ℝ)) * |Real.log u| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc (∑ t ∈ W, |t|) ≤ ∑ t ∈ W, T := by
              refine Finset.sum_le_sum fun t ht => ?_
              rw [abs_of_nonneg (hW t ht).1]
              exact (hW t ht).2
          _ = T * (W.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = T * (W.card : ℝ) * |Real.log u| := by ring

/-- For `0 ≤ x ≤ 1/2`, `e^x ≤ 1/(1-x)`. -/
theorem exp_le_inv_one_sub {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 / (1 - x) := by
  have hx : 0 < 1 - x := by linarith
  have hlog : Real.log (1 - x) ≤ (1 - x) - 1 := Real.log_le_sub_one_of_pos hx
  have hlog' : x ≤ Real.log (1 / (1 - x)) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hx), Real.log_one, zero_sub]
    linarith
  exact (Real.le_log_iff_exp_le (by positivity)).mp hlog'

/-- **Large-window regime.**  If `K ≥ 3T/2` then the interval `[e^{-1/(2T)}, e^{1/(2T)}]` lies
inside the window `[v-K/T, v+K/T]` (for `v ≍ 1`) and there every summand of `R` is within
phase `1/2` of its value at `1`; hence `|W| = ‖R(1)‖` is controlled by the window integral. -/
theorem window_integral_lower {W : Finset ℝ} {T v K : ℝ} (hT : 1 ≤ T)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) (hv : v ∈ Set.Icc (1 / 2 : ℝ) 2) (hK : 3 / 2 * T ≤ K) :
    (W.card : ℝ) ≤ 4 * T * (∫ u in v - K / T..v + K / T, ‖Rfun W u‖) := by
  have hTpos : 0 < T := by linarith
  have hKT : 3 / 2 ≤ K / T := (le_div_iff₀ hTpos).mpr hK
  set y : ℝ := 1 / (2 * T) with hydef
  have hypos : 0 < y := by rw [hydef]; positivity
  have hy_half : y ≤ 1 / 2 := by
    rw [hydef, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * T)]
    linarith
  have hexp_hi : Real.exp y ≤ 1 / (1 - y) := exp_le_inv_one_sub (le_of_lt hypos) hy_half
  have hyT : T * y = 1 / 2 := by rw [hydef]; field_simp
  have hlo : v - K / T ≤ Real.exp (-y) := by
    have h1 : v - K / T ≤ 1 / 2 := by linarith [hv.2, hKT]
    have h2 : (1 : ℝ) / 2 ≤ Real.exp (-y) := by
      have h3 := Real.add_one_le_exp (-y)
      linarith
    linarith
  have hhi : Real.exp y ≤ v + K / T := by
    have h1 : (2 : ℝ) ≤ v + K / T := by linarith [hv.1, hKT]
    have h2 : Real.exp y ≤ 2 := by
      have h3 : 1 / (1 - y) ≤ 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - y)]
        linarith
      linarith
    linarith
  have hpoint : ∀ u ∈ Set.Icc (Real.exp (-y)) (Real.exp y), (W.card : ℝ) / 2 ≤ ‖Rfun W u‖ := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu.1
    have hlogu : |Real.log u| ≤ y := by
      rw [abs_le]
      exact ⟨(Real.le_log_iff_exp_le hu0).mpr hu.1,
             (Real.log_le_iff_le_exp hu0).mpr hu.2⟩
    have hdiff := Rfun_sub_one_norm_le hW hu0
    have hcard : ‖Rfun W 1‖ = (W.card : ℝ) := by simp [Rfun_one]
    have hstep : ‖Rfun W u - Rfun W 1‖ ≤ (W.card : ℝ) / 2 := by
      calc ‖Rfun W u - Rfun W 1‖ ≤ T * (W.card : ℝ) * |Real.log u| := hdiff
        _ ≤ T * (W.card : ℝ) * y := by
            refine mul_le_mul_of_nonneg_left hlogu ?_
            positivity
        _ = (W.card : ℝ) / 2 := by
            calc T * (W.card : ℝ) * y = (W.card : ℝ) * (T * y) := by ring
              _ = (W.card : ℝ) * (1 / 2) := by rw [hyT]
              _ = (W.card : ℝ) / 2 := by ring
    have htri := abs_norm_sub_norm_le (Rfun W 1) (Rfun W u)
    rw [abs_le, ← norm_sub_rev (Rfun W u) (Rfun W 1), hcard] at htri
    linarith [htri.2, hstep]
  have hInt : (Real.exp y - Real.exp (-y)) * ((W.card : ℝ) / 2)
      ≤ ∫ u in Real.exp (-y)..Real.exp y, ‖Rfun W u‖ := by
    have hle : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)
    have h1 := intervalIntegral.integral_mono_on hle
      (Continuous.intervalIntegrable continuous_const _ _)
      (intervalIntegrable_norm_Rfun W _ _) hpoint
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h1
  have hwindow : (∫ u in Real.exp (-y)..Real.exp y, ‖Rfun W u‖)
      ≤ ∫ u in v - K / T..v + K / T, ‖Rfun W u‖ :=
    intervalIntegral.integral_mono_interval hlo (Real.exp_le_exp.mpr (by linarith)) hhi
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (intervalIntegrable_norm_Rfun W _ _)
  have hexp_sub : y ≤ Real.exp y - Real.exp (-y) := by
    have h2 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
    have h3 : Real.exp (-y) ≤ 1 := by
      have h0 : Real.exp 0 = 1 := Real.exp_zero
      rw [← h0]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hlens : (2 : ℝ) ≤ 4 * T * (Real.exp y - Real.exp (-y)) := by
    have h4 : 4 * T * y = 2 := by
      calc 4 * T * y = 4 * (T * y) := by ring
        _ = 4 * (1 / 2) := by rw [hyT]
        _ = 2 := by norm_num
    nlinarith [hexp_sub, h4]
  calc (W.card : ℝ) = 2 * ((W.card : ℝ) / 2) := by ring
    _ ≤ (4 * T * (Real.exp y - Real.exp (-y))) * ((W.card : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hlens (by positivity)
    _ = 4 * T * ((Real.exp y - Real.exp (-y)) * ((W.card : ℝ) / 2)) := by ring
    _ ≤ 4 * T * (∫ u in Real.exp (-y)..Real.exp y, ‖Rfun W u‖) :=
        mul_le_mul_of_nonneg_left hInt (by linarith)
    _ ≤ 4 * T * (∫ u in v - K / T..v + K / T, ‖Rfun W u‖) :=
        mul_le_mul_of_nonneg_left hwindow (by linarith)

/-- **Small-window regime.**  If `K ≤ 3T/2`, the Fourier identity `cutoff_bound` with truncation
`L = K/100` gives the claimed bound. -/
theorem Rfun_bound_small (m : ℕ) {Ct : ℝ}
    (hCtail : ∀ L : ℝ, 0 < L → fourierTail L ≤ Ct / L ^ m)
    {T v K : ℝ} (hT : 1 ≤ T) (hv : v ∈ Set.Icc (1 / 2 : ℝ) 2) (hK : 1 ≤ K)
    (hKT : K ≤ 3 / 2 * T) (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) :
    ‖Rfun W v‖ ≤ fourierA * T * (∫ u in v - K / T..v + K / T, ‖Rfun W u‖)
      + (Ct * ((100 : ℝ) ^ m)) / K ^ (m : ℝ) * (W.card : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hvpos : 0 < v := by linarith [hv.1]
  have hKpos : 0 < K := by linarith
  have hKT' : K / T ≤ 3 / 2 := (div_le_iff₀ hTpos).mpr hKT
  have hKT0 : 0 ≤ K / T := div_nonneg hKpos.le hTpos.le
  set L : ℝ := K / 100 with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  set x : ℝ := 2 * Real.pi * L / T with hxdef
  have hx_eq : x = (Real.pi / 50) * (K / T) := by
    rw [hxdef, hLdef]; field_simp; ring
  have hx_le : x ≤ 3 / 25 := by
    rw [hx_eq]
    have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
    calc (Real.pi / 50) * (K / T) ≤ (Real.pi / 50) * (3 / 2) :=
          mul_le_mul_of_nonneg_left hKT' (by positivity)
      _ = 3 * Real.pi / 100 := by ring
      _ ≤ 3 * 4 / 100 := by linarith
      _ = 3 / 25 := by norm_num
  have hx_nonneg : 0 ≤ x := by rw [hx_eq]; positivity
  have hexp_le : Real.exp x ≤ 1 / (1 - x) := exp_le_inv_one_sub hx_nonneg (by linarith)
  have hexp_sub : Real.exp x - 1 ≤ 2 * x := by
    have hx1 : (1 - x) ≠ 0 := by linarith
    have h2 : 1 / (1 - x) - 1 = x / (1 - x) := by
      field_simp
      ring
    have h3 : x / (1 - x) ≤ 2 * x := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - x)]
      nlinarith
    linarith
  have hexp_neg : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x); linarith
  -- containment of the image of `[-L,L]` in the window
  have hb_le : v * Real.exp x ≤ v + K / T := by
    have hexp1 : 0 ≤ Real.exp x - 1 := by
      have h := Real.one_le_exp_iff.mpr hx_nonneg
      linarith
    have h1 : v * (Real.exp x - 1) ≤ 2 * (2 * x) := by
      calc v * (Real.exp x - 1) ≤ 2 * (Real.exp x - 1) :=
            mul_le_mul_of_nonneg_right hv.2 hexp1
        _ ≤ 2 * (2 * x) := by linarith [hexp_sub]
    have h2 : 4 * x ≤ K / T := by
      rw [hx_eq]
      have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
      calc 4 * ((Real.pi / 50) * (K / T)) = (4 * Real.pi / 50) * (K / T) := by ring
        _ ≤ (4 * 4 / 50) * (K / T) := mul_le_mul_of_nonneg_right (by linarith) hKT0
        _ = 16 / 50 * (K / T) := by norm_num
        _ ≤ K / T := by linarith
    linarith
  have hlow_le : v - K / T ≤ v * Real.exp (-x) := by
    have h2 : v * (1 - Real.exp (-x)) ≤ v * x :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith [hv.1])
    have h3 : v * x ≤ K / T := by
      have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
      calc v * x ≤ 2 * x := mul_le_mul_of_nonneg_right hv.2 hx_nonneg
        _ = 2 * ((Real.pi / 50) * (K / T)) := by rw [hx_eq]
        _ = (2 * Real.pi / 50) * (K / T) := by ring
        _ ≤ (2 * 4 / 50) * (K / T) := mul_le_mul_of_nonneg_right (by linarith) hKT0
        _ = 8 / 50 * (K / T) := by norm_num
        _ ≤ K / T := by linarith
    linarith
  have ha_ge : (1 : ℝ) / 4 ≤ v * Real.exp (-x) := by
    have h1 : (1 : ℝ) / 2 ≤ v := hv.1
    have h2 : (1 : ℝ) / 2 ≤ Real.exp (-x) := by linarith
    calc (1 : ℝ) / 4 = (1 / 2) * (1 / 2) := by norm_num
      _ ≤ v * Real.exp (-x) := mul_le_mul h1 h2 (by norm_num) (by linarith)
  have ha_pos : 0 < v * Real.exp (-x) := by positivity
  -- the substitution and the cutoff
  have hsub := window_subst W hvpos hTpos hLpos ha_pos
    (by rw [← hxdef])
    (by rw [hxdef])
  have hcut := cutoff_bound T hTpos W hW hvpos hLpos
  have hmono : (∫ u in v * Real.exp (-x)..v * Real.exp x, ‖Rfun W u‖)
      ≤ ∫ u in v - K / T..v + K / T, ‖Rfun W u‖ :=
    intervalIntegral.integral_mono_interval hlow_le
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by linarith [hv.1]))
      hb_le (Filter.Eventually.of_forall fun u => norm_nonneg _)
      (intervalIntegrable_norm_Rfun W _ _)
  -- the tail
  have htail : fourierTail L ≤ Ct / L ^ m := hCtail L hLpos
  have htail_val : Ct / L ^ m = Ct * ((100 : ℝ) ^ m) / K ^ m := by
    rw [hLdef, div_pow, div_div_eq_mul_div]
  -- auxiliary nonnegativity
  have hA0 : 0 ≤ fourierA := fourierA_nonneg
  have hI0 : 0 ≤ ∫ u in v * Real.exp (-x)..v * Real.exp x, ‖Rfun W u‖ :=
    intervalIntegral.integral_nonneg
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by linarith [hv.1]))
      (fun u _ => norm_nonneg _)
  have hfac : T / (2 * Real.pi * (v * Real.exp (-x))) ≤ T := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (0 : ℝ) < v * Real.exp (-x) := by positivity
    have h3 : (1 : ℝ) ≤ 2 * Real.pi * (v * Real.exp (-x)) := by
      nlinarith [h2, Real.pi_gt_three, ha_ge]
    nlinarith [h3, hTpos]
  have hstep1 : fourierA * (∫ ξ in (-L)..L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
      ≤ fourierA * (T * (∫ u in v * Real.exp (-x)..v * Real.exp x, ‖Rfun W u‖)) := by
    refine mul_le_mul_of_nonneg_left ?_ hA0
    calc (∫ ξ in (-L)..L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
        ≤ (T / (2 * Real.pi * (v * Real.exp (-x))))
            * (∫ u in v * Real.exp (-x)..v * Real.exp x, ‖Rfun W u‖) := hsub
      _ ≤ T * (∫ u in v * Real.exp (-x)..v * Real.exp x, ‖Rfun W u‖) :=
          mul_le_mul_of_nonneg_right hfac hI0
  have hstep2 : fourierA * (T * (∫ u in v * Real.exp (-x)..v * Real.exp x, ‖Rfun W u‖))
      ≤ fourierA * (T * (∫ u in v - K / T..v + K / T, ‖Rfun W u‖)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hTpos.le) hA0
  have htail' : (W.card : ℝ) * fourierTail L
      ≤ (Ct * ((100 : ℝ) ^ m)) / K ^ (m : ℝ) * (W.card : ℝ) := by
    have h1 : fourierTail L ≤ Ct * ((100 : ℝ) ^ m) / K ^ m := htail.trans_eq htail_val
    calc (W.card : ℝ) * fourierTail L = fourierTail L * (W.card : ℝ) := by ring
      _ ≤ (Ct * ((100 : ℝ) ^ m)) / K ^ (m : ℝ) * (W.card : ℝ) := by
          rw [Real.rpow_natCast]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
  calc ‖Rfun W v‖
      ≤ fourierA * (∫ ξ in (-L)..L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
          + (W.card : ℝ) * fourierTail L := hcut
    _ ≤ fourierA * (T * (∫ u in v - K / T..v + K / T, ‖Rfun W u‖))
          + (Ct * ((100 : ℝ) ^ m)) / K ^ (m : ℝ) * (W.card : ℝ) :=
        add_le_add (hstep1.trans hstep2) htail'
    _ = fourierA * T * (∫ u in v - K / T..v + K / T, ‖Rfun W u‖)
          + (Ct * ((100 : ℝ) ^ m)) / K ^ (m : ℝ) * (W.card : ℝ) := by ring

/-- **GM Lemma 11.7** (the function `R` is locally constant at scale `1/T`): for `v ≍ 1` the
value `R(v) = Σ_{t∈W} |v|^{it}` is controlled by the average of `‖R‖` over a window of length
`K/T`, up to a `K^{-m}` multiple of `|W|`.

(All the ingredients are already present and sorry-free in the
`Submission/Work/GM/Energy/RLocal/` directory, importable via `depends_on`:
`Bump.psiBump` — a bump that is `1` on `[0,1]`, supported in `[-1/3,4/3]`, `C^∞`, compact support;
`Identity.PsiBump_fourier_inversion'` — the Fourier inversion identity;
`Identity.Rfun_pos_eq_sum`; `Estimate.fourierTail_bound`; `Estimate.window_subst`.
Only the final assembly into the stated inequality remains.) -/
theorem Rfun_local (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      ∀ (v : ℝ), v ∈ Set.Icc (1 / 2 : ℝ) 2 → ∀ (K : ℝ), 1 ≤ K →
        ‖Submission.GM.Rfun W v‖ ≤
          C * T * (∫ v' in v - K / T..v + K / T, ‖Submission.GM.Rfun W v'‖)
            + C / K ^ (m : ℝ) * (W.card : ℝ) := by
  obtain ⟨Ct, hCt_pos, hCtail⟩ := fourierTail_bound_pos m hm
  have hCfourierA : 0 ≤ fourierA := fourierA_nonneg
  have hCpos : 0 < 5 + fourierA + Ct * ((100 : ℝ) ^ m) := by
    have h1 : 0 < Ct * ((100 : ℝ) ^ m) := by positivity
    linarith
  refine ⟨5 + fourierA + Ct * ((100 : ℝ) ^ m), hCpos, ?_⟩
  intro T hT W hW v hv K hK
  have hTpos : 0 < T := by linarith
  have hKpos : 0 < K := by linarith
  have hKpow : 0 < K ^ (m : ℝ) := Real.rpow_pos_of_pos hKpos m
  have hcard : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
  have hG : 0 ≤ ∫ u in v - K / T..v + K / T, ‖Rfun W u‖ :=
    intervalIntegral.integral_nonneg (by
      have h : 0 < K / T := div_pos hKpos hTpos
      linarith) fun u _ => norm_nonneg _
  by_cases hcase : K ≤ 3 / 2 * T
  · have hsmall := Rfun_bound_small m hCtail hT hv hK hcase W hW
    have hCge : fourierA ≤ 5 + fourierA + Ct * ((100 : ℝ) ^ m) := by
      have : 0 < Ct * ((100 : ℝ) ^ m) := by positivity
      linarith
    have hCge2 : Ct * ((100 : ℝ) ^ m) ≤ 5 + fourierA + Ct * ((100 : ℝ) ^ m) := by
      linarith [fourierA_nonneg]
    refine hsmall.trans ?_
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge hTpos.le) hG
    · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCge2 hKpow.le) hcard
  · push_neg at hcase
    have hpeak := window_integral_lower hT hW hv (le_of_lt hcase)
    have hnorm : ‖Rfun W v‖ ≤ (W.card : ℝ) := Work.GM.S3.Rfun_norm_le_card W v
    refine (hnorm.trans hpeak).trans ?_
    have hC4 : (4 : ℝ) ≤ 5 + fourierA + Ct * ((100 : ℝ) ^ m) := by
      have h1 : 0 < Ct * ((100 : ℝ) ^ m) := by positivity
      linarith [fourierA_nonneg]
    have hC4' : 4 * T ≤ (5 + fourierA + Ct * ((100 : ℝ) ^ m)) * T :=
      mul_le_mul_of_nonneg_right hC4 hTpos.le
    have hmono : 4 * T * (∫ u in v - K / T..v + K / T, ‖Rfun W u‖)
        ≤ (5 + fourierA + Ct * ((100 : ℝ) ^ m)) * T
          * (∫ u in v - K / T..v + K / T, ‖Rfun W u‖) :=
      mul_le_mul_of_nonneg_right hC4' hG
    have h2 : 0 ≤ (5 + fourierA + Ct * ((100 : ℝ) ^ m)) / K ^ (m : ℝ) * (W.card : ℝ) :=
      mul_nonneg (div_nonneg (by positivity) hKpow.le) hcard
    linarith [hmono, h2]

end Work.GM.Energy.RLocal2
