import Mathlib
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.wideTolAux

/-!
# The fundamental theorem of calculus for the wide-end matching phase

`Work.Drive.wideSigma ta w d lam` is the `period`-shifting matching phase of the chord sweep at
the wide end (`Submission/Work/Drive/sweepFamWideTolDefs.lean`): the piecewise affine function
whose rate is `Work.Drive.wideRho w d lam ∘ sweepParam`.  This file proves the corresponding
fundamental theorem of calculus,

  `∫ t in a..b, wideRho w d lam (sweepParam t) = wideSigma ta w d lam b - wideSigma ta w d lam a`,

for all reals `w`, `d` with `w + d = period` (no sign restriction on `w` or `d`).

No information about the knot is needed.  `wideSigma` is piecewise affine with four pieces per
period, hence Lipschitz on every compact set and differentiable off a countable (null) set, and
Mathlib's fundamental theorem of calculus for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) applies.  The sign restriction on `w`
and `d` in the Lipschitz estimate `Work.Drive.wtPar_lipschitz` is removed by the observation
that `wideSfrac` is affine along the line `w + d = period`, so that the `2`-Lipschitz estimate
at the two endpoints `(w, d) = (0, period)` and `(period, 0)` transfers to the whole line.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open MeasureTheory
open scoped Real Topology intervalIntegral

/-! ## The matching phase is differentiable off its corners -/

/-- Near a point `t` at which the sawtooth `sweepParam` does not vanish, `sweepParam` agrees with
the affine function `y ↦ (y - t) / period + sweepParam t`. -/
lemma wsftc_eventually_sweepParam {t : ℝ} (ht : sweepParam t ≠ 0) :
    ∀ᶠ y in 𝓝 t, sweepParam y = (y - t) / period + sweepParam t := by
  set k : ℤ := ⌊t / period⌋ with hk
  have hle : (k : ℝ) ≤ t / period := by
    have h := Int.floor_le (t / period); rwa [← hk] at h
  have hlt : t / period < (k : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (t / period); rwa [← hk] at h
  have hne : t / period ≠ (k : ℝ) := by
    intro h
    refine ht ?_
    rw [sweepParam, ← hk, h]; ring
  have hgt : (k : ℝ) < t / period := lt_of_le_of_ne hle (Ne.symm hne)
  have hpre : (fun y : ℝ => y / period) ⁻¹' Set.Ioo (k : ℝ) ((k : ℝ) + 1) ∈ 𝓝 t :=
    (continuous_id.div_const period).continuousAt.preimage_mem_nhds (Ioo_mem_nhds hgt hlt)
  filter_upwards [hpre] with y hy
  have hfloor : ⌊y / period⌋ = k := by
    rw [Int.floor_eq_iff]; exact ⟨le_of_lt hy.1, hy.2⟩
  have htk : sweepParam t = t / period - (k : ℝ) := by rw [sweepParam, ← hk]
  rw [htk, sweepParam, hfloor]; ring

/-- **The derivative of `wideSfrac` off its corners.**  Away from the three junction points of
the piecewise-affine profile the derivative is `wideRho` times the period. -/
lemma wsftc_hasDerivAt_wideSfrac {ta w d lam u : ℝ} (hden : (1 : ℝ) / 2 - lam ≠ 0)
    (hc : u ≠ 1 / 2) (hc2 : u ≠ 1 / 2 + lam / 2) (hc3 : u ≠ 1 - lam / 2) :
    HasDerivAt (wideSfrac ta w d lam) (wideRho w d lam u * period) u := by
  have hp : period ≠ 0 := period_ne_zero
  rcases lt_trichotomy u (1 / 2) with h | h | h
  · have hev : (wideSfrac ta w d lam) =ᶠ[𝓝 u]
        (fun v => ta + (lam + (1 - 2 * lam) * (2 * v)) * w) := by
      filter_upwards [Iio_mem_nhds h] with v hv
      exact wideSfrac_arc hv.le
    have hder : HasDerivAt (fun v : ℝ => ta + (lam + (1 - 2 * lam) * (2 * v)) * w)
        ((1 - 2 * lam) * (2 * w)) u := by
      have h1 : HasDerivAt (fun v : ℝ => 2 * v) 2 u := by
        simpa using (hasDerivAt_id u).const_mul 2
      have h2 : HasDerivAt (fun v : ℝ => (1 - 2 * lam) * (2 * v)) ((1 - 2 * lam) * 2) u :=
        h1.const_mul (1 - 2 * lam)
      have h3 : HasDerivAt (fun v : ℝ => lam + (1 - 2 * lam) * (2 * v)) ((1 - 2 * lam) * 2) u :=
        h2.const_add lam
      have h4 : HasDerivAt (fun v : ℝ => (lam + (1 - 2 * lam) * (2 * v)) * w)
          (((1 - 2 * lam) * 2) * w) u := h3.mul_const w
      have h5 : HasDerivAt (fun v : ℝ => ta + (lam + (1 - 2 * lam) * (2 * v)) * w)
          (((1 - 2 * lam) * 2) * w) u := h4.const_add ta
      exact h5.congr_deriv (by ring)
    refine (hder.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [wideRho_arc (le_of_lt h)]
    field_simp
  · exact absurd h hc
  · rcases lt_trichotomy u (1 / 2 + lam / 2) with h2 | h2 | h2
    · have hev : (wideSfrac ta w d lam) =ᶠ[𝓝 u]
          (fun v => ta + (1 - lam) * w + (2 * v - 1) * period) := by
        filter_upwards [Ioi_mem_nhds h, Iio_mem_nhds h2] with v hv hv2
        exact wideSfrac_chamfer₁ (not_le.mpr hv) hv2.le
      have hder : HasDerivAt (fun v : ℝ => ta + (1 - lam) * w + (2 * v - 1) * period)
          (2 * period) u := by
        have h1 : HasDerivAt (fun v : ℝ => 2 * v - 1) 2 u := by
          simpa using ((hasDerivAt_id u).const_mul 2).sub_const 1
        have h2' : HasDerivAt (fun v : ℝ => (2 * v - 1) * period) (2 * period) u :=
          h1.mul_const period
        exact (h2'.const_add (ta + (1 - lam) * w)).congr_deriv (by ring)
      refine (hder.congr_of_eventuallyEq hev).congr_deriv ?_
      rw [wideRho_chamfer₁ (not_le.mpr h) h2.le]
    · exact absurd h2 hc2
    · rcases lt_trichotomy u (1 - lam / 2) with h3 | h3 | h3
      · have hev : (wideSfrac ta w d lam) =ᶠ[𝓝 u]
            (fun v => ta + w + lam * d + 2 * d * (v - (1 / 2 + lam / 2))) := by
          filter_upwards [Ioi_mem_nhds h, Ioi_mem_nhds h2, Iio_mem_nhds h3] with v hv hv2 hv3
          exact (wideSfrac_chord (not_le.mpr hv) (not_le.mpr hv2) hv3.le).trans
            (wideSfrac_chord_affine ta w d lam v hden)
        have hder : HasDerivAt (fun v : ℝ => ta + w + lam * d + 2 * d * (v - (1 / 2 + lam / 2)))
            (2 * d) u := by
          have h1 : HasDerivAt (fun v : ℝ => v - (1 / 2 + lam / 2)) 1 u := by
            simpa using (hasDerivAt_id u).sub_const (1 / 2 + lam / 2)
          have h2' : HasDerivAt (fun v : ℝ => 2 * d * (v - (1 / 2 + lam / 2))) (2 * d) u := by
            simpa using h1.const_mul (2 * d)
          exact h2'.const_add (ta + w + lam * d)
        refine (hder.congr_of_eventuallyEq hev).congr_deriv ?_
        have hq : period * (1 / 2 - lam) ≠ 0 := mul_ne_zero hp hden
        rw [wideRho_chord (not_le.mpr h) (not_le.mpr h2) h3.le, div_mul_eq_mul_div,
          eq_div_iff hq]
        ring
      · exact absurd h3 hc3
      · have hev : (wideSfrac ta w d lam) =ᶠ[𝓝 u]
            (fun v => ta + w + (1 - lam) * d + (2 * v - 2 + lam) * period) := by
          filter_upwards [Ioi_mem_nhds h, Ioi_mem_nhds h2, Ioi_mem_nhds h3] with v hv hv2 hv3
          exact wideSfrac_chamfer₂ (not_le.mpr hv) (not_le.mpr hv2) (not_le.mpr hv3)
        have hder : HasDerivAt (fun v : ℝ => ta + w + (1 - lam) * d + (2 * v - 2 + lam) * period)
            (2 * period) u := by
          have h1 : HasDerivAt (fun v : ℝ => 2 * v - 2 + lam) 2 u := by
            have h1a : HasDerivAt (fun v : ℝ => 2 * v) 2 u := by
              simpa using (hasDerivAt_id u).const_mul 2
            simpa using (h1a.sub_const 2).const_add lam
          have h2' : HasDerivAt (fun v : ℝ => (2 * v - 2 + lam) * period) (2 * period) u :=
            h1.mul_const period
          exact (h2'.const_add (ta + w + (1 - lam) * d)).congr_deriv (by ring)
        refine (hder.congr_of_eventuallyEq hev).congr_deriv ?_
        rw [wideRho_chamfer₂ (not_le.mpr h) (not_le.mpr h2) (not_le.mpr h3)]

/-- **The derivative of the matching phase off the corner set of `sweepParam`.** -/
lemma wsftc_hasDerivAt_wideSigma (ta w d lam : ℝ) (hden : (1 : ℝ) / 2 - lam ≠ 0)
    {τ : ℝ} (hc0 : sweepParam τ ≠ 0) (hc1 : sweepParam τ ≠ 1 / 2)
    (hc2 : sweepParam τ ≠ 1 / 2 + lam / 2) (hc3 : sweepParam τ ≠ 1 - lam / 2) :
    HasDerivAt (wideSigma ta w d lam) (wideRho w d lam (sweepParam τ)) τ := by
  have hp : period ≠ 0 := period_ne_zero
  set u : ℝ := sweepParam τ with hu
  have hc1' : u ≠ 1 / 2 := by simpa [hu] using hc1
  have hc2' : u ≠ 1 / 2 + lam / 2 := by simpa [hu] using hc2
  have hc3' : u ≠ 1 - lam / 2 := by simpa [hu] using hc3
  have hev : ∀ᶠ y in 𝓝 τ, wideSigma ta w d lam y
      = τ - u * period + wideSfrac ta w d lam ((y - τ) / period + u) := by
    filter_upwards [wsftc_eventually_sweepParam hc0] with y hy
    have hy' : sweepParam y = (y - τ) / period + u := by
      rw [hy, hu]
    simp only [wideSigma]
    rw [hy']
    field_simp
    ring
  have hinner : HasDerivAt (fun y : ℝ => (y - τ) / period + u) (1 / period) τ := by
    have h1 : HasDerivAt (fun y : ℝ => y - τ) 1 τ := by
      simpa using (hasDerivAt_id τ).sub_const τ
    have h2 : HasDerivAt (fun y : ℝ => (y - τ) / period) (1 / period) τ := by
      simpa using h1.div_const period
    simpa using h2.add_const u
  have houter : HasDerivAt (fun v : ℝ => τ - u * period + wideSfrac ta w d lam v)
      (wideRho w d lam u * period) u :=
    (wsftc_hasDerivAt_wideSfrac (ta := ta) (w := w) (d := d) (lam := lam) hden hc1' hc2'
      hc3').const_add (τ - u * period)
  have houter' : HasDerivAt (fun v : ℝ => τ - u * period + wideSfrac ta w d lam v)
      (wideRho w d lam u * period) ((fun y : ℝ => (y - τ) / period + u) τ) := by
    rw [show (fun y : ℝ => (y - τ) / period + u) τ = u from by simp]
    exact houter
  have hcomp : HasDerivAt ((fun v : ℝ => τ - u * period + wideSfrac ta w d lam v)
      ∘ fun y : ℝ => (y - τ) / period + u) ((wideRho w d lam u * period) * (1 / period)) τ :=
    houter'.comp τ hinner
  have hval : wideRho w d lam (sweepParam τ) = wideRho w d lam u := by simp only [hu]
  refine (hcomp.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hval]
  field_simp

/-! ## The corner set of `sweepParam` is countable, hence null -/

/-- Each level set of the sawtooth `sweepParam` is countable: it consists of one point per
period. -/
lemma wsftc_countable_sweepParam_eq (c : ℝ) : {x : ℝ | sweepParam x = c}.Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_iUnion fun n : ℤ => Set.countable_singleton (((n : ℝ) + c) * period))
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  refine Set.mem_iUnion.mpr ⟨⌊x / period⌋, ?_⟩
  simp only [Set.mem_singleton_iff]
  have h : x / period = (⌊x / period⌋ : ℤ) + c := by
    rw [sweepParam] at hx
    linarith
  have h' := (div_eq_iff period_ne_zero).mp h
  simpa using h'

/-- The matching phase is differentiable at almost every point, with derivative `wideRho`. -/
lemma wsftc_ae_hasDerivAt (ta w d lam : ℝ) (hden : (1 : ℝ) / 2 - lam ≠ 0) :
    ∀ᵐ x ∂volume,
      HasDerivAt (wideSigma ta w d lam) (wideRho w d lam (sweepParam x)) x := by
  have h0 : ∀ᵐ x ∂volume, sweepParam x ≠ 0 := by
    have h := (wsftc_countable_sweepParam_eq 0).measure_zero volume
    rw [measure_eq_zero_iff_ae_notMem] at h
    exact h
  have h1 : ∀ᵐ x ∂volume, sweepParam x ≠ 1 / 2 := by
    have h := (wsftc_countable_sweepParam_eq (1 / 2)).measure_zero volume
    rw [measure_eq_zero_iff_ae_notMem] at h
    exact h
  have h2 : ∀ᵐ x ∂volume, sweepParam x ≠ 1 / 2 + lam / 2 := by
    have h := (wsftc_countable_sweepParam_eq (1 / 2 + lam / 2)).measure_zero volume
    rw [measure_eq_zero_iff_ae_notMem] at h
    exact h
  have h3 : ∀ᵐ x ∂volume, sweepParam x ≠ 1 - lam / 2 := by
    have h := (wsftc_countable_sweepParam_eq (1 - lam / 2)).measure_zero volume
    rw [measure_eq_zero_iff_ae_notMem] at h
    exact h
  filter_upwards [h0, h1, h2, h3] with x hx0 hx1 hx2 hx3
  exact wsftc_hasDerivAt_wideSigma ta w d lam hden hx0 hx1 hx2 hx3

/-! ## Absolute continuity of the matching phase -/

/-- The `2`-Lipschitz estimate of `Work.Drive.wtPar_lipschitz`, as a `LipschitzOnWith` statement
on an arbitrary interval. -/
lemma wsftc_lipschitzOn (ta w d lam a b : ℝ) (hwd : w + d = period) (hw0 : 0 ≤ w)
    (hd0 : 0 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    LipschitzOnWith 2 (wideSigma ta w d lam) (Set.uIcc a b) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x _ y _
  have h := wtPar_lipschitz ta w d lam hwd hw0 hd0 hlam0 hlam1 y x
  simp only [wtPar] at h
  simpa [Real.dist_eq] using h

lemma wsftc_ac_of_nonneg (ta w d lam a b : ℝ) (hwd : w + d = period) (hw0 : 0 ≤ w)
    (hd0 : 0 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    AbsolutelyContinuousOnInterval (wideSigma ta w d lam) a b :=
  (wsftc_lipschitzOn ta w d lam a b hwd hw0 hd0 hlam0 hlam1).absolutelyContinuousOnInterval

/-! ## Affinity along the line `w + d = period` -/

/-- **`wideSfrac` is affine along the line `w + d = period`**: it interpolates between its
values at the two endpoints `(w, d) = (0, period)` and `(period, 0)`. -/
lemma wsftc_wideSfrac_interp {ta w d lam u : ℝ} (hwd : w + d = period)
    (hden : (1 : ℝ) / 2 - lam ≠ 0) :
    period * wideSfrac ta w d lam u
      = d * wideSfrac ta 0 period lam u + w * wideSfrac ta period 0 lam u := by
  have hd : d = period - w := by linarith
  rw [hd]
  by_cases hu : u ≤ 1 / 2
  · rw [wideSfrac_arc hu, wideSfrac_arc hu, wideSfrac_arc hu]
    ring
  · by_cases hu2 : u ≤ 1 / 2 + lam / 2
    · rw [wideSfrac_chamfer₁ hu hu2, wideSfrac_chamfer₁ hu hu2, wideSfrac_chamfer₁ hu hu2]
      ring
    · by_cases hu3 : u ≤ 1 - lam / 2
      · rw [wideSfrac_chord hu hu2 hu3, wideSfrac_chord hu hu2 hu3, wideSfrac_chord hu hu2 hu3,
          wideSfrac_chord_affine ta w (period - w) lam u hden,
          wideSfrac_chord_affine ta 0 period lam u hden,
          wideSfrac_chord_affine ta period 0 lam u hden]
        ring
      · rw [wideSfrac_chamfer₂ hu hu2 hu3, wideSfrac_chamfer₂ hu hu2 hu3,
          wideSfrac_chamfer₂ hu hu2 hu3]
        ring

/-- **`wideSigma` is affine along the line `w + d = period`**. -/
lemma wsftc_wideSigma_interp {ta w d lam τ : ℝ} (hwd : w + d = period)
    (hden : (1 : ℝ) / 2 - lam ≠ 0) :
    period * wideSigma ta w d lam τ
      = d * wideSigma ta 0 period lam τ + w * wideSigma ta period 0 lam τ := by
  have hd : d = period - w := by linarith
  rw [hd]
  have h := wsftc_wideSfrac_interp (ta := ta) (w := w) (d := period - w) (lam := lam)
    (u := sweepParam τ) (by linarith) hden
  simp only [wideSigma]
  linear_combination h

/-- **The matching phase is absolutely continuous on every interval.** -/
lemma wsftc_ac (ta w d lam a b : ℝ) (hwd : w + d = period) (hlam0 : 0 < lam)
    (hlam1 : lam < 1 / 2) : AbsolutelyContinuousOnInterval (wideSigma ta w d lam) a b := by
  have hp : period ≠ 0 := period_ne_zero
  have hden : (1 : ℝ) / 2 - lam ≠ 0 := by linarith
  have h0 : AbsolutelyContinuousOnInterval (fun τ : ℝ => wideSigma ta 0 period lam τ) a b :=
    wsftc_ac_of_nonneg ta 0 period lam a b (by ring) le_rfl period_pos.le hlam0 hlam1
  have h1 : AbsolutelyContinuousOnInterval (fun τ : ℝ => wideSigma ta period 0 lam τ) a b :=
    wsftc_ac_of_nonneg ta period 0 lam a b (by ring) period_pos.le le_rfl hlam0 hlam1
  have hcomb : AbsolutelyContinuousOnInterval
      (fun τ : ℝ => period⁻¹ * (d * wideSigma ta 0 period lam τ
        + w * wideSigma ta period 0 lam τ)) a b :=
    AbsolutelyContinuousOnInterval.const_mul period⁻¹
      (AbsolutelyContinuousOnInterval.add
        (AbsolutelyContinuousOnInterval.const_mul d h0)
        (AbsolutelyContinuousOnInterval.const_mul w h1))
  have hfun : wideSigma ta w d lam
      = fun τ : ℝ => period⁻¹ * (d * wideSigma ta 0 period lam τ
          + w * wideSigma ta period 0 lam τ) := by
    funext τ
    have h := wsftc_wideSigma_interp (ta := ta) (w := w) (d := d) (lam := lam) (τ := τ) hwd hden
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
  rw [← hfun] at hcomb
  exact hcomb

/-! ## The fundamental theorem of calculus -/

theorem wideSigma_ftc {ta w d lam a b : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hwd : w + d = period) :
    ∫ t in a..b, wideRho w d lam (sweepParam t) = wideSigma ta w d lam b - wideSigma ta w d lam a := by
  have hden : (1 : ℝ) / 2 - lam ≠ 0 := by linarith
  have hac := wsftc_ac ta w d lam a b hwd hlam0 hlam1
  have hae := wsftc_ae_hasDerivAt ta w d lam hden
  have hcongr : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
      wideRho w d lam (sweepParam x) = deriv (wideSigma ta w d lam) x := by
    filter_upwards [hae] with x hx _
    exact hx.deriv.symm
  rw [intervalIntegral.integral_congr_ae hcongr, hac.integral_deriv_eq_sub]

end Work.Drive
