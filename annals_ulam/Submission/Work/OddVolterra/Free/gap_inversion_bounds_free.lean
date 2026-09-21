import Mathlib
import Submission.Work.OddRadon.Abel
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddRadon.Core
import Submission.Work.OddCurve.LowSlope.gapKernel_derivs
import Submission.Work.OddCurve.LowSlope.QuantDefs
import Submission.Work.OddRadon.radonProfile_radonInverse
import Submission.Work.OddRadon.abelReduceIter_abelTrans
import Submission.Work.OddRadon.AbelInversion
import Submission.Work.OddRadon.hasDerivAt_abelTrans
import Submission.Work.OddRadon.abelTrans_hasDerivAt_direct
import Submission.Work.OddRadon.sphereArea_pos
import Submission.Work.OddCurve.LowSlope.abelTrans_slope_tendsto
import Submission.Work.OddCurve.LowSlope.abelTrans_diffQuot_integral_tendsto
import Submission.Work.OddCurve.LowSlope.abs_rpow_sub_div_le

/-!
# Bounds for the inversion of the gap-supported Radon datum (free tips)

`Work.OddVolterra.Free.gap_inversion_bounds_free`: if an even profile `γ` is smooth on `(0,1)`
and bounded by `M` on `(0,a₀)`, and the datum `δ` — smooth on `(0,1)` — is supported in the
"gap" `[tStar, a₀]` and equals `radonProfile (2n+1) γ` there, then the inverse Radon transform
`radonInverse n δ` and its first two derivatives are bounded by `C * M` on `[4/5, 1]`, with `C`
absolute.

The mechanism.  With `Ψ c = (2 |S^{2n-2}|)⁻¹ c^{2n-2} δ c` the reduction identity
`radonProfile_eq_abelTrans'` gives `Ψ = T_{n-3/2} γ` on `(0,a₀)`, and the exponent-lowering
recursion `T_β' = 2βc T_{β-1}` (in the robust form
`abelTrans_hasDerivAt_local` below, which needs only continuity and local
boundedness of `γ`) turns the `(n-1)`-fold reduction of `Ψ` into `Φ = T_{-1/2} γ` on `(0,a₀)`,
where `|Φ| ≤ 2M`.  Since `Ψ` vanishes off `(tStar, a₀)`, so does `Φ`; and
`radonInverse n δ` is by definition `(2/π)` times the derivative of the classical Abel integral
of `Φ`.  On `[4/5,1] ∋ u` the integration range of that Abel integral is confined to
`[tStar, a₀]`, where `u² - c² ≥ (4/5)² - cStar² = 31/1025`, so the singular kernels are bounded
and `Work.OddCurve.LowSlope.gapKernel_derivs` gives the three derivatives as explicit
integrals, bounded by `C * M`.

This is the *corrected* form of `Work.OddCurve.LowSlope.gap_inversion_bounds`: the earlier
statement used `Even γ` (Mathlib's *additive* predicate, vacuous for function types) instead of
`Function.Even γ`; see `Submission/Work/OddCurve/LowSlope/NOTES_gap_inversion_bounds_FALSE.md`.
-/

namespace Work.OddVolterra.Free

-- a few steps of the main proof are definitionally heavy (unfolding `radonInverse`/`abelInvert`)
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

/-! ## The two-sided derivative of the Abel transform at an interior point

The following block is the (self-contained) proof of the exponent-lowering recursion
(a teammate's development, at that time in `Work.OddCurve.LowSlope.abelTrans_hasDerivAt_local`;
it is reproduced here so that this module depends on nothing under active development).
`T_β' = 2βc · T_{β-1}` for a profile `γ` that is merely continuous and locally bounded on
`(0,a₀)`: only the kernel is differentiated, never `γ`.  The right-hand difference-quotient limit
is `Work.OddCurve.LowSlope.abelTrans_slope_tendsto`; the mirror image for `h → 0⁻` is proved
below. -/

/-! ## An elementary chord bound for `Real.rpow` -/

/-- **Chord bound.**  For `0 ≤ B ≤ A` and `β > 0`, `A^β - B^β ≤ (max 1 β) (A - B) A^(β-1)`.

For `β ≤ 1` the graph of `t ↦ t^β` lies below the chord from `(0,0)` to `(A,A^β)`; for `β ≥ 1` it
lies below its tangent at the right endpoint. -/
theorem rpow_sub_le_max_mul {β A B : ℝ} (hβ : 0 < β) (hB : 0 ≤ B) (hBA : B ≤ A)
    (hA : 0 < A) :
    A ^ β - B ^ β ≤ max 1 β * (A - B) * A ^ (β - 1) := by
  have hAβpos : 0 < A ^ β := Real.rpow_pos_of_pos hA β
  have hr0 : 0 ≤ B / A := div_nonneg hB hA.le
  have hr1 : B / A ≤ 1 := (div_le_one hA).mpr hBA
  have hdiv : (B / A) ^ β = B ^ β / A ^ β := Real.div_rpow hB hA.le β
  have hBAβ : A ^ β * (B / A) = B * A ^ (β - 1) := by
    rw [Real.rpow_sub_one hA.ne' β]; field_simp
  have hAβ : A ^ β = A * A ^ (β - 1) := by
    conv_lhs => rw [show β = 1 + (β - 1) by ring]
    rw [Real.rpow_add hA, Real.rpow_one]
  rcases le_total β 1 with hβ1 | hβ1
  · rw [max_eq_left hβ1, one_mul]
    have hkey : B / A ≤ B ^ β / A ^ β := by
      rw [← hdiv]; exact Real.self_le_rpow_of_le_one hr0 hr1 hβ1
    have h2 : B * A ^ (β - 1) ≤ B ^ β := by
      have h3 := mul_le_mul_of_nonneg_left hkey hAβpos.le
      rwa [hBAβ, mul_div_cancel₀ _ hAβpos.ne'] at h3
    calc A ^ β - B ^ β ≤ A ^ β - B * A ^ (β - 1) := by linarith
      _ = (A - B) * A ^ (β - 1) := by rw [hAβ]; ring
  · rw [max_eq_right hβ1]
    have hkey : 1 + β * (B / A - 1) ≤ (B / A) ^ β := by
      have h := one_add_mul_self_le_rpow_one_add (s := B / A - 1) (by linarith) hβ1
      rwa [show 1 + (B / A - 1) = B / A by ring] at h
    rw [hdiv] at hkey
    have h2 : A ^ β * (1 + β * (B / A - 1)) ≤ B ^ β := by
      have h3 := mul_le_mul_of_nonneg_left hkey hAβpos.le
      rwa [mul_div_cancel₀ _ hAβpos.ne'] at h3
    have hexp : A ^ β * (1 + β * (B / A - 1)) = A ^ β - β * (A - B) * A ^ (β - 1) := by
      calc A ^ β * (1 + β * (B / A - 1))
          = A ^ β + β * (A ^ β * (B / A)) - β * A ^ β := by ring
        _ = A ^ β + β * (B * A ^ (β - 1)) - β * (A * A ^ (β - 1)) := by rw [hBAβ, hAβ]
        _ = A ^ β - β * (A - B) * A ^ (β - 1) := by ring
    linarith [h2, hexp]

/-! ## Small helpers for measurability, integrability and locality -/

/-- A function continuous on `(a,b)` is a.e. strongly measurable for the restriction of Lebesgue
measure to `(a,b]` (the two intervals differ by the null set `{b}`). -/
private lemma aestronglyMeasurable_of_continuousOn_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Ioo a b)) :
    AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)) := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b))]
  exact hf.aestronglyMeasurable measurableSet_Ioo

/-- A function continuous on `(a,b)` and bounded there by `C` is interval integrable on `(a,b)`. -/
private lemma intervalIntegrable_of_continuousOn_Ioo_of_bound {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Ioo a b)) (hb : ∀ s ∈ Set.Ioo a b, |f s| ≤ C) :
    IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun' ?_ ?_
  · rw [Set.uIoc_of_le hab.le, ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b))]
    exact hf.aestronglyMeasurable measurableSet_Ioo
  · rw [Set.uIoc_of_le hab.le, Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b)).symm]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs]
    exact hb s hs

/-- `abelTrans` only sees `γ` on `(0,c)`. -/
private lemma abelTrans_congr_of_eqOn {α : ℝ} {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Set.EqOn f g (Set.Ioo 0 c)) :
    Work.OddRadon.abelTrans α f c = Work.OddRadon.abelTrans α g c := by
  unfold Work.OddRadon.abelTrans
  apply intervalIntegral.integral_congr_ae
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [MeasureTheory.ae_iff]; simp [measure_singleton]
  filter_upwards [hcompl] with x hxc hx
  rw [Set.uIoc_of_le hc.le] at hx
  rw [h ⟨hx.1, lt_of_le_of_ne hx.2 hxc⟩]

/-! ## The left-hand difference quotient -/

/-- The pointwise difference-quotient limit from the left:
`(((c+h)²-s²)^β - (c²-s²)^β)/h → β (c²-s²)^(β-1) (2c)` as `h → 0⁻` for `0 ≤ s < c`. -/
private lemma tendsto_diffQuot_rpow_sq_left {β c s : ℝ} (hs : s < c) (hs0 : 0 ≤ s) :
    Filter.Tendsto (fun h : ℝ => (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h)
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (β * (c ^ 2 - s ^ 2) ^ (β - 1) * (2 * c))) := by
  have hpos : 0 < c ^ 2 - s ^ 2 := by nlinarith
  have hderiv : HasDerivAt (fun x : ℝ => (x ^ 2 - s ^ 2) ^ β)
      (β * (c ^ 2 - s ^ 2) ^ (β - 1) * (2 * c)) c := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 - s ^ 2) (2 * c) c := by
      have h := ((hasDerivAt_id c).pow 2).sub_const (s ^ 2)
      simpa using h
    have h2 : HasDerivAt (fun u : ℝ => u ^ β) (β * (c ^ 2 - s ^ 2) ^ (β - 1)) (c ^ 2 - s ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hpos))
    exact h2.comp c h1
  have hsub : Set.Iio (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_lt hx
  have key := hderiv.tendsto_slope_zero.mono_left (nhdsWithin_mono (0 : ℝ) hsub)
  simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using key

/-- **Domination of the left difference-quotient kernel.**  For `h < 0`, `c + h > 0` and
`0 < s < min c (c+h)`,

`|(((c+h)²-s²)^β - (c²-s²)^β)/h| ≤ (max 1 β)(2c) (c²-s²)^(β-1)`. -/
private lemma abs_left_diffQuot_le {β c h s : ℝ} (hβ : 0 < β) (hc : 0 < c) (hh : h < 0)
    (hhc : -c < h) (hsc : s < c + h) (hs0 : 0 < s) (hsc' : s < c) :
    |(((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h|
      ≤ max 1 β * (2 * c) * (c ^ 2 - s ^ 2) ^ (β - 1) := by
  have hk : 0 < -h := by linarith
  have hA : 0 < c ^ 2 - s ^ 2 := by
    have h1 : 0 < c - s := by linarith
    have h2 : 0 < c + s := by linarith
    nlinarith [mul_pos h1 h2]
  have hB : 0 ≤ (c + h) ^ 2 - s ^ 2 := by
    have h1 : 0 < c + h - s := by linarith
    have h2 : 0 < c + h + s := by linarith
    nlinarith [mul_pos h1 h2]
  have hBA : (c + h) ^ 2 - s ^ 2 ≤ c ^ 2 - s ^ 2 := by nlinarith
  have hXnp : ((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β ≤ 0 := by
    have h := Real.rpow_le_rpow hB hBA hβ.le
    linarith
  have hAB : c ^ 2 - s ^ 2 - ((c + h) ^ 2 - s ^ 2) = (-h) * (2 * c + h) := by ring
  have hchord := rpow_sub_le_max_mul hβ hB hBA hA
  have hmaxpos : 0 < max 1 β := lt_of_lt_of_le one_pos (le_max_left 1 β)
  have hstep : ((c ^ 2 - s ^ 2) ^ β - ((c + h) ^ 2 - s ^ 2) ^ β) / (-h)
      ≤ max 1 β * (2 * c) * (c ^ 2 - s ^ 2) ^ (β - 1) := by
    rw [div_le_iff₀ hk]
    calc (c ^ 2 - s ^ 2) ^ β - ((c + h) ^ 2 - s ^ 2) ^ β
        ≤ max 1 β * (c ^ 2 - s ^ 2 - ((c + h) ^ 2 - s ^ 2)) * (c ^ 2 - s ^ 2) ^ (β - 1) := hchord
      _ = max 1 β * ((-h) * (2 * c + h)) * (c ^ 2 - s ^ 2) ^ (β - 1) := by rw [hAB]
      _ ≤ max 1 β * ((-h) * (2 * c)) * (c ^ 2 - s ^ 2) ^ (β - 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hk.le) hmaxpos.le
          · exact Real.rpow_nonneg hA.le _
      _ = max 1 β * (2 * c) * (c ^ 2 - s ^ 2) ^ (β - 1) * (-h) := by ring
  have habs : |(((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h|
      = ((c ^ 2 - s ^ 2) ^ β - ((c + h) ^ 2 - s ^ 2) ^ β) / (-h) := by
    rw [abs_of_nonneg (div_nonneg_of_nonpos hXnp hh.le),
      div_eq_div_iff (ne_of_lt hh) (by linarith : -h ≠ 0)]
    ring
  rw [habs]
  exact hstep

/-- **Dominated-convergence step for the left-hand difference quotient.**  The family

`h ↦ s ↦ 1_{s<c+h} γ s (((c+h)²-s²)^β - (c²-s²)^β)/h`

converges, as `h → 0⁻` and integrated over the fixed interval `(0,c)`, to `2βc · T_{β-1} γ c`. -/
private lemma abelTrans_left_diffQuot_tendsto {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Set.Ioo 0 c)) (hγb : ∀ s ∈ Set.Ioo 0 c, |γ s| ≤ M) :
    Filter.Tendsto
      (fun h : ℝ => ∫ s in (0 : ℝ)..c, (Set.Iio (c + h)).indicator
        (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s / h)
      (nhdsWithin (0 : ℝ) (Set.Iio 0))
      (nhds (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c)) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (γ (c / 2))) (hγb (c / 2) ⟨by linarith, by linarith⟩)
  have hBint : IntervalIntegrable
      (fun s : ℝ => M * (max 1 β * (2 * c) * (c ^ 2 - s ^ 2) ^ (β - 1))) volume (0 : ℝ) c := by
    have h1 : IntervalIntegrable (fun s : ℝ => (c ^ 2 - s ^ 2) ^ (β - 1)) volume (0 : ℝ) c :=
      Work.OddCurve.LowSlope.intervalIntegrable_sq_sub_sq_rpow hc (by linarith)
    have h2 : IntervalIntegrable
        (fun s : ℝ => M * ((max 1 β * (2 * c)) * (c ^ 2 - s ^ 2) ^ (β - 1))) volume (0 : ℝ) c :=
      (h1.const_mul (max 1 β * (2 * c))).const_mul M
    refine h2.congr fun s _ => by ring
  have hlim : (∫ s in (0 : ℝ)..c, γ s * (β * (c ^ 2 - s ^ 2) ^ (β - 1) * (2 * c)))
      = 2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c := by
    rw [Work.OddRadon.abelTrans, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hae : ∀ᵐ s ∂volume, s ∉ ({c} : Set ℝ) := compl_mem_ae_iff.mpr (measure_singleton c)
  have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Iio 0), h ∈ Set.Ioo (-c) (0 : ℝ) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (-c : ℝ) < 0 by linarith)] with h hgt hlt
    exact ⟨hgt, hlt⟩
  have hDCT : Filter.Tendsto
      (fun h : ℝ => ∫ s in (0 : ℝ)..c, (Set.Iio (c + h)).indicator
        (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s / h)
      (nhdsWithin (0 : ℝ) (Set.Iio 0))
      (nhds (∫ s in (0 : ℝ)..c, γ s * (β * (c ^ 2 - s ^ 2) ^ (β - 1) * (2 * c)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := (0 : ℝ)) (b := c) (l := nhdsWithin (0 : ℝ) (Set.Iio 0))
      (F := fun h s => (Set.Iio (c + h)).indicator
        (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s / h)
      (f := fun s => γ s * (β * (c ^ 2 - s ^ 2) ^ (β - 1) * (2 * c)))
      (fun s => M * (max 1 β * (2 * c) * (c ^ 2 - s ^ 2) ^ (β - 1))) ?_ ?_ hBint ?_
    · filter_upwards with h
      have hγmeas : AEStronglyMeasurable γ (volume.restrict (Set.uIoc (0 : ℝ) c)) := by
        rw [Set.uIoc_of_le hc.le]
        exact aestronglyMeasurable_of_continuousOn_Ioo hγc
      have hker : AEStronglyMeasurable
          (fun s : ℝ => ((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β)
          (volume.restrict (Set.uIoc (0 : ℝ) c)) :=
        Measurable.aestronglyMeasurable (by fun_prop)
      have hprod : AEStronglyMeasurable
          (fun s : ℝ => (Set.Iio (c + h)).indicator
            (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s)
          (volume.restrict (Set.uIoc (0 : ℝ) c)) :=
        (hγmeas.mul hker).indicator measurableSet_Iio
      refine (hprod.const_mul h⁻¹).congr (Eventually.of_forall (fun s => ?_))
      show h⁻¹ * ((Set.Iio (c + h)).indicator
            (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s)
        = ((Set.Iio (c + h)).indicator
            (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s) / h
      rw [div_eq_mul_inv, mul_comm]
    · filter_upwards [hev] with h hh
      filter_upwards [hae] with s hsne hsmem
      rw [Set.uIoc_of_le hc.le, Set.mem_Ioc] at hsmem
      obtain ⟨hhgt, hhlt⟩ := hh
      have hsc : s ≠ c := fun hcontra => hsne (by simp [hcontra])
      have hs : s ∈ Set.Ioo 0 c := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hsc⟩
      have hγ : |γ s| ≤ M := hγb s hs
      have hmaxnn : 0 ≤ max 1 β := le_trans zero_le_one (le_max_left 1 β)
      rw [Real.norm_eq_abs]
      by_cases hsch : s < c + h
      · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hsch)]
        have hker := abs_left_diffQuot_le hβ hc hhlt hhgt hsch hs.1 hs.2
        have hfac : |γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h|
            = |γ s| * |(((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h| := by
          rw [mul_div_assoc, abs_mul]
        rw [hfac]
        exact mul_le_mul hγ hker (abs_nonneg _) hM0
      · rw [Set.indicator_of_notMem (by simpa using hsch), zero_div, abs_zero]
        exact mul_nonneg hM0 (mul_nonneg (mul_nonneg hmaxnn (by linarith))
          (Real.rpow_nonneg (by nlinarith [hs.1, hs.2, hc]) _))
    · filter_upwards [hae] with s hsne hsmem
      rw [Set.uIoc_of_le hc.le, Set.mem_Ioc] at hsmem
      have hsc : s < c := lt_of_le_of_ne hsmem.2 (fun hcontra => hsne (by simp [hcontra]))
      have hdp := tendsto_diffQuot_rpow_sq_left (β := β) hsc hsmem.1.le
      have hev2 : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Set.Iio 0), s < c + h := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Ioi_mem_nhds (show s - c < 0 by linarith)] with h hh _
        rw [Set.mem_Ioi] at hh
        linarith
      refine Tendsto.congr' ?_ (hdp.const_mul (γ s))
      filter_upwards [hev2] with h hsh
      rw [Set.indicator_of_mem (Set.mem_Iio.mpr hsh)]
      ring_nf
  rw [hlim] at hDCT
  exact hDCT

/-- **The boundary tongue is `o(1)` from the left.**  On `(c+h,c) ⊂ (0,c)` the kernel is bounded
by `(2c(c-s))^β` and `|γ| ≤ M`, so the integral is `≤ M (2c)^β |h|^{β+1}` and its quotient by
`|h|` tends to `0`. -/
private lemma abelTrans_left_tail_tendsto {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) {γ : ℝ → ℝ}
    (hγb : ∀ s ∈ Set.Ioo 0 c, |γ s| ≤ M) :
    Filter.Tendsto (fun h : ℝ => (∫ s in (c + h)..c, γ s * (c ^ 2 - s ^ 2) ^ β) / (-h))
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (γ (c / 2))) (hγb (c / 2) ⟨by linarith, by linarith⟩)
  refine squeeze_zero_norm' (a := fun h : ℝ => M * ((2 * c) ^ β * (-h) ^ β)) ?_ ?_
  · have hev : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Set.Iio 0), h ∈ Set.Ioo (-c) (0 : ℝ) := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioi_mem_nhds (show (-c : ℝ) < 0 by linarith)] with h hgt hlt
      exact ⟨hgt, hlt⟩
    filter_upwards [hev] with h hh
    obtain ⟨hhgt, hhlt⟩ := hh
    have hk : 0 < -h := by linarith
    have hle : c + h ≤ c := by linarith
    have hae : ∀ᵐ s ∂volume, s ∈ Set.uIoc (c + h) c →
        ‖γ s * (c ^ 2 - s ^ 2) ^ β‖ ≤ M * ((2 * c) ^ β * (-h) ^ β) := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with s hsne hsmem
      rw [Set.uIoc_of_le hle, Set.mem_Ioc] at hsmem
      have hs : s ∈ Set.Ioo 0 c :=
        ⟨by linarith [hsmem.1, hhgt, hc],
          lt_of_le_of_ne hsmem.2 (fun hcontra => hsne (by simp [hcontra]))⟩
      have hγ : |γ s| ≤ M := hγb s hs
      have hbase : c ^ 2 - s ^ 2 ≤ (2 * c) * (-h) := by
        have h1 : c - s ≤ -h := by linarith [hsmem.1]
        have h2 : c + s ≤ 2 * c := by linarith [hsmem.2]
        have h3 : 0 ≤ c - s := by linarith [hsmem.2]
        have h4 : 0 ≤ c + s := by linarith [hs.1, hc]
        nlinarith [h1, h2, h3, h4]
      have hnn : 0 ≤ c ^ 2 - s ^ 2 := by nlinarith [hs.1, hs.2, hc]
      have hpow : (c ^ 2 - s ^ 2) ^ β ≤ (2 * c) ^ β * (-h) ^ β := by
        calc (c ^ 2 - s ^ 2) ^ β ≤ ((2 * c) * (-h)) ^ β := Real.rpow_le_rpow hnn hbase hβ.le
          _ = (2 * c) ^ β * (-h) ^ β := Real.mul_rpow (by linarith) hk.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hnn β)]
      calc |γ s| * (c ^ 2 - s ^ 2) ^ β ≤ M * (c ^ 2 - s ^ 2) ^ β :=
            mul_le_mul_of_nonneg_right hγ (Real.rpow_nonneg hnn β)
        _ ≤ M * ((2 * c) ^ β * (-h) ^ β) := mul_le_mul_of_nonneg_left hpow hM0
    have hnorm : ‖(∫ s in (c + h)..c, γ s * (c ^ 2 - s ^ 2) ^ β) / (-h)‖
        = ‖∫ s in (c + h)..c, γ s * (c ^ 2 - s ^ 2) ^ β‖ / (-h) := by
      rw [norm_div]
      congr 1
      rw [Real.norm_eq_abs, abs_of_pos hk]
    have habs2 : |c - (c + h)| = -h := by
      rw [show c - (c + h) = -h by ring, abs_of_pos hk]
    rw [hnorm]
    calc ‖∫ s in (c + h)..c, γ s * (c ^ 2 - s ^ 2) ^ β‖ / (-h)
        ≤ (M * ((2 * c) ^ β * (-h) ^ β) * |c - (c + h)|) / (-h) :=
          div_le_div_of_nonneg_right (intervalIntegral.norm_integral_le_of_norm_le_const_ae hae) hk.le
      _ = M * ((2 * c) ^ β * (-h) ^ β) := by
          rw [habs2, mul_div_assoc]
          rw [div_self (show (-h) ≠ 0 by linarith)]
          ring
  · have h1 : Filter.Tendsto (fun h : ℝ => -h) (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
      have hcont : Continuous (fun h : ℝ => -h) := by fun_prop
      simpa using (hcont.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Iio 0))
    have h2 : Filter.Tendsto (fun h : ℝ => (-h) ^ β) (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
      have h3 := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.comp h1
      rw [Real.zero_rpow hβ.ne'] at h3
      exact h3
    have h3 : Filter.Tendsto (fun h : ℝ => (2 * c) ^ β * (-h) ^ β)
        (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
      have h4 := h2.const_mul ((2 * c) ^ β)
      simpa using h4
    have h4 : Filter.Tendsto (fun h : ℝ => M * ((2 * c) ^ β * (-h) ^ β))
        (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
      have h5 := h3.const_mul M
      simpa using h5
    exact h4

/-- **The left difference-quotient split.**  For `h < 0` with `c + h > 0`,

`(T(c+h) - T c)/h = ∫_0^c 1_{s<c+h} γs(((c+h)²-s²)^β - (c²-s²)^β) ds / h + (∫_{c+h}^c γs(c²-s²)^β)/(-h)`. -/
private lemma abelTrans_left_decomp {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Set.Ioo 0 c)) (hγb : ∀ s ∈ Set.Ioo 0 c, |γ s| ≤ M)
    {h : ℝ} (hh : h < 0) (hhc : -c < h) :
    (Work.OddRadon.abelTrans β γ (c + h) - Work.OddRadon.abelTrans β γ c) / h
      = (∫ s in (0 : ℝ)..c, (Set.Iio (c + h)).indicator
            (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s / h)
        + (∫ s in (c + h)..c, γ s * (c ^ 2 - s ^ 2) ^ β) / (-h) := by
  have hch : 0 < c + h := by linarith
  have hle : c + h ≤ c := by linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (γ (c / 2))) (hγb (c / 2) ⟨by linarith, by linarith⟩)
  have hγ1 : ContinuousOn γ (Set.Ioo 0 (c + h)) :=
    hγc.mono (fun x hx => ⟨hx.1, by linarith [hx.2, hle]⟩)
  have hγ2 : ContinuousOn γ (Set.Ioo (c + h) c) :=
    hγc.mono (fun x hx => ⟨by linarith [hx.1, hch], hx.2⟩)
  have hbsq : ∀ {a : ℝ}, 0 < a → a ≤ c → ∀ s ∈ Set.Ioo 0 a,
      |γ s * (a ^ 2 - s ^ 2) ^ β| ≤ M * (a ^ 2) ^ β := by
    intro a ha hac s hs
    have hγ : |γ s| ≤ M := hγb s ⟨hs.1, by linarith [hs.2, hac]⟩
    have hbase : 0 ≤ a ^ 2 - s ^ 2 := by
      have h1 : 0 < a - s := by linarith [hs.2]
      have h2 : 0 < a + s := by linarith [hs.1, ha]
      nlinarith [mul_pos h1 h2]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hbase β)]
    calc |γ s| * (a ^ 2 - s ^ 2) ^ β ≤ M * (a ^ 2 - s ^ 2) ^ β :=
          mul_le_mul_of_nonneg_right hγ (Real.rpow_nonneg hbase β)
      _ ≤ M * (a ^ 2) ^ β :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase (by nlinarith) hβ.le) hM0
  have hcont1 : ContinuousOn (fun s : ℝ => γ s * ((c + h) ^ 2 - s ^ 2) ^ β) (Set.Ioo 0 (c + h)) :=
    hγ1.mul (ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
      (fun x hx => Or.inl (ne_of_gt (by
        have h1 : 0 < c + h - x := by linarith [hx.2]
        have h2 : 0 < c + h + x := by linarith [hx.1, hch]
        nlinarith [mul_pos h1 h2]))))
  have hcont2 : ContinuousOn (fun s : ℝ => γ s * (c ^ 2 - s ^ 2) ^ β) (Set.Ioo 0 (c + h)) :=
    hγ1.mul (ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
      (fun x hx => Or.inl (ne_of_gt (by
        have h1 : 0 < c - x := by linarith [hx.2, hle]
        have h2 : 0 < c + x := by linarith [hx.1, hc]
        nlinarith [mul_pos h1 h2]))))
  have hcont3 : ContinuousOn (fun s : ℝ => γ s * (c ^ 2 - s ^ 2) ^ β) (Set.Ioo (c + h) c) :=
    hγ2.mul (ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
      (fun x hx => Or.inl (ne_of_gt (by
        have h1 : 0 < c - x := by linarith [hx.2]
        have h2 : 0 < c + x := by linarith [hx.1, hch]
        nlinarith [mul_pos h1 h2]))))
  have hI1 : IntervalIntegrable (fun s : ℝ => γ s * ((c + h) ^ 2 - s ^ 2) ^ β) volume
      (0 : ℝ) (c + h) := intervalIntegrable_of_continuousOn_Ioo_of_bound hch hcont1
        (fun s hs => hbsq hch hle s hs)
  have hI2 : IntervalIntegrable (fun s : ℝ => γ s * (c ^ 2 - s ^ 2) ^ β) volume
      (0 : ℝ) (c + h) := intervalIntegrable_of_continuousOn_Ioo_of_bound hch hcont2
        (fun s hs => hbsq hc le_rfl s ⟨hs.1, by linarith [hs.2, hle]⟩)
  have hI3 : IntervalIntegrable (fun s : ℝ => γ s * (c ^ 2 - s ^ 2) ^ β) volume
      (c + h) c := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_bound (C := M * (c ^ 2) ^ β)
      (by linarith : c + h < c) hcont3 ?_
    intro s hs
    have hγ : |γ s| ≤ M := hγb s ⟨by linarith [hs.1, hch], hs.2⟩
    have hbase : 0 ≤ c ^ 2 - s ^ 2 := by
      have h1 : 0 < c - s := by linarith [hs.2]
      have h2 : 0 < c + s := by linarith [hs.1, hch]
      nlinarith [mul_pos h1 h2]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hbase β)]
    calc |γ s| * (c ^ 2 - s ^ 2) ^ β ≤ M * (c ^ 2 - s ^ 2) ^ β :=
          mul_le_mul_of_nonneg_right hγ (Real.rpow_nonneg hbase β)
      _ ≤ M * (c ^ 2) ^ β :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase (by nlinarith) hβ.le) hM0
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI2 hI3
  have hsub := intervalIntegral.integral_sub hI1 hI2
  have hsub' : (∫ s in (0 : ℝ)..(c + h),
        γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β))
      = (∫ s in (0 : ℝ)..(c + h), γ s * ((c + h) ^ 2 - s ^ 2) ^ β)
        - ∫ s in (0 : ℝ)..(c + h), γ s * (c ^ 2 - s ^ 2) ^ β := by
    rw [← hsub]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  have hind : (∫ s in (0 : ℝ)..c, (Set.Iio (c + h)).indicator
        (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s)
      = ∫ s in (0 : ℝ)..(c + h),
          γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) := by
    rw [intervalIntegral.integral_of_le hc.le, intervalIntegral.integral_of_le hch.le]
    rw [MeasureTheory.integral_indicator measurableSet_Iio]
    rw [Measure.restrict_restrict measurableSet_Iio]
    rw [show Set.Iio (c + h) ∩ Set.Ioc (0 : ℝ) c = Set.Ioo 0 (c + h) by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩]
    rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := c + h))]
  have key : (∫ s in (0 : ℝ)..c, (Set.Iio (c + h)).indicator
        (fun t => γ t * (((c + h) ^ 2 - t ^ 2) ^ β - (c ^ 2 - t ^ 2) ^ β)) s / h)
      = (∫ s in (0 : ℝ)..(c + h),
          γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β)) / h := by
    rw [intervalIntegral.integral_div (r := h), hind]
  simp only [Work.OddRadon.abelTrans]
  rw [key, ← hsplit, hsub', div_neg]
  ring

/-- **The left-hand difference-quotient limit.**  For `γ` continuous and bounded on `(0,c)`,
`(T_βγ(c+h) - T_βγ c)/h → 2βc · T_{β-1}γ c` as `h → 0⁻`. -/
theorem abelTrans_slope_tendsto_left {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Set.Ioo 0 c)) (hγb : ∀ s ∈ Set.Ioo 0 c, |γ s| ≤ M) :
    Filter.Tendsto
      (fun h : ℝ => (Work.OddRadon.abelTrans β γ (c + h) - Work.OddRadon.abelTrans β γ c) / h)
      (nhdsWithin (0 : ℝ) (Set.Iio 0))
      (nhds (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c)) := by
  have hmain := abelTrans_left_diffQuot_tendsto hβ hc hγc hγb
  have htail := abelTrans_left_tail_tendsto hβ hc hγb
  have hsum := hmain.add htail
  rw [add_zero] at hsum
  refine Tendsto.congr' ?_ hsum
  have hev : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Set.Iio 0), h ∈ Set.Ioo (-c) (0 : ℝ) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (-c : ℝ) < 0 by linarith)] with h hgt hlt
    exact ⟨hgt, hlt⟩
  filter_upwards [hev] with h hh
  exact (abelTrans_left_decomp hβ hc hγc hγb hh.2 hh.1).symm

/-! ## The two-sided derivative -/

/-- **The exponent-lowering recursion `T_β' = 2βc T_{β-1}` (two-sided)**, for `γ` continuous and
bounded on `(0,a₀)` and `0 < c < a₀`. -/
theorem abelTrans_hasDerivAt_local {β a₀ c : ℝ} (hβ : 0 < β) (ha₀ : 0 < a₀)
    (hc : 0 < c) (hca : c < a₀) {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Set.Ioo 0 a₀))
    (hb : ∃ M, ∀ s ∈ Set.Ioo 0 a₀, |γ s| ≤ M) :
    HasDerivAt (fun x : ℝ => Work.OddRadon.abelTrans β γ x)
      (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c) c := by
  obtain ⟨M, hM⟩ := hb
  -- the left-hand limit, directly from `γ` on `(0,c)`
  have hleft : Filter.Tendsto
      (fun h : ℝ => (Work.OddRadon.abelTrans β γ (c + h) - Work.OddRadon.abelTrans β γ c) / h)
      (nhdsWithin (0 : ℝ) (Set.Iio 0))
      (nhds (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c)) :=
    abelTrans_slope_tendsto_left hβ hc (hγ.mono (fun x hx => ⟨hx.1, by linarith [hx.2, hca]⟩))
      (fun s hs => hM s ⟨hs.1, by linarith [hs.2, hca]⟩)
  -- the right-hand limit: extend `γ` to `(0,2c)` by `s ↦ γ (min s d)`, `c < d < min a₀ (2c)`
  set d : ℝ := c + min (a₀ - c) c / 2 with hd
  have hminpos : 0 < min (a₀ - c) c := lt_min (by linarith) hc
  have hdc : c < d := by rw [hd]; linarith
  have hda : d < a₀ := by
    rw [hd]; have h1 : min (a₀ - c) c ≤ a₀ - c := min_le_left _ _
    linarith
  have hd2c : d < 2 * c := by
    rw [hd]; have h1 : min (a₀ - c) c ≤ c := min_le_right _ _
    linarith
  set γ' : ℝ → ℝ := fun s => γ (min s d) with hγ'
  have hmaps : Set.MapsTo (fun s : ℝ => min s d) (Set.Ioo 0 (2 * c)) (Set.Ioo 0 a₀) := by
    intro s hs
    exact ⟨lt_min hs.1 (by linarith), lt_of_le_of_lt (min_le_right s d) hda⟩
  have hγ'cont : ContinuousOn γ' (Set.Ioo 0 (2 * c)) := by
    rw [hγ']
    exact hγ.comp (continuous_id.min continuous_const).continuousOn hmaps
  have hγ'bd : ∀ s ∈ Set.Ioo 0 (2 * c), |γ' s| ≤ M := by
    intro s hs
    rw [hγ']
    exact hM _ (hmaps hs)
  have hcongr_c : Work.OddRadon.abelTrans (β - 1) γ' c = Work.OddRadon.abelTrans (β - 1) γ c :=
    abelTrans_congr_of_eqOn hc (fun s hs => by
      have hs' : s ≤ d := le_of_lt (by linarith [hs.2, hdc])
      simp only [hγ', min_eq_left hs'])
  have hright' := Work.OddCurve.LowSlope.abelTrans_slope_tendsto (β := β) (M := M) (c := c) hβ hc hγ'cont hγ'bd
  rw [hcongr_c] at hright'
  have hright : Filter.Tendsto
      (fun h : ℝ => (Work.OddRadon.abelTrans β γ (c + h) - Work.OddRadon.abelTrans β γ c) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c)) := by
    refine Tendsto.congr' ?_ hright'
    have hev : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), h < d - c := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds (show (0:ℝ) < d - c by linarith)] with h hh _
      exact hh
    filter_upwards [self_mem_nhdsWithin, hev] with h hhpos hhd
    have hhpos' : 0 < h := hhpos
    have h1 : Work.OddRadon.abelTrans β γ' (c + h) = Work.OddRadon.abelTrans β γ (c + h) :=
      abelTrans_congr_of_eqOn (by linarith) (fun s hs => by
        have hs' : s ≤ d := le_of_lt (by linarith [hs.2, hhd])
        simp only [hγ', min_eq_left hs'])
    have h2 : Work.OddRadon.abelTrans β γ' c = Work.OddRadon.abelTrans β γ c :=
      abelTrans_congr_of_eqOn hc (fun s hs => by
        have hs' : s ≤ d := le_of_lt (by linarith [hs.2, hdc])
        simp only [hγ', min_eq_left hs'])
    rw [h1, h2]
  -- combine the two one-sided limits and convert to `HasDerivAt`
  have hboth : Filter.Tendsto
      (fun h : ℝ => (Work.OddRadon.abelTrans β γ (c + h) - Work.OddRadon.abelTrans β γ c) / h)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c)) := by
    have hset : Set.Ioi (0 : ℝ) ∪ Set.Iio (0 : ℝ) = ({0} : Set ℝ)ᶜ := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro (h1 | h1) <;> linarith
      · intro hx
        rcases lt_trichotomy x 0 with h1 | h1 | h1
        · exact Or.inr h1
        · exact absurd h1 hx
        · exact Or.inl h1
    rw [← hset, nhdsWithin_union]
    exact hright.sup hleft
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine Tendsto.congr' (Eventually.of_forall (fun h => ?_)) hboth
  simp only [smul_eq_mul]
  rw [inv_mul_eq_div]

lemma abelReduce_abelTrans_local {β a₀ : ℝ} (hβ : 0 < β) (ha₀ : 0 < a₀) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Set.Ioo 0 a₀)) (hb : ∃ M, ∀ s ∈ Set.Ioo 0 a₀, |γ s| ≤ M) :
    Set.EqOn (Work.OddRadon.abelReduce β (Work.OddRadon.abelTrans β γ))
      (Work.OddRadon.abelTrans (β - 1) γ) (Set.Ioo 0 a₀) := by
  intro c hc
  have hderiv := abelTrans_hasDerivAt_local hβ ha₀ hc.1 hc.2 hγc hb
  rw [Work.OddRadon.abelReduce, hderiv.deriv]
  exact mul_div_cancel_left₀ _ (ne_of_gt (by nlinarith [hβ, hc.1]))

lemma abelReduceIter_abelTrans_local {β a₀ : ℝ} {γ : ℝ → ℝ} (ha₀ : 0 < a₀)
    (hγc : ContinuousOn γ (Set.Ioo 0 a₀)) (hb : ∃ M, ∀ s ∈ Set.Ioo 0 a₀, |γ s| ≤ M)
    {k : ℕ} (hk : (k : ℝ) - 1 < β) :
    Set.EqOn (Work.OddRadon.abelReduceIter β k (Work.OddRadon.abelTrans β γ))
      (Work.OddRadon.abelTrans (β - k) γ) (Set.Ioo 0 a₀) := by
  induction k generalizing β with
  | zero => intro c hc; simp
  | succ k ih =>
      intro c hc
      have hk0 : ((k:ℕ):ℝ) < β := by push_cast at hk; linarith
      have hβ : 0 < β := lt_of_le_of_lt (Nat.cast_nonneg k) hk0
      rw [Work.OddRadon.abelReduceIter_succ]
      have hstep : Set.EqOn (Work.OddRadon.abelReduce β (Work.OddRadon.abelTrans β γ))
          (Work.OddRadon.abelTrans (β - 1) γ) (Set.Ioo 0 a₀) :=
        abelReduce_abelTrans_local hβ ha₀ hγc hb
      have hcongr := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo k (β - 1) hstep
      rw [hcongr hc]
      have hk' : ((k:ℕ):ℝ) - 1 < β - 1 := by push_cast at hk ⊢; linarith
      rw [ih hk' hc]
      congr 1
      push_cast
      ring

lemma abelReduce_zero (β : ℝ) : Work.OddRadon.abelReduce β (0 : ℝ → ℝ) = 0 := by
  funext c; simp [Work.OddRadon.abelReduce]

lemma abelReduceIter_zero (β : ℝ) (k : ℕ) :
    Work.OddRadon.abelReduceIter β k (0 : ℝ → ℝ) = 0 := by
  induction k generalizing β with
  | zero => rfl
  | succ k ih => rw [Work.OddRadon.abelReduceIter_succ, abelReduce_zero]; exact ih (β - 1)

lemma abelReduce_contDiffOn {β : ℝ} (hβ : β ≠ 0) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Set.Ioo 0 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddRadon.abelReduce β F) (Set.Ioo 0 1) := by
  have h2β : (2 * β) ≠ 0 := mul_ne_zero (by norm_num) hβ
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv F) (Set.Ioo 0 1) :=
    hF.deriv_of_isOpen isOpen_Ioo (by simp)
  have hlin : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c : ℝ => 2 * β * c) (Set.Ioo 0 1) := by
    fun_prop
  have hne : ∀ c ∈ Set.Ioo (0:ℝ) 1, (2 * β * c) ≠ 0 := fun c hc => mul_ne_zero h2β (ne_of_gt hc.1)
  have hdiv := hd.div hlin hne
  have hfun : (deriv F / fun c : ℝ => 2 * β * c) = Work.OddRadon.abelReduce β F := by
    funext c; simp [Work.OddRadon.abelReduce, Pi.div_apply]
  rwa [hfun] at hdiv

lemma abelReduceIter_contDiffOn {β : ℝ} {k : ℕ} (hk : ∀ j, j < k → β - j ≠ 0) :
    ∀ {F : ℝ → ℝ},
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Set.Ioo 0 1) →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddRadon.abelReduceIter β k F)
        (Set.Ioo 0 1) := by
  induction k generalizing β with
  | zero => intro F hF; simpa using hF
  | succ k ih =>
      intro F hF
      have hk0 : β - (↑(0:ℕ) : ℝ) ≠ 0 := hk 0 (Nat.zero_lt_succ k)
      have hred : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddRadon.abelReduce β F)
          (Set.Ioo 0 1) := abelReduce_contDiffOn (by simpa using hk0) hF
      have hk' : ∀ j, j < k → (β - 1) - j ≠ 0 := by
        intro j hj
        have := hk (j+1) (by omega)
        simpa [sub_sub, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm] using this
      exact ih hk' hred

lemma tStar_eq : Work.OddEnvelope.tStar = (Real.sqrt (1 + (9 / 10 : ℝ) ^ 2))⁻¹ := by
  simp only [Work.OddEnvelope.tStar, Work.OddEnvelope.profileX, Work.OddEnvelope.tau]
  norm_num

lemma tStar_pos : 0 < Work.OddEnvelope.tStar := by
  rw [tStar_eq]; positivity

lemma tStar_lt_one : Work.OddEnvelope.tStar < 1 := by
  rw [tStar_eq]
  apply inv_lt_one_of_one_lt₀
  rw [← Real.sqrt_one]
  apply Real.sqrt_lt_sqrt (by norm_num)
  norm_num

lemma cStar_lt_79 : Work.OddCurve.LowSlope.cStar < (79 / 100 : ℝ) := by
  rw [Work.OddCurve.LowSlope.cStar, inv_lt_iff_one_lt_mul₀ (Real.sqrt_pos.mpr (by norm_num))]
  have h1 : (100 / 79 : ℝ) < Real.sqrt (1 + (4 / 5) ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  calc (1 : ℝ) = (79 / 100) * (100 / 79) := by norm_num
    _ < (79 / 100) * Real.sqrt (1 + (4 / 5) ^ 2) := mul_lt_mul_of_pos_left h1 (by norm_num)

/-! ## Bounds for the classical Abel transform of a bounded profile -/

lemma integral_one_sub_sq_neg_half_le_two :
    (∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ (-(1 / 2 : ℝ))) ≤ 2 := by
  have hint1 : IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    Work.OddRadon.AbelDirect.intervalIntegrable_one_sub_sq_rpow (by norm_num)
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
      (r := -(1 / 2)) (by norm_num)).comp_sub_left 1
    simpa using h.symm
  have hmono : (∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ (-(1 / 2 : ℝ)))
      ≤ ∫ t in (0 : ℝ)..1, (1 - t) ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_mono_on zero_le_one hint1 hint2 ?_
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1; norm_num
    · refine Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < 1 - t) ?_ (by norm_num)
      nlinarith [ht.1, h1]
  have htwo : (∫ t in (0 : ℝ)..1, (1 - t) ^ (-(1 / 2 : ℝ))) = 2 := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) 1
    rw [h]
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
    norm_num
  linarith

/-- **The Abel transform `T_{-1/2}` of a profile bounded by `M` is bounded by `2M`.** -/
lemma abelTrans_neg_half_bound {M a₀ c : ℝ} (hM : 0 ≤ M) (ha₀ : 0 < a₀) (hc : 0 < c)
    (hca : c < a₀) {γ : ℝ → ℝ} (hb : ∀ s ∈ Set.Ioo 0 a₀, |γ s| ≤ M) :
    |Work.OddRadon.abelTrans (-(1 / 2)) γ c| ≤ 2 * M := by
  have hsub := Work.OddRadon.abelTrans_eq_integral_comp_mul (α := -(1 / 2)) γ hc
  have hpow : c ^ (2 * (-(1 / 2 : ℝ)) + 1) = (1 : ℝ) := by
    have hexp : 2 * (-(1 / 2 : ℝ)) + 1 = 0 := by norm_num
    rw [hexp, Real.rpow_zero]
  have hsub' : Work.OddRadon.abelTrans (-(1 / 2)) γ c
      = ∫ t in (0 : ℝ)..1, γ (c * t) * (1 - t ^ 2) ^ (-(1 / 2 : ℝ)) := by
    rw [hsub]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [hpow, one_mul]
  rw [hsub']
  have hint : IntervalIntegrable (fun t : ℝ => M * (1 - t ^ 2) ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    (Work.OddRadon.AbelDirect.intervalIntegrable_one_sub_sq_rpow (p := -(1/2)) (by norm_num)).const_mul M
  have hbd : ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioc (0 : ℝ) 1 →
      ‖γ (c * t) * (1 - t ^ 2) ^ (-(1 / 2 : ℝ))‖ ≤ M * (1 - t ^ 2) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hct : c * t ∈ Set.Ioo 0 a₀ := ⟨by positivity, by nlinarith [hc, ht1, hca]⟩
    have hnn : (0:ℝ) ≤ (1 - t^2) ^ (-(1/2:ℝ)) := Real.rpow_nonneg (by nlinarith [ht0, ht1]) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (hb (c*t) hct) hnn
  calc |∫ t in (0 : ℝ)..1, γ (c * t) * (1 - t ^ 2) ^ (-(1 / 2 : ℝ))|
      = ‖∫ t in (0 : ℝ)..1, γ (c * t) * (1 - t ^ 2) ^ (-(1 / 2 : ℝ))‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ t in (0 : ℝ)..1, M * (1 - t ^ 2) ^ (-(1 / 2 : ℝ)) :=
        intervalIntegral.norm_integral_le_of_norm_le zero_le_one hbd hint
    _ = M * ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ (-(1 / 2 : ℝ)) :=
        intervalIntegral.integral_const_mul M _
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left integral_one_sub_sq_neg_half_le_two hM
    _ = 2 * M := by ring

/-! ## The comparison of the two integral forms -/

lemma abelIntegral_eq_gapIntegral {m M' v : ℝ} (hm : 0 < m) (hmM' : m ≤ M') (hM'v : M' < v)
    {G : ℝ → ℝ} (hGl : ∀ c ∈ Set.Ioo 0 m, G c = 0) (hGr : ∀ c ∈ Set.Ioo M' 1, G c = 0)
    (hv0 : 0 < v) (hv1 : v < 1) :
    (∫ c in (0 : ℝ)..v, c * G c / Real.sqrt (v ^ 2 - c ^ 2))
      = ∫ c in m..M', c * G c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) := by
  set f : ℝ → ℝ := fun c => c * G c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) with hf
  have hstep1 : (∫ c in (0 : ℝ)..v, c * G c / Real.sqrt (v ^ 2 - c ^ 2))
      = ∫ c in (0 : ℝ)..v, f c := by
    apply intervalIntegral.integral_congr
    intro c hc
    rw [Set.uIcc_of_le hv0.le] at hc
    have hnn : 0 ≤ v ^ 2 - c ^ 2 := by nlinarith [hc.1, hc.2]
    simp only [hf]
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hnn, div_eq_mul_inv]
  rw [hstep1, intervalIntegral.integral_of_le hv0.le, intervalIntegral.integral_of_le hmM']
  have h1 : ∫ x in Set.Ioc (0 : ℝ) v, f x = ∫ x in Set.Icc m M', f x := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc ?_ ?_
    · intro x hx
      exact ⟨lt_of_lt_of_le hm hx.1, le_of_lt (lt_of_le_of_lt hx.2 hM'v)⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases lt_or_ge x m with h | h
      · have hxI : x ∈ Set.Ioo 0 m := ⟨hx1.1, h⟩
        simp only [hf]
        rw [hGl x hxI]
        ring
      · have hxM' : M' < x := by
          by_contra hh
          exact hx2 ⟨h, le_of_not_gt hh⟩
        have hxI : x ∈ Set.Ioo M' 1 := ⟨hxM', lt_of_le_of_lt hx1.2 hv1⟩
        simp only [hf]
        rw [hGr x hxI]
        ring
  have h2 : ∫ x in Set.Icc m M', f x = ∫ x in Set.Ioc m M', f x :=
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := m) (b := M')).symm
  rw [h1, h2]

/-! ## The one-sided derivative lemma -/

lemma deriv_eq_of_eventuallyEq_nhdsLT {f g : ℝ → ℝ} {x : ℝ}
    (h : f =ᶠ[𝓝[<] x] g) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv f x = deriv g x := by
  have : (𝓝[<] x).NeBot := nhdsWithin_Iio_neBot le_rfl
  have hfx : f x = g x := by
    have h1 : Tendsto f (𝓝[<] x) (𝓝 (f x)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[<] x) (𝓝 (g x)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h1 (h2.congr' h.symm)
  have h1 : HasDerivWithinAt f (deriv f x) (Set.Iio x) x := hf.hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt g (deriv g x) (Set.Iio x) x := hg.hasDerivAt.hasDerivWithinAt
  have h3 : HasDerivWithinAt f (deriv g x) (Set.Iio x) x := h2.congr_of_eventuallyEq h hfx
  have e1 : derivWithin f (Set.Iio x) x = deriv f x := h1.derivWithin (uniqueDiffWithinAt_Iio x)
  have e2 : derivWithin f (Set.Iio x) x = deriv g x := h3.derivWithin (uniqueDiffWithinAt_Iio x)
  rw [← e1, e2]

lemma deriv_const_mul_uncond (a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => a * f y) x = a * deriv f x := by
  by_cases h : DifferentiableAt ℝ f x
  · exact deriv_const_mul a h
  · rw [deriv_zero_of_not_differentiableAt h, mul_zero]
    by_cases ha : a = 0
    · subst ha; simp
    · refine deriv_zero_of_not_differentiableAt (fun hd => h ?_)
      have h2 : DifferentiableAt ℝ (fun y => a⁻¹ * (a * f y)) x := hd.const_mul a⁻¹
      have h3 : (fun y => a⁻¹ * (a * f y)) = f := by
        funext y; rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      rwa [h3] at h2

/-! ## Numeric facts about `Work.OddCurve.LowSlope.cStar` -/

lemma cStar_sq : Work.OddCurve.LowSlope.cStar ^ 2 = 25 / 41 := by
  rw [Work.OddCurve.LowSlope.cStar, inv_pow]
  have h : Real.sqrt (1 + (4 / 5 : ℝ) ^ 2) ^ 2 = 1 + (4 / 5 : ℝ) ^ 2 :=
    Real.sq_sqrt (by norm_num)
  rw [h]; norm_num

lemma four_fifths_sq_sub_cStar_sq : (4 / 5 : ℝ) ^ 2 - Work.OddCurve.LowSlope.cStar ^ 2 = 31 / 1025 := by
  rw [cStar_sq]; norm_num

lemma cStarThm : (31 / 1025 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 6 := by
  have hkey : (31 / 1025 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (31 / 1025))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 31 / 1025) (1 / 2), ← Real.sqrt_eq_rpow]
  rw [hkey]
  have h3 : (1 / 6 : ℝ) ≤ Real.sqrt (31 / 1025) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h1 : (0 : ℝ) < 1 / 6 := by norm_num
  have h2 : 0 < Real.sqrt (31 / 1025) := Real.sqrt_pos.mpr (by norm_num)
  simpa using (inv_le_inv₀ h2 h1).mpr h3

lemma mul_inv_mul_cancel (a b A : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ * b * (a * b⁻¹ * A) = A := by
  have h2 : a⁻¹ * b * (a * (b⁻¹ * A)) = (a⁻¹ * a) * (b * (b⁻¹ * A)) := by ring
  rw [show a * b⁻¹ * A = a * (b⁻¹ * A) by ring, h2, inv_mul_cancel₀ ha,
    show b * (b⁻¹ * A) = A by rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul], one_mul]

lemma abs_integral_le_of_pointwise {m M' : ℝ} (hmM' : m ≤ M') {f : ℝ → ℝ} {C : ℝ}
    (h : ∀ c ∈ Set.Icc m M', |f c| ≤ C) : |∫ c in m..M', f c| ≤ C * (M' - m) := by
  have hpt : ∀ c ∈ Set.uIoc m M', ‖f c‖ ≤ C := by
    intro c hc
    rw [Set.uIoc_of_le hmM'] at hc
    rw [Real.norm_eq_abs]
    exact h c ⟨le_of_lt hc.1, hc.2⟩
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ M' - m)] at h1
  exact h1

theorem gap_inversion_bounds_free (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ δ : ℝ → ℝ) (a₀ M : ℝ),
      0 < a₀ → a₀ ≤ (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ → 0 ≤ M →
      Function.Even γ →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ (Set.Ioo (0 : ℝ) 1) →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) δ (Set.Ioo (0 : ℝ) 1) →
      (∀ c ∈ Set.Ioo (0 : ℝ) a₀, |γ c| ≤ M) →
      (∀ c ∈ Set.Ioo (0 : ℝ) 1, c < Work.OddEnvelope.tStar → δ c = 0) →
      (∀ c ∈ Set.Ioo (0 : ℝ) 1, a₀ < c → δ c = 0) →
      (∀ c ∈ Set.Ioo (0 : ℝ) a₀, δ c = Work.OddRadon.radonProfile (2 * n + 1) γ c) →
      ∀ u ∈ Set.Icc (4 / 5 : ℝ) 1,
        |Work.OddRadon.radonInverse n δ u| ≤ C * M ∧
        |deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v) u| ≤ C * M ∧
        |deriv (deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v)) u| ≤ C * M := by
  refine ⟨(10 : ℝ) ^ 8, by norm_num, ?_⟩
  intro γ δ a₀ M ha₀ ha₀c hM hγeven hγsm hδsm hγb hδz₁ hδz₂ hδrad u hu
  have hγev : ∀ t, γ (-t) = γ t := hγeven
  have ha₀_one : a₀ < 1 := lt_of_le_of_lt ha₀c (lt_trans Work.OddCurve.LowSlope.cStar_lt_four_fifths (by norm_num))
  have hγcont : ContinuousOn γ (Set.Ioo 0 a₀) :=
    hγsm.continuousOn.mono (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 ha₀_one.le⟩)
  have hγbdd : ∃ M', ∀ s ∈ Set.Ioo 0 a₀, |γ s| ≤ M' := ⟨M, hγb⟩
  set α : ℝ := (n : ℝ) - 3 / 2 with hαdef
  set sA : ℝ := 2 * Work.OddRadon.sphereArea (2 * n - 2) with hsAdef
  set Ψ : ℝ → ℝ := fun c => sA⁻¹ * c ^ (2 * n - 2) * δ c with hΨdef
  set G : ℝ → ℝ := Work.OddRadon.abelReduceIter α (n - 1) Ψ with hGdef
  -- ### 1. the iterated reduction of the datum is the classical Abel transform of γ
  have hΨ_eq : Set.EqOn Ψ (Work.OddRadon.abelTrans α γ) (Set.Ioo 0 a₀) := by
    intro c hc
    rw [hΨdef]
    simp only
    rw [hδrad c hc, Work.OddRadon.radonProfile_eq_abelTrans' n hn hγev hc.1, ← hαdef, hsAdef]
    have h1 : c ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hc.1)
    have h2 : (2 * Work.OddRadon.sphereArea (2 * n - 2)) ≠ 0 :=
      mul_ne_zero (by norm_num) (ne_of_gt (Work.OddRadon.sphereArea_pos _))
    exact mul_inv_mul_cancel _ _ _ h2 h1
  have hG_eq_Phi : ∀ c ∈ Set.Ioo 0 a₀, G c = Work.OddRadon.abelTrans (-(1 / 2)) γ c := by
    intro c hc
    have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
    have hk : (((n - 1 : ℕ)) : ℝ) - 1 < α := by rw [hαdef, hnc]; linarith
    have hiter := abelReduceIter_abelTrans_local ha₀ hγcont hγbdd (β := α) (k := n - 1) hk
    have hcongr := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1) α hΨ_eq
    rw [hGdef, hcongr hc, hiter hc]
    congr 1
    rw [hαdef, hnc]
    ring
  have hG_bound_open : ∀ c ∈ Set.Ioo 0 a₀, |G c| ≤ 2 * M := by
    intro c hc
    rw [hG_eq_Phi c hc]
    exact abelTrans_neg_half_bound hM ha₀ hc.1 hc.2 hγb
  -- ### 2. vanishing off the gap
  have hΨ_zero_l : Set.EqOn Ψ 0 (Set.Ioo 0 Work.OddEnvelope.tStar) := by
    intro c hc
    rw [hΨdef]
    simp only [Pi.zero_apply]
    rw [hδz₁ c ⟨hc.1, lt_trans hc.2 tStar_lt_one⟩ hc.2]
    ring
  have hΨ_zero_r : Set.EqOn Ψ 0 (Set.Ioo a₀ 1) := by
    intro c hc
    rw [hΨdef]
    simp only [Pi.zero_apply]
    rw [hδz₂ c ⟨lt_trans ha₀ hc.1, hc.2⟩ hc.1]
    ring
  have hG_zero_l : ∀ c ∈ Set.Ioo 0 Work.OddEnvelope.tStar, G c = 0 := by
    have h := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1) α hΨ_zero_l
    intro c hc
    rw [hGdef, h hc, abelReduceIter_zero]
    simp
  have hG_zero_r : ∀ c ∈ Set.Ioo a₀ 1, G c = 0 := by
    have h := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1) α hΨ_zero_r
    intro c hc
    rw [hGdef, h hc, abelReduceIter_zero]
    simp
  -- ### 3. smoothness of the reduced datum
  have hΨ_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ (Set.Ioo 0 1) := by
    rw [hΨdef]
    have hpoly : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun c : ℝ => sA⁻¹ * c ^ (2 * n - 2)) (Set.Ioo 0 1) := by fun_prop
    simpa [mul_assoc] using hpoly.mul hδsm
  have hG_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Set.Ioo 0 1) := by
    rw [hGdef]
    refine abelReduceIter_contDiffOn (β := α) (k := n - 1) ?_ hΨ_smooth
    intro j hj
    have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
    have h2 : (j : ℝ) + 1 ≤ ((n - 1 : ℕ) : ℝ) := by
      have : j + 1 ≤ n - 1 := by omega
      exact_mod_cast this
    rw [hnc] at h2
    rw [hαdef]
    intro hzero
    linarith
  -- ### 4. the interval [m, M']
  set m : ℝ := min Work.OddEnvelope.tStar a₀ with hmdef
  set M' : ℝ := max Work.OddEnvelope.tStar a₀ with hM'def
  have hm_pos : 0 < m := by rw [hmdef]; exact lt_min tStar_pos ha₀
  have hmM' : m ≤ M' := by rw [hmdef, hM'def]; exact min_le_max
  have hM'le : M' ≤ Work.OddCurve.LowSlope.cStar := by rw [hM'def]; exact max_le Work.OddCurve.LowSlope.tStar_lt_cStar.le ha₀c
  have hM'pos : 0 < M' := by rw [hM'def]; exact lt_of_lt_of_le tStar_pos (le_max_left _ _)
  have hM'lt : M' < 79 / 100 := lt_of_le_of_lt hM'le cStar_lt_79
  have hM'lt1 : M' < 1 := lt_trans hM'lt (by norm_num)
  have hG_bound : ∀ c ∈ Set.Icc m M', |G c| ≤ 2 * M := by
    have hoff : ∀ c ∈ (Set.Ioo (0 : ℝ) 1) \ {a₀}, |G c| ≤ 2 * M := by
      intro c hc
      obtain ⟨hc1, hca⟩ := hc
      rcases lt_trichotomy c a₀ with h | h | h
      · exact hG_bound_open c ⟨hc1.1, h⟩
      · exact absurd h hca
      · rw [hG_zero_r c ⟨h, hc1.2⟩, abs_zero]
        linarith [hM]
    have ha₀mem : a₀ ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha₀, ha₀_one⟩
    have ha₀b : |G a₀| ≤ 2 * M := by
      have hcont : ContinuousAt G a₀ :=
        hG_smooth.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ha₀mem)
      have ht : Tendsto (fun c => |G c|) (𝓝[{a₀}ᶜ] a₀) (𝓝 |G a₀|) :=
        hcont.abs.tendsto.mono_left (nhdsWithin_le_nhds (s := {a₀}ᶜ))
      refine le_of_tendsto ht ?_
      filter_upwards [Filter.le_def.mp nhdsWithin_le_nhds (Set.Ioo (0 : ℝ) 1)
        (isOpen_Ioo.mem_nhds ha₀mem), self_mem_nhdsWithin] with c hc1 hc2
      exact hoff c ⟨hc1, hc2⟩
    intro c hc
    by_cases hca : c = a₀
    · rw [hca]; exact ha₀b
    · exact hoff c ⟨⟨lt_of_lt_of_le hm_pos hc.1, lt_of_le_of_lt hc.2 hM'lt1⟩, hca⟩
  have hG_cont : ContinuousOn G (Set.Icc m M') :=
    hG_smooth.continuousOn.mono
      (fun x hx => ⟨lt_of_lt_of_le hm_pos hx.1, lt_of_le_of_lt hx.2 hM'lt1⟩)
  -- ### 5. kernel bounds
  have hkeyker : ∀ c ∈ Set.Icc m M', (u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 6 := by
    intro c hc
    have hc0 : 0 ≤ c := le_trans (le_of_lt hm_pos) hc.1
    have h1 : (31 / 1025 : ℝ) ≤ u ^ 2 - c ^ 2 := by
      have hu45 : (4 / 5 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith [hu.1]
      have hM'c : M' ^ 2 ≤ Work.OddCurve.LowSlope.cStar ^ 2 := by nlinarith [hM'le, le_of_lt Work.OddCurve.LowSlope.cStar_pos, Work.OddCurve.LowSlope.cStar_pos]
      have hcc : c ^ 2 ≤ M' ^ 2 := by nlinarith [hc0, hc.2, le_of_lt (lt_of_lt_of_le hm_pos hmM')]
      nlinarith [hu45, hM'c, hcc, four_fifths_sq_sub_cStar_sq]
    exact le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) h1 (by norm_num)) cStarThm
  have hker_pos : ∀ c ∈ Set.Icc m M', 0 < u ^ 2 - c ^ 2 := by
    intro c hc
    have hc0 : 0 ≤ c := le_trans (le_of_lt hm_pos) hc.1
    have h1 : (31 / 1025 : ℝ) ≤ u ^ 2 - c ^ 2 := by
      have hu45 : (4 / 5 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith [hu.1]
      have hM'c : M' ^ 2 ≤ Work.OddCurve.LowSlope.cStar ^ 2 := by nlinarith [hM'le, le_of_lt Work.OddCurve.LowSlope.cStar_pos, Work.OddCurve.LowSlope.cStar_pos]
      have hcc : c ^ 2 ≤ M' ^ 2 := by nlinarith [hc0, hc.2, le_of_lt (lt_of_lt_of_le hm_pos hmM')]
      nlinarith [hu45, hM'c, hcc, four_fifths_sq_sub_cStar_sq]
    linarith
  have hker3 : ∀ c ∈ Set.Icc m M', (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)) ≤ 6 ^ 3 := by
    intro c hc
    have hpos := hker_pos c hc
    have h3 : (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)) = ((u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))) ^ 3 := by
      rw [show (-(3 / 2) : ℝ) = (-(1 / 2)) * 3 by norm_num, Real.rpow_mul hpos.le]
      simp
    rw [h3]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) (hkeyker c hc) 3
  have hker5 : ∀ c ∈ Set.Icc m M', (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)) ≤ 6 ^ 5 := by
    intro c hc
    have hpos := hker_pos c hc
    have h3 : (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)) = ((u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))) ^ 5 := by
      rw [show (-(5 / 2) : ℝ) = (-(1 / 2)) * 5 by norm_num, Real.rpow_mul hpos.le]
      simp
    rw [h3]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) (hkeyker c hc) 5
  have hker7 : ∀ c ∈ Set.Icc m M', (u ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ)) ≤ 6 ^ 7 := by
    intro c hc
    have hpos := hker_pos c hc
    have h3 : (u ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ)) = ((u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))) ^ 7 := by
      rw [show (-(7 / 2) : ℝ) = (-(1 / 2)) * 7 by norm_num, Real.rpow_mul hpos.le]
      simp
    rw [h3]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) (hkeyker c hc) 7
  -- ### 6. the kernel-derivative functions and the comparison
  have hu79 : (79 / 100 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu.1
  have hu11 : u < (11 / 10 : ℝ) := lt_of_le_of_lt hu.2 (by norm_num)
  have hu79' : u ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10) := ⟨hu79, hu11⟩
  set I : ℝ → ℝ := fun v => ∫ c in m..M', c * G c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) with hIdef
  set J1 : ℝ → ℝ := fun v => ∫ c in m..M', c * G c * (-v * (v ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ))) with hJ1def
  set J2 : ℝ → ℝ := fun v => ∫ c in m..M',
    c * G c * ((2 * v ^ 2 + c ^ 2) * (v ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ))) with hJ2def
  set J3 : ℝ → ℝ := fun v => ∫ c in m..M',
    c * G c * ((-(6 * v ^ 3) - 9 * v * c ^ 2) * (v ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ))) with hJ3def
  set Bfun : ℝ → ℝ := fun w => ∫ c in (0 : ℝ)..w, c * G c / Real.sqrt (w ^ 2 - c ^ 2) with hBfundef
  have hcmp : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) 1, Bfun v = I v := by
    intro v hv
    rw [hBfundef, hIdef]
    exact abelIntegral_eq_gapIntegral (v := v) hm_pos hmM'
      (lt_of_le_of_lt hM'le (lt_trans cStar_lt_79 hv.1))
      (fun c hc => hG_zero_l c ⟨hc.1, lt_of_lt_of_le hc.2 (by rw [hmdef]; exact min_le_left _ _)⟩)
      (fun c hc => hG_zero_r c ⟨lt_of_le_of_lt (by rw [hM'def]; exact le_max_right _ _) hc.1, hc.2⟩)
      (lt_trans (by norm_num : (0 : ℝ) < 79 / 100) hv.1) hv.2
  have hgap := Work.OddCurve.LowSlope.gapKernel_derivs (m := m) (M' := M') (B := 2 * M) (le_of_lt hm_pos) hmM' hM'lt
    hG_cont hG_bound
  have hd1 : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10), HasDerivAt I (J1 v) v := by
    intro v hv; simpa [hIdef, hJ1def] using (hgap v hv).1
  have hd2 : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10), HasDerivAt J1 (J2 v) v := by
    intro v hv; simpa [hJ1def, hJ2def] using (hgap v hv).2.1
  have hd3 : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10), HasDerivAt J2 (J3 v) v := by
    intro v hv; simpa [hJ2def, hJ3def] using (hgap v hv).2.2
  -- ### 7. the iterated derivatives of the Abel integral
  set F0 : ℝ → ℝ := fun v => deriv Bfun v with hF0def
  set F1 : ℝ → ℝ := fun v => deriv F0 v with hF1def
  set F2 : ℝ → ℝ := fun v => deriv F1 v with hF2def
  have hF0J : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) 1, F0 v = J1 v := by
    intro v hv
    have hev : Bfun =ᶠ[𝓝 v] I := by
      filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
      exact hcmp w hw
    have h1 : deriv Bfun v = deriv I v := hev.deriv_eq
    have h2 : deriv I v = J1 v := (hd1 v ⟨hv.1, by linarith [hv.2]⟩).deriv
    rw [hF0def]; exact h1.trans h2
  have hF1J : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) 1, F1 v = J2 v := by
    intro v hv
    have hev : F0 =ᶠ[𝓝 v] J1 := by
      filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
      exact hF0J w hw
    have h1 : deriv F0 v = deriv J1 v := hev.deriv_eq
    have h2 : deriv J1 v = J2 v := (hd2 v ⟨hv.1, by linarith [hv.2]⟩).deriv
    rw [hF1def]; exact h1.trans h2
  have hF2J : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) 1, F2 v = J3 v := by
    intro v hv
    have hev : F1 =ᶠ[𝓝 v] J2 := by
      filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
      exact hF1J w hw
    have h1 : deriv F1 v = deriv J2 v := hev.deriv_eq
    have h2 : deriv J2 v = J3 v := (hd3 v ⟨hv.1, by linarith [hv.2]⟩).deriv
    rw [hF2def]; exact h1.trans h2
  -- ### 8. one-sided comparison at u
  have hB_left : Bfun =ᶠ[𝓝[<] u] I := by
    filter_upwards [Ioo_mem_nhdsLT hu79] with w hw
    exact hcmp w ⟨hw.1, lt_of_lt_of_le hw.2 hu.2⟩
  have hF0_left : F0 =ᶠ[𝓝[<] u] J1 := by
    filter_upwards [Ioo_mem_nhdsLT hu79] with w hw
    exact hF0J w ⟨hw.1, lt_of_lt_of_le hw.2 hu.2⟩
  have hF1_left : F1 =ᶠ[𝓝[<] u] J2 := by
    filter_upwards [Ioo_mem_nhdsLT hu79] with w hw
    exact hF1J w ⟨hw.1, lt_of_lt_of_le hw.2 hu.2⟩
  have hF2_left : F2 =ᶠ[𝓝[<] u] J3 := by
    filter_upwards [Ioo_mem_nhdsLT hu79] with w hw
    exact hF2J w ⟨hw.1, lt_of_lt_of_le hw.2 hu.2⟩
  have hJu1 : |F0 u| ≤ |J1 u| := by
    by_cases hd : DifferentiableAt ℝ Bfun u
    · change |deriv Bfun u| ≤ |J1 u|
      have h1 : deriv Bfun u = deriv I u :=
        deriv_eq_of_eventuallyEq_nhdsLT hB_left hd (hd1 u hu79').differentiableAt
      rw [h1, (hd1 u hu79').deriv]
    · change |deriv Bfun u| ≤ |J1 u|
      rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
      exact abs_nonneg _
  have hJu2 : |F1 u| ≤ |J2 u| := by
    by_cases hd : DifferentiableAt ℝ F0 u
    · change |deriv F0 u| ≤ |J2 u|
      have h1 : deriv F0 u = deriv J1 u :=
        deriv_eq_of_eventuallyEq_nhdsLT hF0_left hd (hd2 u hu79').differentiableAt
      rw [h1, (hd2 u hu79').deriv]
    · change |deriv F0 u| ≤ |J2 u|
      rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
      exact abs_nonneg _
  have hJu3 : |F2 u| ≤ |J3 u| := by
    by_cases hd : DifferentiableAt ℝ F1 u
    · change |deriv F1 u| ≤ |J3 u|
      have h1 : deriv F1 u = deriv J2 u :=
        deriv_eq_of_eventuallyEq_nhdsLT hF1_left hd (hd3 u hu79').differentiableAt
      rw [h1, (hd3 u hu79').deriv]
    · change |deriv F1 u| ≤ |J3 u|
      rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
      exact abs_nonneg _
  -- ### 9. bounds for the kernels
  have hJu1bd : |J1 u| ≤ 432 * M := by
    have hJ1u : J1 u = ∫ c in m..M', c * G c * (-u * (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ))) := by
      rw [hJ1def]
    rw [hJ1u]
    have hpt : ∀ c ∈ Set.Icc m M',
        |c * G c * (-u * (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)))| ≤ 432 * M := by
      intro c hc
      have hc0 : 0 ≤ c := le_trans (le_of_lt hm_pos) hc.1
      have hGc := hG_bound c hc
      have hk := hker3 c hc
      have hk0 : 0 ≤ (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt (hker_pos c hc)) _
      have h1 : |c * G c| ≤ M' * (2 * M) := by
        rw [abs_mul]
        refine mul_le_mul ?_ hGc (abs_nonneg _) (by linarith [hM])
        rw [abs_of_nonneg hc0]; exact hc.2
      have h2 : |(-u) * (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ))| ≤ 1 * 6 ^ 3 := by
        rw [abs_mul, abs_neg, abs_of_nonneg (by linarith [hu.1] : (0 : ℝ) ≤ u), abs_of_nonneg hk0]
        exact mul_le_mul hu.2 hk hk0 (by norm_num)
      calc |c * G c * (-u * (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)))|
          = |c * G c| * |(-u) * (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ))| := by rw [abs_mul]
        _ ≤ (M' * (2 * M)) * (1 * 6 ^ 3) := mul_le_mul h1 h2 (by positivity) (mul_nonneg hM'pos.le (by linarith [hM]))
        _ ≤ 432 * M := by nlinarith [hM'lt1, hM]
    refine le_trans (abs_integral_le_of_pointwise hmM' hpt) ?_
    have h2 : M' - m ≤ 1 := by linarith [hmM', hM'lt1]
    nlinarith [h2, hM]
  have hJu2bd : |J2 u| ≤ 46656 * M := by
    have hJ2u : J2 u = ∫ c in m..M',
        c * G c * ((2 * u ^ 2 + c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ))) := by
      rw [hJ2def]
    rw [hJ2u]
    have hpt : ∀ c ∈ Set.Icc m M',
        |c * G c * ((2 * u ^ 2 + c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)))| ≤ 46656 * M := by
      intro c hc
      have hc0 : 0 ≤ c := le_trans (le_of_lt hm_pos) hc.1
      have hGc := hG_bound c hc
      have hk := hker5 c hc
      have hk0 : 0 ≤ (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt (hker_pos c hc)) _
      have h1 : |c * G c| ≤ M' * (2 * M) := by
        rw [abs_mul]
        refine mul_le_mul ?_ hGc (abs_nonneg _) (by linarith [hM])
        rw [abs_of_nonneg hc0]; exact hc.2
      have h2 : |(2 * u ^ 2 + c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ))| ≤ 3 * 6 ^ 5 := by
        have hpoly : |2 * u ^ 2 + c ^ 2| ≤ 3 := by
          rw [abs_of_nonneg (by positivity)]
          nlinarith [hu.2, hc.2, hM'lt1, hc0, hu.1]
        rw [abs_mul, abs_of_nonneg hk0]
        exact mul_le_mul hpoly hk hk0 (by norm_num)
      calc |c * G c * ((2 * u ^ 2 + c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)))|
          = |c * G c| * |(2 * u ^ 2 + c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ))| := by rw [abs_mul]
        _ ≤ (M' * (2 * M)) * (3 * 6 ^ 5) := mul_le_mul h1 h2 (by positivity) (mul_nonneg hM'pos.le (by linarith [hM]))
        _ ≤ 46656 * M := by nlinarith [hM'lt1, hM]
    refine le_trans (abs_integral_le_of_pointwise hmM' hpt) ?_
    have h2 : M' - m ≤ 1 := by linarith [hmM', hM'lt1]
    nlinarith [h2, hM]
  have hJu3bd : |J3 u| ≤ 8398080 * M := by
    have hJ3u : J3 u = ∫ c in m..M',
        c * G c * ((-(6 * u ^ 3) - 9 * u * c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ))) := by
      rw [hJ3def]
    rw [hJ3u]
    have hpt : ∀ c ∈ Set.Icc m M',
        |c * G c * ((-(6 * u ^ 3) - 9 * u * c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ)))| ≤ 8398080 * M := by
      intro c hc
      have hc0 : 0 ≤ c := le_trans (le_of_lt hm_pos) hc.1
      have hGc := hG_bound c hc
      have hk := hker7 c hc
      have hk0 : 0 ≤ (u ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt (hker_pos c hc)) _
      have h1 : |c * G c| ≤ M' * (2 * M) := by
        rw [abs_mul]
        refine mul_le_mul ?_ hGc (abs_nonneg _) (by linarith [hM])
        rw [abs_of_nonneg hc0]; exact hc.2
      have h2 : |(-(6 * u ^ 3) - 9 * u * c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ))| ≤ 15 * 6 ^ 7 := by
        have hpoly : |(-(6 * u ^ 3) - 9 * u * c ^ 2)| ≤ 15 := by
          rw [abs_of_nonpos (by nlinarith [hu.1, hu.2, hc0, hc.2])]
          nlinarith [hu.1, hu.2, hc0, hc.2, hM'lt1]
        rw [abs_mul, abs_of_nonneg hk0]
        exact mul_le_mul hpoly hk hk0 (by norm_num)
      calc |c * G c * ((-(6 * u ^ 3) - 9 * u * c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ)))|
          = |c * G c| * |(-(6 * u ^ 3) - 9 * u * c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ))| := by rw [abs_mul]
        _ ≤ (M' * (2 * M)) * (15 * 6 ^ 7) := mul_le_mul h1 h2 (by positivity) (mul_nonneg hM'pos.le (by linarith [hM]))
        _ ≤ 8398080 * M := by nlinarith [hM'lt1, hM]
    refine le_trans (abs_integral_le_of_pointwise hmM' hpt) ?_
    have h2 : M' - m ≤ 1 := by linarith [hmM', hM'lt1]
    nlinarith [h2, hM]
  -- ### 10. the value of radonInverse and its derivatives
  have hB : (fun w : ℝ => ∫ c in (0 : ℝ)..w,
      c * (Work.OddRadon.abelReduceIter α (n - 1)
        (fun c => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * δ c)) c
      / Real.sqrt (w ^ 2 - c ^ 2)) = Bfun := by
    funext w
    rw [hBfundef]
  have hR0 : ∀ v, Work.OddRadon.radonInverse n δ v = (2 / Real.pi) * F0 v := by
    intro v
    rw [hF0def]
    simp only [Work.OddRadon.radonInverse, Work.OddRadon.abelInvert]
    rw [hB]
  have hR1 : deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v) = fun v => (2 / Real.pi) * F1 v := by
    have h1 : (fun v : ℝ => Work.OddRadon.radonInverse n δ v) = fun v => (2 / Real.pi) * F0 v :=
      funext hR0
    rw [h1]
    funext v
    rw [hF1def]
    exact deriv_const_mul_uncond (2 / Real.pi) F0 v
  have hR2 : deriv (deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v)) =
      fun v => (2 / Real.pi) * F2 v := by
    rw [hR1]
    funext v
    rw [hF2def]
    exact deriv_const_mul_uncond (2 / Real.pi) F1 v
  have hval0 : |Work.OddRadon.radonInverse n δ u| = (2 / Real.pi) * |F0 u| := by
    rw [hR0 u, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have hval1 : |deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v) u| = (2 / Real.pi) * |F1 u| := by
    rw [hR1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have hval2 : |deriv (deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v)) u| =
      (2 / Real.pi) * |F2 u| := by
    rw [hR2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have hpi : (2 / Real.pi) ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  refine ⟨?_, ?_, ?_⟩
  · rw [hval0]
    calc (2 / Real.pi) * |F0 u| ≤ (2 / Real.pi) * |J1 u| := mul_le_mul_of_nonneg_left hJu1 (by positivity)
      _ ≤ (2 / Real.pi) * (432 * M) := mul_le_mul_of_nonneg_left hJu1bd (by positivity)
      _ ≤ (10 : ℝ) ^ 8 * M := by nlinarith [hpi, hM]
  · rw [hval1]
    calc (2 / Real.pi) * |F1 u| ≤ (2 / Real.pi) * |J2 u| := mul_le_mul_of_nonneg_left hJu2 (by positivity)
      _ ≤ (2 / Real.pi) * (46656 * M) := mul_le_mul_of_nonneg_left hJu2bd (by positivity)
      _ ≤ (10 : ℝ) ^ 8 * M := by nlinarith [hpi, hM]
  · rw [hval2]
    calc (2 / Real.pi) * |F2 u| ≤ (2 / Real.pi) * |J3 u| := mul_le_mul_of_nonneg_left hJu3 (by positivity)
      _ ≤ (2 / Real.pi) * (8398080 * M) := mul_le_mul_of_nonneg_left hJu3bd (by positivity)
      _ ≤ (10 : ℝ) ^ 8 * M := by nlinarith [hpi, hM]

end

end Work.OddVolterra.Free
