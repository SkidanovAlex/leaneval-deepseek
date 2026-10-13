import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Submission.Work.FTS_EllLimOK.SliceTrace.abs_le_half_sq_mul_rpow_add
import Submission.Work.FTS_EllLimOK.SliceTrace.abs_deriv_sub_le_intervalIntegral
import Submission.Work.FTS_EllLimOK.SliceTrace.exists_abs_le_of_integrable_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.SliceTrace

/-!
# Endpoint decay of `deriv f` at `π/2`

Auxiliary lemmas for `deriv_tendsto_zero_at_pi_div_two`.

With `g = deriv f` and `s θ = sin (2θ)` the two integrability hypotheses are

* `∫ (g')² s^{-η} < ∞`, which makes the *variation* of `g` near `π/2` small
  (fundamental theorem of calculus together with `2ab ≤ a² + b²`), and
* `∫ g² s^{-γ} < ∞` with `γ > 1`, which forces a point near `π/2` where `g` is small
  (because `s^{-γ}` fails to be integrable at `π/2`).

Combining the two gives `g x → 0`.
-/

lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

lemma sin_two_le_one {θ : ℝ} : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- **Tail integrals of an `L¹`-function on `(0, π/2)` vanish at the right endpoint.** -/
theorem tendsto_setIntegral_tail_pi_div_two {F : ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto (fun s : ℝ => ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2), F x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmeas : Filter.Tendsto
      (fun s : ℝ => MeasureTheory.volume (Set.Ioo (Real.pi / 2 - s) (Real.pi / 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => ENNReal.ofReal s) (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
      have hcont : Filter.Tendsto (fun s : ℝ => s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (0 : ℝ)) :=
        Filter.Tendsto.mono_left Filter.tendsto_id nhdsWithin_le_nhds
      simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (m := fun s : ℝ => s) (a := 0) hcont
    have hEq : (fun s : ℝ =>
          MeasureTheory.volume (Set.Ioo (Real.pi / 2 - s) (Real.pi / 2)))
        = fun s : ℝ => ENNReal.ofReal s := by
      funext s
      rw [Real.volume_Ioo, show Real.pi / 2 - (Real.pi / 2 - s) = s by ring]
    rw [hEq]
    exact h1
  have hGint : MeasureTheory.Integrable ((Set.Ioo 0 (Real.pi / 2)).indicator F)
      MeasureTheory.volume := hF.integrable_indicator measurableSet_Ioo
  have hmain : Filter.Tendsto
      (fun s : ℝ => ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2),
        (Set.Ioo 0 (Real.pi / 2)).indicator F x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hGint.tendsto_setIntegral_nhds_zero
      (s := fun s : ℝ => Set.Ioo (Real.pi / 2 - s) (Real.pi / 2)) hmeas
  have heq : (fun s : ℝ => ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2),
        (Set.Ioo 0 (Real.pi / 2)).indicator F x)
      =ᶠ[nhds (0 : ℝ)]
        (fun s : ℝ => ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2), F x) := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with s hs
    rw [Set.mem_Iio] at hs
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [Set.mem_Ioo] at hx
    exact Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨by linarith [hx.1, hs], hx.2⟩) F
  exact Filter.Tendsto.congr' (Filter.Eventually.filter_mono nhdsWithin_le_nhds heq) hmain

/-- If `F` is integrable on `(0, π/2)` then for every target length `a > 0` and `ε > 0`
there is a tail `(t, π/2)` of length at most `a` whose integral is at most `ε`. -/
theorem exists_tail_le {F : ℝ → ℝ} (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 (Real.pi / 2)))
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo 0 (Real.pi / 2),
      Real.pi / 2 - t ≤ a ∧ ∫ x in Set.Ioo t (Real.pi / 2), F x ≤ ε := by
  have htail := tendsto_setIntegral_tail_pi_div_two hF
  rw [Metric.tendsto_nhdsWithin_nhds] at htail
  obtain ⟨δ, hδ0, hδ⟩ := htail ε hε
  set s : ℝ := min (min (δ / 2) a) (Real.pi / 4) with hs
  have hs0 : 0 < s := lt_min (lt_min (by linarith) ha) (by positivity)
  have hsa : s ≤ a := le_trans (min_le_left _ _) (min_le_right _ _)
  have hsδ : s < δ :=
    lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hsπ : s ≤ Real.pi / 4 := min_le_right _ _
  have hint : ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2), F x ≤ ε := by
    have h := hδ (x := s) (by rw [Set.mem_Ioi]; exact hs0)
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hsδ)
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt (abs_lt.mp h).2
  refine ⟨Real.pi / 2 - s, ⟨by linarith [hsπ, Real.pi_pos], by linarith [hs0]⟩,
    by linarith [hsa], hint⟩

/-- Integrability of `sin (2·)^η` on a tail, for `η ≥ 0`. -/
theorem integrableOn_sin_two_rpow {η : ℝ} (hη : 0 ≤ η) {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (Real.sin (2 * x)) ^ η)
      (Set.Ioo t (Real.pi / 2)) := by
  have hvol : MeasureTheory.volume (Set.Ioo t (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo t (Real.pi / 2)) :=
    MeasureTheory.integrableOn_const hvol
  refine MeasureTheory.Integrable.mono' h1
    ((by fun_prop : Measurable fun x : ℝ => (Real.sin (2 * x)) ^ η).aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  have hx' : 0 < Real.sin (2 * x) := sin_two_pos_of_mem_Ioo ⟨lt_of_le_of_lt ht hx.1, hx.2⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx' η)]
  exact Real.rpow_le_one (le_of_lt hx') sin_two_le_one hη

/-- The `η`-weighted integral of `sin (2·)` over a tail is at most the tail length. -/
theorem setIntegral_sin_two_rpow_le_length {η : ℝ} (hη : 0 ≤ η) {t : ℝ} (ht : 0 ≤ t)
    (ht2 : t ≤ Real.pi / 2) :
    ∫ x in Set.Ioo t (Real.pi / 2), (Real.sin (2 * x)) ^ η ≤ Real.pi / 2 - t := by
  have hvol : MeasureTheory.volume (Set.Ioo t (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo t (Real.pi / 2)) :=
    MeasureTheory.integrableOn_const hvol
  have hpoint : ∀ x ∈ Set.Ioo t (Real.pi / 2), (Real.sin (2 * x)) ^ η ≤ (1 : ℝ) :=
    fun x hx => Real.rpow_le_one (le_of_lt (sin_two_pos_of_mem_Ioo
      ⟨lt_of_le_of_lt ht hx.1, hx.2⟩)) sin_two_le_one hη
  calc ∫ x in Set.Ioo t (Real.pi / 2), (Real.sin (2 * x)) ^ η
      ≤ ∫ x in Set.Ioo t (Real.pi / 2), (1 : ℝ) :=
        MeasureTheory.setIntegral_mono_on (integrableOn_sin_two_rpow hη ht) h1
          measurableSet_Ioo hpoint
    _ = Real.pi / 2 - t := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (show (0 : ℝ) ≤ Real.pi / 2 - t by linarith [ht2])]
        simp

/-- The same bound over a tail `(t, π/2)`. -/
theorem abs_deriv_sub_le_tail_aux {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {t x y : ℝ} (ht : 0 < t) (hx : x ∈ Set.Ioo t (Real.pi / 2))
    (hy : y ∈ Set.Ioo t (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun z => |deriv (deriv f) z|) (Set.Ioo t (Real.pi / 2))) :
    |deriv f x - deriv f y| ≤ ∫ z in Set.Ioo t (Real.pi / 2), |deriv (deriv f) z| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm]
    refine (abs_deriv_sub_le_intervalIntegral (a := x) (b := y) hf (lt_trans ht hx.1) hxy
      hy.2).trans ?_
    rw [intervalIntegral.integral_of_le hxy, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact MeasureTheory.setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun z hz => ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩)
  · refine (abs_deriv_sub_le_intervalIntegral (a := y) (b := x) hf (lt_trans ht hy.1) hyx
      hx.2).trans ?_
    rw [intervalIntegral.integral_of_le hyx, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact MeasureTheory.setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun z hz => ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hx.2⟩)

/-- **The variation bound**: the oscillation of `deriv f` on a tail is bounded by half the
sum of the two weighted `L²`-tails. -/
theorem abs_deriv_sub_le_half_weights_aux {η : ℝ} (hη : 0 ≤ η) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)))
    {t x y : ℝ} (ht : 0 < t) (hx : x ∈ Set.Ioo t (Real.pi / 2))
    (hy : y ∈ Set.Ioo t (Real.pi / 2)) :
    |deriv f x - deriv f y| ≤
      ((∫ z in Set.Ioo t (Real.pi / 2),
          (deriv (deriv f) z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
  have hF1int : MeasureTheory.IntegrableOn
      (fun z => (deriv (deriv f) z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
      (Set.Ioo t (Real.pi / 2)) := h2.mono_set (Set.Ioo_subset_Ioo_left ht.le)
  have hSint : MeasureTheory.IntegrableOn (fun z => (Real.sin (2 * z)) ^ η)
      (Set.Ioo t (Real.pi / 2)) := integrableOn_sin_two_rpow hη ht.le
  have hs : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo le_rfl
  have hs2 : ContDiffOn ℝ 0 (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) :=
    hs.deriv_of_isOpen isOpen_Ioo le_rfl
  have hcont2 : ContinuousOn (fun z => |deriv (deriv f) z|) (Set.Ioo t (Real.pi / 2)) :=
    (hs2.mono (Set.Ioo_subset_Ioo_left ht.le)).continuousOn.abs
  have hpoint : ∀ z ∈ Set.Ioo t (Real.pi / 2),
      |deriv (deriv f) z| ≤ ((deriv (deriv f) z) ^ 2 * (Real.sin (2 * z)) ^ (-η)
        + (Real.sin (2 * z)) ^ η) / 2 :=
    fun z hz => abs_le_half_sq_mul_rpow_add
      (sin_two_pos_of_mem_Ioo ⟨lt_trans ht hz.1, hz.2⟩)
  have hgint : MeasureTheory.IntegrableOn (fun z => |deriv (deriv f) z|)
      (Set.Ioo t (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' (f := fun z => |deriv (deriv f) z|)
      ((hF1int.add hSint).div_const 2)
      (hcont2.aestronglyMeasurable measurableSet_Ioo) (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
        rw [Real.norm_eq_abs, abs_abs]
        exact hpoint z hz)
  have hmono := MeasureTheory.setIntegral_mono_on hgint ((hF1int.add hSint).div_const 2)
    measurableSet_Ioo hpoint
  have hsplit : (∫ z in Set.Ioo t (Real.pi / 2),
        ((deriv (deriv f) z) ^ 2 * (Real.sin (2 * z)) ^ (-η)
          + (Real.sin (2 * z)) ^ η) / 2)
      = ((∫ z in Set.Ioo t (Real.pi / 2),
            (deriv (deriv f) z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
          + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hF1int hSint]
  have hL1 : ∫ z in Set.Ioo t (Real.pi / 2), |deriv (deriv f) z| ≤
      ((∫ z in Set.Ioo t (Real.pi / 2),
          (deriv (deriv f) z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
    rw [← hsplit]
    exact hmono
  exact (abs_deriv_sub_le_tail_aux hf ht hx hy hgint).trans hL1

theorem deriv_tendsto_zero_at_pi_div_two {η γ : ℝ} (hη : 0 ≤ η) (hγ : 1 < γ) {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2))) (h1 : MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) (Set.Ioo 0 (Real.pi / 2))) : Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ δ > 0, ∀ x : ℝ, x ∈ Set.Iio (Real.pi / 2) →
      dist x (Real.pi / 2) < δ → dist (deriv f x) 0 < ε := by
    intro ε hε hε1
    -- a short tail on which the weighted second-derivative integral is small
    obtain ⟨t, ht, htlen, htU⟩ := exists_tail_le
      (F := fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) h2
      (a := ε ^ 2 / 16) (ε := ε ^ 2 / 8) (by positivity) (by positivity)
    have htV : ∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η ≤ ε ^ 2 / 8 :=
      (setIntegral_sin_two_rpow_le_length hη ht.1.le ht.2.le).trans (by nlinarith [htlen, hε])
    -- a point of the tail where `deriv f` is small
    have hpoint : ∃ τ ∈ Set.Ioo t (Real.pi / 2), |deriv f τ| ≤ ε / 2 :=
      exists_abs_le_of_integrable_weighted hγ (f := deriv f) ht
        (h1.mono_set (Set.Ioo_subset_Ioo_left ht.1.le)) (by positivity)
    obtain ⟨τ, hτ, hτle⟩ := hpoint
    refine ⟨Real.pi / 2 - t, by linarith [ht.2], fun x hx hdx => ?_⟩
    have hxt : x ∈ Set.Ioo t (Real.pi / 2) := by
      rw [Real.dist_eq] at hdx
      rw [abs_lt] at hdx
      exact ⟨by linarith [hdx.1], hx⟩
    have hvar := abs_deriv_sub_le_half_weights_aux hη hf h2 ht.1 hxt hτ
    have hbound : ((∫ z in Set.Ioo t (Real.pi / 2),
          (deriv (deriv f) z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 ≤ ε ^ 2 / 8 := by
      linarith
    have htri : |deriv f x| ≤ |deriv f x - deriv f τ| + |deriv f τ| := by
      have h := abs_add_le (deriv f x - deriv f τ) (deriv f τ)
      rwa [sub_add_cancel] at h
    have hε2 : ε ^ 2 ≤ ε := by nlinarith [hε1, hε.le]
    rw [Real.dist_eq, sub_zero]
    linarith [hvar.trans hbound, hτle, htri, hε2]
  intro ε hε
  rcases le_or_gt (1 / 2 : ℝ) ε with hbig | hsmall
  · obtain ⟨δ, hδ0, hδ⟩ := key (1 / 2) (by norm_num) (by norm_num)
    exact ⟨δ, hδ0, fun x hx hd => lt_of_lt_of_le (hδ x hx hd) hbig⟩
  · exact key ε hε (by linarith)

end Work.FTS_EllLimOK.SliceTrace
