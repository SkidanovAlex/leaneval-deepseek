import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_EllLimOK.SliceTrace.deriv_tendsto_zero_at_pi_div_two
import Submission.Work.FTS_EllLimOK.SliceTrace.exists_abs_le_of_integrable_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Real

namespace Work.FTS_EllLimOK.SliceTrace

/-!
# The endpoint trace of a function with two weighted `L²` bounds

This is the first-order companion of `deriv_tendsto_zero_at_pi_div_two`.  There, `f` is `C²`
and the conclusion is `deriv f → 0`; here `g` is only `C¹` and the conclusion is `g → 0`.

The two hypotheses are the natural ones for the argument:

* `∫_t^{π/2} g² sin(2θ)^{-γ} < ∞` with `γ > 1`: since `sin(2θ)^{-γ}` fails to be
  integrable at `π/2`, `g` must be small somewhere on every tail
  (`exists_abs_le_of_integrable_weighted`), giving a point `τ` with `|g τ| ≤ ε/2`;
* `∫_0^{π/2} (g')² sin(2θ)^{-η} < ∞` with `η ≥ 0`: on the tail `(t', π/2)` the fundamental
  theorem of calculus bounds the *variation* of `g` by
  `(∫ (g')² sin^{-η} + ∫ sin^{η})/2` (AM–GM against the weight), and both pieces can be made
  as small as we wish.

Combining the two gives `g x → 0` as `x → π/2⁻`.
-/

/-- **Fundamental theorem of calculus for a `C¹` function** on a closed subinterval of
`(0, π/2)`: the oscillation of `g` is bounded by the integral of `|g'|`. -/
private theorem abs_sub_le_intervalIntegral_deriv {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi / 2))) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    |g b - g a| ≤ ∫ x in a..b, |deriv g x| := by
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hsub' : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  -- `deriv g` is continuous on `[a,b]`, hence interval integrable
  have hcont : ContinuousOn (deriv g) (Set.uIcc a b) :=
    (hg.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn.mono hsub
  have hint : IntervalIntegrable (deriv g) volume a b := hcont.intervalIntegrable
  have hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt g (deriv g x) x := by
    intro x hx
    exact ((hg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩)).hasDerivAt
  have hFTC : ∫ x in a..b, deriv g x = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hg.continuousOn.mono hsub')
      hdiff hint
  rw [← hFTC]
  exact intervalIntegral.abs_integral_le_integral_abs hab

/-- **The variation bound**: the oscillation of a `C¹` function `g` on a tail is bounded by
half the sum of the two weighted `L²`-tails (`η`-weight on `g'`, and the reciprocal weight). -/
private theorem abs_sub_le_half_weights_deriv_aux {η : ℝ} (hη : 0 ≤ η) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)))
    {t x y : ℝ} (ht : 0 < t) (hx : x ∈ Set.Ioo t (Real.pi / 2))
    (hy : y ∈ Set.Ioo t (Real.pi / 2)) :
    |g x - g y| ≤
      ((∫ z in Set.Ioo t (Real.pi / 2),
          (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
  have hF1int : MeasureTheory.IntegrableOn
      (fun z => (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
      (Set.Ioo t (Real.pi / 2)) := h2.mono_set (Set.Ioo_subset_Ioo_left ht.le)
  have hSint : MeasureTheory.IntegrableOn (fun z => (Real.sin (2 * z)) ^ η)
      (Set.Ioo t (Real.pi / 2)) := integrableOn_sin_two_rpow hη ht.le
  have hcont2 : ContinuousOn (fun z => |deriv g z|) (Set.Ioo t (Real.pi / 2)) :=
    ((hg.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn.mono
      (Set.Ioo_subset_Ioo_left ht.le)).abs
  have hpoint : ∀ z ∈ Set.Ioo t (Real.pi / 2),
      |deriv g z| ≤ ((deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η)
        + (Real.sin (2 * z)) ^ η) / 2 :=
    fun z hz => abs_le_half_sq_mul_rpow_add
      (sin_two_pos_of_mem_Ioo ⟨lt_trans ht hz.1, hz.2⟩)
  have hgint : MeasureTheory.IntegrableOn (fun z => |deriv g z|)
      (Set.Ioo t (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' (f := fun z => |deriv g z|)
      ((hF1int.add hSint).div_const 2)
      (hcont2.aestronglyMeasurable measurableSet_Ioo) (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
        rw [Real.norm_eq_abs, abs_abs]
        exact hpoint z hz)
  have hmono := MeasureTheory.setIntegral_mono_on hgint ((hF1int.add hSint).div_const 2)
    measurableSet_Ioo hpoint
  have hsplit : (∫ z in Set.Ioo t (Real.pi / 2),
        ((deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η) + (Real.sin (2 * z)) ^ η) / 2)
      = ((∫ z in Set.Ioo t (Real.pi / 2),
            (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
          + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hF1int hSint]
  have hL1 : ∫ z in Set.Ioo t (Real.pi / 2), |deriv g z| ≤
      ((∫ z in Set.Ioo t (Real.pi / 2),
          (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
    rw [← hsplit]
    exact hmono
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm]
    refine (abs_sub_le_intervalIntegral_deriv hg (lt_trans ht hx.1) hxy hy.2).trans ?_
    rw [intervalIntegral.integral_of_le hxy, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact (MeasureTheory.setIntegral_mono_set hgint
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun z (hz : z ∈ Set.Ioo x y) =>
        ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩)).trans hL1
  · refine (abs_sub_le_intervalIntegral_deriv (a := y) (b := x) hg (lt_trans ht hy.1) hyx
      hx.2).trans ?_
    rw [intervalIntegral.integral_of_le hyx, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact (MeasureTheory.setIntegral_mono_set hgint
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun z (hz : z ∈ Set.Ioo y x) =>
        ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hx.2⟩)).trans hL1

theorem tendsto_zero_of_deriv_sq_integrable {η γ : ℝ} (hη : 0 ≤ η) (hγ : 1 < γ)
    {g : ℝ → ℝ} {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
      (Set.Ioo t (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ δ > 0, ∀ x : ℝ, x ∈ Set.Iio (Real.pi / 2) →
      dist x (Real.pi / 2) < δ → dist (g x) 0 < ε := by
    intro ε hε hε1
    -- a short tail on which the weighted derivative integral is small
    obtain ⟨t', ht', ht'len, ht'U⟩ := exists_tail_le
      (F := fun θ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) h2
      (a := ε ^ 2 / 16) (ε := ε ^ 2 / 8) (by positivity) (by positivity)
    have ht'V : ∫ z in Set.Ioo t' (Real.pi / 2), (Real.sin (2 * z)) ^ η ≤ ε ^ 2 / 8 :=
      (setIntegral_sin_two_rpow_le_length hη ht'.1.le ht'.2.le).trans
        (by nlinarith [ht'len, hε])
    have hF'int : MeasureTheory.IntegrableOn
        (fun z => (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        (Set.Ioo t' (Real.pi / 2)) := h2.mono_set (Set.Ioo_subset_Ioo_left ht'.1.le)
    have hS'int : MeasureTheory.IntegrableOn (fun z => (Real.sin (2 * z)) ^ η)
        (Set.Ioo t' (Real.pi / 2)) := integrableOn_sin_two_rpow hη ht'.1.le
    have hF'nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo t' (Real.pi / 2))]
        (fun z => (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt
        (sin_two_pos_of_mem_Ioo ⟨lt_trans ht'.1 hz.1, hz.2⟩)) _)
    have hS'nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo t' (Real.pi / 2))]
        (fun z => (Real.sin (2 * z)) ^ η) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      exact Real.rpow_nonneg (le_of_lt
        (sin_two_pos_of_mem_Ioo ⟨lt_trans ht'.1 hz.1, hz.2⟩)) _
    -- shrink the tail so that it also sits inside `(t, π/2)`, where `h1` lives
    set t'' : ℝ := max t t' with ht''def
    have ht''1 : 0 < t'' := lt_of_lt_of_le ht.1 (le_max_left t t')
    have ht''2 : t'' < Real.pi / 2 := max_lt ht.2 ht'.2
    have ht''mem : t'' ∈ Set.Ioo 0 (Real.pi / 2) := ⟨ht''1, ht''2⟩
    have hsub'' : Set.Ioo t'' (Real.pi / 2) ⊆ Set.Ioo t' (Real.pi / 2) :=
      Set.Ioo_subset_Ioo_left (le_max_right t t')
    have hU'' : ∫ z in Set.Ioo t'' (Real.pi / 2),
        (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η) ≤ ε ^ 2 / 8 :=
      (MeasureTheory.setIntegral_mono_set hF'int hF'nonneg
        (Filter.Eventually.of_forall fun _ hz => hsub'' hz)).trans ht'U
    have hV'' : ∫ z in Set.Ioo t'' (Real.pi / 2), (Real.sin (2 * z)) ^ η ≤ ε ^ 2 / 8 :=
      (MeasureTheory.setIntegral_mono_set hS'int hS'nonneg
        (Filter.Eventually.of_forall fun _ hz => hsub'' hz)).trans ht'V
    -- a point of the tail where `g` is small
    obtain ⟨τ, hτ, hτle⟩ := exists_abs_le_of_integrable_weighted hγ (f := g)
      (t := t'') ht''mem (h1.mono_set (Set.Ioo_subset_Ioo_left (le_max_left t t')))
      (d := ε / 2) (by positivity)
    refine ⟨Real.pi / 2 - t'', by linarith, fun x hx hdx => ?_⟩
    have hxt : x ∈ Set.Ioo t'' (Real.pi / 2) := by
      rw [Real.dist_eq] at hdx
      rw [abs_lt] at hdx
      exact ⟨by linarith [hdx.1], hx⟩
    have hvar := abs_sub_le_half_weights_deriv_aux (t := t'') hη hg h2 ht''1 hxt hτ
    have hbound : ((∫ z in Set.Ioo t'' (Real.pi / 2),
          (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t'' (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 ≤ ε ^ 2 / 8 := by
      linarith
    have htri : |g x| ≤ |g x - g τ| + |g τ| := by
      have h := abs_add_le (g x - g τ) (g τ)
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
