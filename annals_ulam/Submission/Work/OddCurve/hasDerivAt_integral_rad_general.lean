import Mathlib
import Submission.Work.OddCurve.Defs
import Submission.Work.OddCurve.abs_rad_phi_sub_le

/-!
# Differentiating the odd-case moment integrand in the cutting slope, without positivity

Same as `Submission.Work.OddCurve.hasDerivAt_integral_rad`, but the hypothesis that the radicand
`rad h f u t` be positive on the section is **dropped**: the pointwise derivative of
`u ↦ rad h f u t ^ n * √(rad h f u t)` at `u = s` exists for *every* value of the radicand when
`1 ≤ n` (the zero set of `√` is harmless because the exponent `n ≥ 1` gives a vanishing
difference quotient there), and the dominating bound is the global Lipschitz estimate
`Work.OddCurve.abs_rad_phi_sub_le`, which needs no sign information.

This is the form needed when the integration interval `[a,b]` is strictly larger than the cut
section `(-(x s), y s)`: there the radicand is non-positive on a set of positive measure
(`Work.OddCurve.rad_nonpos_outside`), so no positivity hypothesis is available.

The proof is the one of `Work.OddCurve.hasDerivAt_integral_rad`, verbatim; that proof never used
the positivity hypothesis.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

/-! ## The one-variable facts -/

/-- `d/dx (x ^ n * √x) = (n + 1/2) * x ^ (n-1) * √x` for `1 ≤ n`, on all of `ℝ`
(Lean's `√x = 0` for `x ≤ 0`).  At `x = 0` the increment quotient is `x ^ (n-1) * √x`, which tends
to `0` precisely because `1 ≤ n`. -/
private lemma hasDerivAt_pow_mul_sqrt {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ n * Real.sqrt y)
      (((n : ℝ) + 1 / 2) * (x ^ (n - 1) * Real.sqrt x)) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- `x < 0`: the function vanishes on a neighbourhood.
    have hev : (fun y : ℝ => y ^ n * Real.sqrt y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      rw [Real.sqrt_eq_zero_of_nonpos hy.le, mul_zero]
    have h0 : ((n : ℝ) + 1 / 2) * (x ^ (n - 1) * Real.sqrt x) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos hx.le, mul_zero, mul_zero]
    rw [h0]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · -- `x = 0`: the increment quotient is `x ^ (n-1) * √x → 0`.
    subst hx
    rw [show ((n : ℝ) + 1 / 2) * ((0 : ℝ) ^ (n - 1) * Real.sqrt 0) = 0 by simp]
    rw [hasDerivAt_iff_tendsto_slope]
    have hcont : Continuous (fun y : ℝ => y ^ (n - 1) * Real.sqrt y) :=
      (continuous_id.pow _).mul Real.continuous_sqrt
    have hlim : Tendsto (fun y : ℝ => y ^ (n - 1) * Real.sqrt y) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    refine Tendsto.congr' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := by simpa using hy
    have hyn : y ^ n = y ^ (n - 1) * y := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [pow_succ]
    simp only [zero_pow (by omega : n ≠ 0), Real.sqrt_zero, mul_zero, sub_zero,
      smul_eq_mul, slope, vsub_eq_sub]
    rw [hyn]
    field_simp
  · -- `x > 0`: product rule.
    have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt y) (1 / (2 * Real.sqrt x)) x :=
      Real.hasDerivAt_sqrt (ne_of_gt hx)
    have hprod := (hasDerivAt_pow n x).mul hsqrt
    refine hprod.congr_deriv ?_
    have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    have hxn : x ^ n = x ^ (n - 1) * x := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [pow_succ]
    field_simp
    rw [hxn, hs2]
    ring

/-- Chain rule in the second variable:
`d/dψ ((y ^ 2 - ψ ^ 2) ^ n * √(y ^ 2 - ψ ^ 2)) = -(2n+1) ψ (y ^ 2 - ψ ^ 2) ^ (n-1) √(y ^ 2 - ψ ^ 2)`,
for every `y ψ : ℝ` — no sign restriction on the radicand. -/
private lemma hasDerivAt_rad_phi {n : ℕ} (hn : 1 ≤ n) (y φ : ℝ) :
    HasDerivAt (fun ψ : ℝ => (y ^ 2 - ψ ^ 2) ^ n * Real.sqrt (y ^ 2 - ψ ^ 2))
      (-(2 * (n : ℝ) + 1) * φ * (y ^ 2 - φ ^ 2) ^ (n - 1) * Real.sqrt (y ^ 2 - φ ^ 2)) φ := by
  have hinner : HasDerivAt (fun ψ : ℝ => y ^ 2 - ψ ^ 2) (-(2 * φ)) φ := by
    have h1 := (hasDerivAt_const φ (y ^ 2)).sub (hasDerivAt_pow 2 φ)
    refine h1.congr_deriv ?_
    ring
  refine ((hasDerivAt_pow_mul_sqrt hn (y ^ 2 - φ ^ 2)).comp φ hinner).congr_deriv ?_
  ring

/-- The pointwise derivative in the slope variable at the base point `s`:
`d/du (rad h f u t ^ n * √(rad h f u t))` at `u = s` equals
`-(2n+1) (s t + h s) (t + h' s) rad h f s t ^ (n-1) √(rad h f s t)`.

No positivity of the radicand is assumed: at `rad h f s t ≤ 0` both the function and the claimed
derivative vanish. -/
private lemma hasDerivAt_rad_at_s {n : ℕ} (hn : 1 ≤ n) {h f : ℝ → ℝ} {s t : ℝ}
    (hh : DifferentiableAt ℝ h s) :
    HasDerivAt (fun u : ℝ => Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t))
      (-(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h f s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h f s t)) s := by
  have hlin : HasDerivAt (fun u : ℝ => u * t + h u) (t + deriv h s) s := by
    have h1 := ((hasDerivAt_id s).mul_const t).add (hh.hasDerivAt)
    rw [one_mul] at h1
    exact h1
  have hrad : HasDerivAt (fun u : ℝ => Work.OddCurve.rad h f u t)
      (-(2 * (s * t + h s) * (t + deriv h s))) s := by
    have houter : HasDerivAt (fun y : ℝ => f t ^ 2 - y ^ 2) (-(2 * (s * t + h s))) (s * t + h s) := by
      have h1 := (hasDerivAt_const (s * t + h s) (f t ^ 2)).sub (hasDerivAt_pow 2 (s * t + h s))
      refine h1.congr_deriv ?_
      ring
    refine (houter.comp s hlin).congr_deriv ?_
    ring
  refine ((hasDerivAt_pow_mul_sqrt hn (Work.OddCurve.rad h f s t)).comp s hrad).congr_deriv ?_
  ring

/-! ## Differentiation under the integral sign with a one-point bound -/

/-- Parametric interval integral with a **difference-quotient bound at the base point only**:
if the difference quotients `(F u t - F s t) / (u - s)` are dominated, uniformly in `t` on
`(a, b]`, by the `t`-integrable function `bound`, and converge pointwise to `F' s t`, then
`u ↦ ∫ t in a..b, F u t` is differentiable at `s` with derivative `∫ t in a..b, F' s t`.

This is the version of the Leibniz rule needed for kernels whose derivative in the parameter is not
controlled uniformly near the base point; it follows from dominated convergence. -/
private lemma hasDerivAt_integral_of_quot_bound {F F' : ℝ → ℝ → ℝ} {a b : ℝ} {bound : ℝ → ℝ}
    {s : ℝ} (hab : a ≤ b)
    (hF_int : IntervalIntegrable (F s) volume a b)
    (hF_int_near : ∀ᶠ u in 𝓝[≠] s, IntervalIntegrable (F u) volume a b)
    (hF_meas : ∀ᶠ u in 𝓝[≠] s, AEStronglyMeasurable
      (fun t : ℝ => (F u t - F s t) / (u - s)) (volume.restrict (Set.uIoc a b)))
    (hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc a b)))
    (h_bound : ∀ᶠ u in 𝓝[≠] s, ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      ‖(F u t - F s t) / (u - s)‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound volume a b)
    (h_lim : ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      Tendsto (fun u : ℝ => (F u t - F s t) / (u - s)) (𝓝[≠] s) (𝓝 (F' s t))) :
    HasDerivAt (fun u : ℝ => ∫ t in a..b, F u t) (∫ t in a..b, F' s t) s := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hbound_int : Integrable bound (volume.restrict (Set.uIoc a b)) := by
    have h0 : IntegrableOn bound (Set.Ioc a b) volume := bound_integrable.1
    rw [Set.uIoc_of_le hab]
    exact h0.integrable
  have h_tend_int := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (ι := ℝ) (l := 𝓝[≠] s)
    (F := fun u t => (F u t - F s t) / (u - s))
    (f := F' s) (bound := bound) hF_meas h_bound hbound_int h_lim
  have h_slope_eq : slope (fun u : ℝ => ∫ t in a..b, F u t) s =ᶠ[𝓝[≠] s]
      (fun u : ℝ => ∫ t in a..b, (F u t - F s t) / (u - s)) := by
    filter_upwards [self_mem_nhdsWithin, hF_int_near] with u hu hu_int
    have hu_ne : u ≠ s := by simpa [Set.mem_compl_singleton_iff] using hu
    have hsub : (∫ t in a..b, F u t) - ∫ t in a..b, F s t = ∫ t in a..b, (F u t - F s t) :=
      (intervalIntegral.integral_sub hu_int hF_int).symm
    change (u - s)⁻¹ • ((∫ t in a..b, F u t) - ∫ t in a..b, F s t) =
      ∫ t in a..b, (F u t - F s t) / (u - s)
    rw [hsub]
    have hdiv : (u - s)⁻¹ • (∫ t in a..b, F u t - F s t) =
        (∫ t in a..b, F u t - F s t) / (u - s) := by
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [hdiv, ← intervalIntegral.integral_div (u - s)]
  have hmain : Tendsto (fun u : ℝ => ∫ t in a..b, (F u t - F s t) / (u - s))
      (𝓝[≠] s) (𝓝 (∫ t in a..b, F' s t)) := by
    simpa [Set.uIoc_of_le hab, intervalIntegral.integral_of_le hab] using h_tend_int
  exact (tendsto_congr' h_slope_eq).mpr hmain

/-! ## The statement -/

theorem hasDerivAt_integral_rad_general {n : ℕ} (hn : 1 ≤ n) {h f : ℝ → ℝ} {a b s : ℝ}
    (hab : a ≤ b) (hh : ∀ᶠ u in nhds s, DifferentiableAt ℝ h u) (hf : Continuous f) :
    HasDerivAt (fun u : ℝ => ∫ t in a..b,
        Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t))
      (∫ t in a..b, -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h f s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h f s t)) s := by
  -- `h` is differentiable at `s` itself (differentiability on a neighbourhood is a local property).
  have hds : DifferentiableAt ℝ h s :=
    DifferentiableOn.differentiableAt (fun u hu => hu.differentiableWithinAt) hh
  -- Differentiability at `s` gives the linear bound `|h u - h s| ≤ K |u - s|` near `s`.
  obtain ⟨K, δ, hK0, hδpos, hKlip⟩ :
      ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ u : ℝ, |u - s| < δ → |h u - h s| ≤ K * |u - s| := by
    have hslope : Tendsto (slope h s) (𝓝[≠] s) (𝓝 (deriv h s)) := hds.hasDerivAt.tendsto_slope
    have h1 : ∀ᶠ u in 𝓝[≠] s, |slope h s u| ≤ |deriv h s| + 1 := by
      filter_upwards [hslope.eventually (Metric.ball_mem_nhds (deriv h s) one_pos)] with u hu
      have hlt : |slope h s u - deriv h s| < 1 := by simpa [Real.dist_eq] using hu
      have h3 : |slope h s u| ≤ |slope h s u - deriv h s| + |deriv h s| := by
        have := abs_add_le (slope h s u - deriv h s) (deriv h s)
        rwa [sub_add_cancel] at this
      linarith
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨|deriv h s| + 1, δ, by positivity, hδpos, fun u hu => ?_⟩
    have hdist : dist u s < δ := by rw [Real.dist_eq]; exact hu
    by_cases hne : u = s
    · subst hne
      simp
    · have hsl : |slope h s u| ≤ |deriv h s| + 1 := hδ hdist (by simpa using hne)
      have hsu : slope h s u * (u - s) = h u - h s := by
        rw [slope_def_field]
        field_simp
      calc |h u - h s| = |slope h s u * (u - s)| := by rw [hsu]
        _ = |slope h s u| * |u - s| := abs_mul _ _
        _ ≤ (|deriv h s| + 1) * |u - s| := mul_le_mul_of_nonneg_right hsl (abs_nonneg _)
  -- A bound `M` for `|f|` on `[a, b]`.
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ t ∈ Set.Icc a b, |f t| ≤ M := by
    obtain ⟨t₀, -, ht₀max⟩ :=
      isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf.continuousOn.abs
    exact ⟨max 1 |f t₀|, le_max_left _ _, fun t ht => (ht₀max ht).trans (le_max_right _ _)⟩
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  -- The dominating constant.
  set Cb : ℝ := (2 * (n : ℝ) + 1) * M ^ (2 * n) * (max |a| |b| + K) with hCbdef
  have hCb0 : 0 ≤ Cb := by
    have h1 : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) ≤ M ^ (2 * n) := by positivity
    have h3 : (0 : ℝ) ≤ max |a| |b| + K := by
      have := abs_nonneg a
      have := abs_nonneg b
      positivity
    rw [hCbdef]
    positivity
  -- Apply the parametric lemma.
  refine hasDerivAt_integral_of_quot_bound
    (F := fun u t => Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t))
    (F' := fun _ t => -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
      Work.OddCurve.rad h f s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h f s t))
    (bound := fun _ => Cb) hab ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- integrability of the integrand at `u = s`
    have hcont : Continuous
        (fun t : ℝ => Work.OddCurve.rad h f s t ^ n * Real.sqrt (Work.OddCurve.rad h f s t)) := by
      unfold Work.OddCurve.rad
      fun_prop
    exact (hcont.continuousOn.mono (Set.subset_univ _)).intervalIntegrable
  · -- integrability of the integrand for `u` near `s`
    refine Eventually.of_forall fun u => ?_
    have hcont : Continuous
        (fun t : ℝ => Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t)) := by
      unfold Work.OddCurve.rad
      fun_prop
    exact (hcont.continuousOn.mono (Set.subset_univ _)).intervalIntegrable
  · -- measurability of the difference quotients
    refine Eventually.of_forall fun u => ?_
    have hcont : Continuous (fun t : ℝ =>
        (Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t) -
          Work.OddCurve.rad h f s t ^ n * Real.sqrt (Work.OddCurve.rad h f s t)) / (u - s)) := by
      unfold Work.OddCurve.rad
      fun_prop
    exact hcont.aestronglyMeasurable
  · -- measurability of the derivative
    have hcont : Continuous (fun t : ℝ => -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h f s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h f s t)) := by
      unfold Work.OddCurve.rad
      fun_prop
    exact hcont.aestronglyMeasurable
  · -- the uniform difference-quotient bound
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds s hδpos] with u hu1
    intro hne
    have hu1' : |u - s| < δ := by rw [Metric.mem_ball, Real.dist_eq] at hu1; exact hu1
    have hhu : |h u - h s| ≤ K * |u - s| := hKlip u hu1'
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le hab] at ht
    have htIcc : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, ht.2⟩
    have htle : |t| ≤ max |a| |b| := by
      rcases le_total 0 t with h0 | h0
      · rw [abs_of_nonneg h0]
        exact ht.2.trans (le_trans (le_abs_self b) (le_max_right _ _))
      · rw [abs_of_nonpos h0]
        exact (by linarith [ht.1] : -t ≤ -a).trans
          (le_trans (neg_le_abs a) (le_max_left _ _))
    have hphi := abs_rad_phi_sub_le (n := n) hn (M := M) hM0 (hM t htIcc)
      (φ₁ := u * t + h u) (φ₂ := s * t + h s)
    have hdiff : |(u * t + h u) - (s * t + h s)| ≤ (max |a| |b| + K) * |u - s| := by
      have h1 : (u * t + h u) - (s * t + h s) = (u - s) * t + (h u - h s) := by ring
      calc |(u * t + h u) - (s * t + h s)| = |(u - s) * t + (h u - h s)| := by rw [h1]
        _ ≤ |(u - s) * t| + |h u - h s| := abs_add_le _ _
        _ = |u - s| * |t| + |h u - h s| := by rw [abs_mul]
        _ ≤ |u - s| * max |a| |b| + K * |u - s| :=
            add_le_add (mul_le_mul_of_nonneg_left htle (abs_nonneg _)) hhu
        _ = (max |a| |b| + K) * |u - s| := by ring
    have hmain : |Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t) -
        Work.OddCurve.rad h f s t ^ n * Real.sqrt (Work.OddCurve.rad h f s t)|
        ≤ Cb * |u - s| := by
      have hshape : Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t) -
          Work.OddCurve.rad h f s t ^ n * Real.sqrt (Work.OddCurve.rad h f s t) =
          (f t ^ 2 - (u * t + h u) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (u * t + h u) ^ 2) -
            (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) := by
        simp only [Work.OddCurve.rad_def]
      rw [hshape]
      calc |(f t ^ 2 - (u * t + h u) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (u * t + h u) ^ 2) -
            (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)|
          ≤ (2 * (n : ℝ) + 1) * M ^ (2 * n) * |(u * t + h u) - (s * t + h s)| := hphi
        _ ≤ (2 * (n : ℝ) + 1) * M ^ (2 * n) * ((max |a| |b| + K) * |u - s|) := by
            exact mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = Cb * |u - s| := by rw [hCbdef]; ring
    rw [Real.norm_eq_abs, abs_div]
    rw [div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hne))]
    exact hmain
  · -- integrability of the constant bound
    exact intervalIntegrable_const
  · -- pointwise convergence of the difference quotients
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    have hD := hasDerivAt_rad_at_s (h := h) (f := f) (s := s) (t := t) hn hds
    have hslope := hasDerivAt_iff_tendsto_slope.mp hD
    have heq : slope (fun u : ℝ =>
          Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t)) s =ᶠ[𝓝[≠] s]
        (fun u : ℝ => (Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t) -
          Work.OddCurve.rad h f s t ^ n * Real.sqrt (Work.OddCurve.rad h f s t)) / (u - s)) := by
      filter_upwards with u
      rw [slope_def_field]
    exact Tendsto.congr' heq hslope

end

end Work.OddCurve
