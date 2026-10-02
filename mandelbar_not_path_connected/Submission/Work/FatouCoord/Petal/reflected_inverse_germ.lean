/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Reflecting a parabolic germ through the origin

Let `f z = z + z ^ 2 * h z` be a parabolic germ of multiplicity one at `0`, with the
quantitative hypotheses of `ParabolicBounds f h a r A A'` (so `h 0 = 1`, `h z = 1 + a * z + O(z^2)`
and `h`, `h'` are bounded on the disc of radius `r`).  Write `finv` for the local inverse of `f`
at `0` and put

`F u = - finv (-u)`.

Then `finv (f z) = z` and `f (finv z) = z` for `z` in a small disc, and `F` is again a parabolic
germ of multiplicity one, with parameter `2 - a`: writing `f z = z + z ^ 2 + a z^3 + O(z^4)` we
have `finv w = w - w ^ 2 + (2 - a) w ^ 3 + O(w ^ 4)`, so `F u = u + u ^ 2 - (2 - a) u ^ 3 + … `  In
other words the reflection `u ↦ -finv (-u)` realises the reversion `a ↦ 2 - a` on the parameter;
this is the local germ statement underlying the reversible structure of the Fatou coordinate
of an antiholomorphic parabolic germ.

## Main result

* `Work.FatouCoord.Petal.reflected_inverse_germ`
-/

open scoped Topology
open Set Filter Metric

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Petal

noncomputable section

variable {f h F : ℂ → ℂ} {a b : ℂ} {r A A' : ℝ}

/-! ## Elementary consequences of the quantitative hypotheses -/

/-- The normalisation `h 0 = 1` is implied by the second order expansion of `h`. -/
lemma parabolic_h_zero (hb : ParabolicBounds f h a r A A') : h 0 = 1 := by
  have hc : ‖h 0 - 1‖ ≤ 0 := by simpa using hb.h_close 0 (by simpa using hb.hr)
  have h1 : ‖h 0 - 1‖ = 0 := le_antisymm hc (norm_nonneg _)
  simpa using sub_eq_zero.mp (norm_eq_zero.mp h1)

/-- The parabolic fixed point: `f 0 = 0`. -/
lemma parabolic_f_zero (hb : ParabolicBounds f h a r A A') : f 0 = 0 := by
  rw [hb.f_eq 0 (by simpa using hb.hr)]
  ring

/-- `h` is analytic at the origin. -/
lemma parabolic_analyticAt_h (hb : ParabolicBounds f h a r A A') : AnalyticAt ℂ h 0 :=
  hb.h_diff.analyticAt (ball_mem_nhds 0 hb.hr)

/-- The parameter `a` is the derivative of `h` at the origin. -/
lemma parabolic_deriv_h_zero (hb : ParabolicBounds f h a r A A') : deriv h 0 = a := by
  have hh0 : h 0 = 1 := parabolic_h_zero hb
  have hbound : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖(h z - 1 - a * z) / z‖ ≤ A * ‖z‖ := by
    have hball : ball (0 : ℂ) r ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds (ball_mem_nhds 0 hb.hr)
    filter_upwards [hball] with z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hz0)]
      have hc := hb.h_close z hz
      have hmul : A * ‖z‖ * ‖z‖ = A * ‖z‖ ^ 2 := by ring
      linarith [hc, hmul]
  have htend : Tendsto (fun z : ℂ => ‖(h z - 1 - a * z) / z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) hbound ?_
    have h2 : Tendsto (fun z : ℂ => A * ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 (A * ‖(0 : ℂ)‖)) :=
      (continuous_const.mul continuous_norm).continuousAt.continuousWithinAt
    simpa using h2
  have htend2 : Tendsto (fun z : ℂ => (h z - 1 - a * z) / z) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr htend
  have hslope : Tendsto (slope h 0) (𝓝[≠] (0 : ℂ)) (𝓝 a) := by
    have h1 : Tendsto (fun z : ℂ => a + (h z - 1 - a * z) / z) (𝓝[≠] (0 : ℂ)) (𝓝 a) := by
      simpa using tendsto_const_nhds.add htend2
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    rw [slope_def_field, hh0]
    field_simp
    ring
  exact (hasDerivAt_iff_tendsto_slope.mpr hslope).deriv

/-- `f` is analytic at the origin. -/
lemma parabolic_analyticAt_f (hb : ParabolicBounds f h a r A A') : AnalyticAt ℂ f 0 := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => z + z ^ 2 * h z) 0 := by
    have hh := parabolic_analyticAt_h hb
    fun_prop
  refine h1.congr ?_
  filter_upwards [ball_mem_nhds 0 hb.hr] with z hz
  exact (hb.f_eq z hz).symm

/-- The derivative of `f` at the parabolic fixed point is `1`. -/
lemma parabolic_deriv_f_zero (hb : ParabolicBounds f h a r A A') : deriv f 0 = 1 := by
  have hh0 : h 0 = 1 := parabolic_h_zero hb
  have hfe : f =ᶠ[𝓝 (0 : ℂ)] fun z : ℂ => z + z ^ 2 * h z := by
    filter_upwards [ball_mem_nhds 0 hb.hr] with z hz
    exact hb.f_eq z hz
  rw [hfe.deriv_eq]
  change deriv ((id : ℂ → ℂ) + (id : ℂ → ℂ) ^ 2 * h) 0 = 1
  rw [deriv_add differentiableAt_id ((differentiableAt_id.pow 2).mul
    (parabolic_analyticAt_h hb).differentiableAt)]
  rw [deriv_mul (differentiableAt_id.pow 2) (parabolic_analyticAt_h hb).differentiableAt]
  rw [deriv_pow differentiableAt_id 2]
  simp [hh0]

/-- The second derivative of `f` at the origin. -/
lemma parabolic_iteratedDeriv_two (hb : ParabolicBounds f h a r A A') :
    iteratedDeriv 2 f 0 = 2 := by
  have hh0 : h 0 = 1 := parabolic_h_zero hb
  have hh_an : AnalyticAt ℂ h 0 := parabolic_analyticAt_h hb
  have hfe : f =ᶠ[𝓝 (0 : ℂ)] fun z : ℂ => z + z ^ 2 * h z := by
    filter_upwards [ball_mem_nhds 0 hb.hr] with z hz
    exact hb.f_eq z hz
  rw [EventuallyEq.iteratedDeriv_eq 2 hfe]
  change iteratedDeriv 2 ((fun z : ℂ => z) + (fun z : ℂ => z ^ 2 * h z)) 0 = 2
  rw [iteratedDeriv_add (f := fun z : ℂ => z) (g := fun z : ℂ => z ^ 2 * h z)]
  · change iteratedDeriv 2 (fun z : ℂ => z) 0 + iteratedDeriv 2 ((fun z : ℂ => z ^ 2) * h) 0 = 2
    rw [iteratedDeriv_mul (f := fun z : ℂ => z ^ 2) (g := h)]
    · norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
        iteratedDeriv_fun_id_zero, hh0]
    · fun_prop
    · exact hh_an.contDiffAt
  · fun_prop
  · exact ContDiffAt.mul (by fun_prop) hh_an.contDiffAt

/-- The third derivative of `f` at the origin, in terms of the parameter `a`. -/
lemma parabolic_iteratedDeriv_three (hb : ParabolicBounds f h a r A A') :
    iteratedDeriv 3 f 0 = 6 * a := by
  have hh0 : h 0 = 1 := parabolic_h_zero hb
  have hh_an : AnalyticAt ℂ h 0 := parabolic_analyticAt_h hb
  have hde : deriv h 0 = a := parabolic_deriv_h_zero hb
  have hfe : f =ᶠ[𝓝 (0 : ℂ)] fun z : ℂ => z + z ^ 2 * h z := by
    filter_upwards [ball_mem_nhds 0 hb.hr] with z hz
    exact hb.f_eq z hz
  rw [EventuallyEq.iteratedDeriv_eq 3 hfe]
  change iteratedDeriv 3 ((fun z : ℂ => z) + (fun z : ℂ => z ^ 2 * h z)) 0 = 6 * a
  rw [iteratedDeriv_add (f := fun z : ℂ => z) (g := fun z : ℂ => z ^ 2 * h z)]
  · change iteratedDeriv 3 (fun z : ℂ => z) 0 + iteratedDeriv 3 ((fun z : ℂ => z ^ 2) * h) 0
      = 6 * a
    rw [iteratedDeriv_mul (f := fun z : ℂ => z ^ 2) (g := h)]
    · norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
        iteratedDeriv_fun_id_zero, hh0, hde]
    · fun_prop
    · exact hh_an.contDiffAt
  · fun_prop
  · exact ContDiffAt.mul (by fun_prop) hh_an.contDiffAt

/-! ## The local inverse of the germ -/

/-- The local inverse `G` of a parabolic germ at `0` is again a parabolic germ: `G 0 = 0`,
`G' 0 = 1`, `G'' 0 = -2` and `G''' 0 = 12 - 6 a`.  Moreover `G` is a two-sided inverse of `f`
near the origin. -/
lemma exists_local_inverse_of_parabolicBounds (hb : ParabolicBounds f h a r A A') :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧ deriv G 0 = 1 ∧
      iteratedDeriv 2 G 0 = -2 ∧ iteratedDeriv 3 G 0 = 12 - 6 * a ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), G (f z) = z) ∧ (∀ᶠ w in 𝓝 (0 : ℂ), f (G w) = w) := by
  have hf_an : AnalyticAt ℂ f 0 := parabolic_analyticAt_f hb
  have hf0 : f 0 = 0 := parabolic_f_zero hb
  have hd : deriv f 0 = 1 := parabolic_deriv_f_zero hb
  have h2 : iteratedDeriv 2 f 0 = 2 := parabolic_iteratedDeriv_two hb
  have h3 : iteratedDeriv 3 f 0 = 6 * a := parabolic_iteratedDeriv_three hb
  have hf' : deriv f 0 ≠ 0 := by rw [hd]; norm_num
  set G : ℂ → ℂ := HasStrictDerivAt.localInverse f (deriv f 0) 0 hf_an.hasStrictDerivAt hf'
    with hGdef
  have hGan : AnalyticAt ℂ G 0 := by
    rw [hGdef]; simpa [hf0] using hf_an.analyticAt_localInverse hf'
  have hG0 : G 0 = 0 := by
    have hFD := hf_an.hasStrictDerivAt.hasStrictFDerivAt_equiv hf'
    rw [hGdef]
    simpa [hf0] using hFD.localInverse_apply_image
  have hGd : deriv G 0 = 1 := by
    rw [hGdef]
    have hh := HasStrictDerivAt.hasDerivAt
      (HasStrictDerivAt.to_localInverse hf_an.hasStrictDerivAt hf')
    simpa [hf0, hd] using hh.deriv
  have hcomp : f ∘ G =ᶠ[𝓝 (0 : ℂ)] id := by
    rw [hGdef]
    have hh := HasStrictDerivAt.eventually_right_inverse hf_an.hasStrictDerivAt hf'
    rw [hf0] at hh
    exact hh
  have h2G : iteratedDeriv 2 G 0 = -2 := by
    have key : iteratedDeriv 2 (f ∘ G) 0 = 0 := by
      rw [EventuallyEq.iteratedDeriv_eq 2 hcomp, iteratedDeriv_id]; norm_num
    rw [iteratedDeriv_comp_two (f := G) (g := f) (by rw [hG0]; exact hf_an.contDiffAt)
      hGan.contDiffAt] at key
    rw [hG0, h2, hd, hGd] at key
    have hk : (2 : ℂ) + iteratedDeriv 2 G 0 = 0 := by simpa using key
    exact eq_neg_of_add_eq_zero_right hk
  have h3G : iteratedDeriv 3 G 0 = 12 - 6 * a := by
    have key : iteratedDeriv 3 (f ∘ G) 0 = 0 := by
      rw [EventuallyEq.iteratedDeriv_eq 3 hcomp, iteratedDeriv_id]; norm_num
    rw [iteratedDeriv_comp_three (f := G) (g := f) (by rw [hG0]; exact hf_an.contDiffAt)
      hGan.contDiffAt] at key
    rw [hG0, h3, h2, hd, hGd, h2G] at key
    linear_combination key
  have hleft : ∀ᶠ z in 𝓝 (0 : ℂ), G (f z) = z := by
    rw [hGdef]
    exact HasStrictDerivAt.eventually_left_inverse hf_an.hasStrictDerivAt hf'
  have hright : ∀ᶠ w in 𝓝 (0 : ℂ), f (G w) = w := by
    rw [hGdef]
    have hh := HasStrictDerivAt.eventually_right_inverse hf_an.hasStrictDerivAt hf'
    rwa [hf0] at hh
  exact ⟨G, hGan, hG0, hGd, h2G, h3G, hleft, hright⟩

/-! ## The Taylor remainder for a germ with prescribed first coefficients -/

/-- A germ analytic at `0` whose Taylor coefficients of order `1, 2, 3` are `1, 2, 6 * b`
satisfies `F u = u + u ^ 2 + u ^ 3 * R u` with `R` analytic at `0` and `R 0 = b`. -/
lemma exists_taylor_remainder {F : ℂ → ℂ} {b : ℂ} (hFan : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hF1 : iteratedDeriv 1 F 0 = 1) (hF2 : iteratedDeriv 2 F 0 = 2)
    (hF3 : iteratedDeriv 3 F 0 = 6 * b) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ (∀ u, F u = u + u ^ 2 + u ^ 3 * R u) ∧ R 0 = b := by
  obtain ⟨R, hRan, hReq⟩ := hFan.exists_eq_sum_add_pow_mul 3
  have hReq' : ∀ u, F u = u + u ^ 2 + u ^ 3 * R u := by
    intro u
    rw [hReq u]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_two, pow_zero, pow_one, pow_two, iteratedDeriv_zero, hF0, hF1, hF2,
      Nat.cast_one, Nat.cast_ofNat, div_one, one_mul, zero_mul, zero_add, smul_eq_mul]
    ring
  obtain ⟨R₄, hR₄an, hR₄eq⟩ := hFan.exists_eq_sum_add_pow_mul 4
  have hR₄eq' : ∀ u, F u = u + u ^ 2 + b * u ^ 3 + u ^ 4 * R₄ u := by
    intro u
    rw [hR₄eq u]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_two, pow_zero, pow_one, pow_two, pow_succ, iteratedDeriv_zero, hF0, hF1,
      hF2, hF3, Nat.cast_one, Nat.cast_ofNat, div_one, one_mul, zero_mul, zero_add, smul_eq_mul]
    ring
  have hR0 : R 0 = b := by
    have hev : R =ᶠ[𝓝[≠] (0 : ℂ)] fun u => b + u * R₄ u := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : u ≠ 0 := hu
      have key : u ^ 3 * R u = b * u ^ 3 + u ^ 4 * R₄ u := by
        have h1 := hReq' u
        rw [hR₄eq' u] at h1
        linear_combination -h1
      refine mul_left_cancel₀ (pow_ne_zero 3 hu0) ?_
      rw [key]
      ring
    have ht1 : Tendsto R (𝓝[≠] (0 : ℂ)) (𝓝 (R 0)) :=
      hRan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun u : ℂ => b + u * R₄ u) (𝓝[≠] (0 : ℂ)) (𝓝 (b + 0 * R₄ 0)) :=
      (tendsto_const_nhds.add (tendsto_id.mul hR₄an.continuousAt.tendsto)).mono_left
        nhdsWithin_le_nhds
    have huniq := tendsto_nhds_unique (ht1.congr' hev) ht2
    simpa using huniq
  exact ⟨R, hRan, hReq', hR0⟩

/-! ## A parabolic germ from an analytic germ -/

/-- An analytic germ with `F u = u + u ^ 2 + b u ^ 3 + O(u ^ 4)` is a parabolic germ
`F u = u + u ^ 2 * hF u`, where `hF` is analytic at `0`, `hF 0 = 1`, and
`hF u = 1 + b u + O(u ^ 2)`; moreover `hF` is bounded by `2` and its derivative is bounded on a
small disc. -/
lemma exists_parabolic_germ_bounds {F : ℂ → ℂ} {b : ℂ} (hFan : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hF1 : iteratedDeriv 1 F 0 = 1) (hF2 : iteratedDeriv 2 F 0 = 2)
    (hF3 : iteratedDeriv 3 F 0 = 6 * b) :
    ∃ (hF : ℂ → ℂ) (r' A'' A''' : ℝ), 0 < r' ∧ 0 ≤ A'' ∧ 0 ≤ A''' ∧
      (∀ u ∈ ball 0 r', F u = u + u ^ 2 * hF u) ∧
      DifferentiableOn ℂ hF (ball 0 r') ∧
      (∀ u ∈ ball 0 r', ‖hF u - 1 - b * u‖ ≤ A'' * ‖u‖ ^ 2) ∧
      (∀ u ∈ ball 0 r', ‖hF u‖ ≤ 2) ∧
      (∀ u ∈ ball 0 r', ‖deriv hF u‖ ≤ A''') := by
  obtain ⟨R, hRan, hReq, hR0⟩ := exists_taylor_remainder hFan hF0 hF1 hF2 hF3
  obtain ⟨S, hSan, hSeq⟩ := hRan.exists_eq_sum_add_pow_mul 1
  have hSeq' : ∀ u, R u = R 0 + u * S u := by
    intro u
    rw [hSeq u]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.cast_one,
      pow_zero, pow_one, iteratedDeriv_zero, div_one, one_mul, zero_add, smul_eq_mul]
  set hF : ℂ → ℂ := fun u => 1 + u * R u with hFdef
  have hF_an : AnalyticAt ℂ hF 0 := by
    rw [hFdef]
    fun_prop
  -- bounds on `S`
  have hS_bd : ∀ᶠ u in 𝓝 (0 : ℂ), ‖S u‖ ≤ ‖S 0‖ + 1 :=
    (Filter.Tendsto.eventually_lt_const (v := ‖S 0‖) (u := ‖S 0‖ + 1) (by linarith)
      hSan.continuousAt.tendsto.norm).mono fun u hu => le_of_lt hu
  -- the second order remainder of `hF`
  have hclose : ∀ᶠ u in 𝓝 (0 : ℂ),
      ‖hF u - 1 - b * u‖ ≤ max (‖S 0‖ + 1) 0 * ‖u‖ ^ 2 := by
    filter_upwards [hS_bd] with u hu
    have key : hF u - 1 - b * u = u ^ 2 * S u := by
      simp only [hFdef]
      rw [hSeq' u, hR0]
      ring
    rw [key, norm_mul, norm_pow]
    calc ‖u‖ ^ 2 * ‖S u‖ ≤ ‖u‖ ^ 2 * (‖S 0‖ + 1) :=
          mul_le_mul_of_nonneg_left hu (sq_nonneg ‖u‖)
      _ ≤ max (‖S 0‖ + 1) 0 * ‖u‖ ^ 2 := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ‖u‖)
  -- `hF` is analytic on a disc around `0`, so `deriv hF` is bounded there
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ > 0, ∀ u ∈ ball 0 ρ, AnalyticAt ℂ hF u := by
    have hh := hF_an.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hh
    obtain ⟨ε, hε, h'⟩ := hh
    exact ⟨ε, hε, fun u hu => h' (mem_ball.mp hu)⟩
  have hρ_ev : ∀ᶠ u in 𝓝 (0 : ℂ), DifferentiableAt ℂ hF u :=
    hF_an.eventually_analyticAt.mono fun u hu => hu.differentiableAt
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ u in 𝓝 (0 : ℂ), ‖deriv hF u‖ ≤ C := by
    have hcont : ContinuousOn (deriv hF) (closedBall 0 (ρ / 2)) := by
      intro u hu
      have huρ : u ∈ ball 0 ρ := by
        rw [mem_closedBall_zero_iff] at hu
        rw [mem_ball_zero_iff]
        linarith
      exact ((hρ u huρ).deriv).continuousAt.continuousWithinAt
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn hcont
    exact ⟨C, by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (by linarith : 0 < ρ / 2)] with u hu
      exact hC u hu⟩
  have hC' : ∀ᶠ u in 𝓝 (0 : ℂ), ‖deriv hF u‖ ≤ max C 0 :=
    hC.mono fun u hu => le_trans hu (le_max_left _ _)
  -- `hF` is bounded by `2` near `0`
  have hbound : ∀ᶠ u in 𝓝 (0 : ℂ), ‖hF u‖ ≤ 2 := by
    have htend : Tendsto hF (𝓝 (0 : ℂ)) (𝓝 1) := by
      rw [hFdef]
      have h1 : Tendsto (fun u : ℂ => 1 + u * R u) (𝓝 (0 : ℂ)) (𝓝 (1 + 0 * R 0)) :=
        tendsto_const_nhds.add (tendsto_id.mul hRan.continuousAt.tendsto)
      simpa using h1
    exact (Filter.Tendsto.eventually_lt_const (v := ‖(1 : ℂ)‖) (u := 2) (by norm_num)
      htend.norm).mono fun u hu => le_of_lt hu
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ),
      DifferentiableAt ℂ hF u ∧ ‖hF u - 1 - b * u‖ ≤ max (‖S 0‖ + 1) 0 * ‖u‖ ^ 2 ∧
        ‖hF u‖ ≤ 2 ∧ ‖deriv hF u‖ ≤ max C 0 := by
    filter_upwards [hρ_ev, hclose, hbound, hC'] with u h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := hev
  refine ⟨hF, ε, max (‖S 0‖ + 1) 0, max C 0, hεpos, le_max_right _ _, le_max_right _ _,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro u _
    rw [hReq u, hFdef]
    ring
  · intro u hu
    exact ((hε (mem_ball.mp hu)).1).differentiableWithinAt
  · intro u hu
    exact (hε (mem_ball.mp hu)).2.1
  · intro u hu
    exact (hε (mem_ball.mp hu)).2.2.1
  · intro u hu
    exact (hε (mem_ball.mp hu)).2.2.2

/-! ## The reflected germ -/

/-- **The reflected inverse germ.**  If `f z = z + z ^ 2 * h z` is a parabolic germ of
multiplicity one at `0` with quantitative bounds, then its local inverse `finv` and the reflected
map `F u = -finv (-u)` satisfy `finv (f z) = z`, `f (finv z) = z` on a small disc and `F` is
again a parabolic germ, with parameter `2 - a`. -/
theorem reflected_inverse_germ {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ (finv F hF : ℂ → ℂ) (r' : ℝ) (A'' A''' : ℝ), ParabolicBounds F hF (2 - a) r' A'' A''' ∧ (∀ z ∈ ball 0 r', finv (f z) = z) ∧ (∀ z ∈ ball 0 r', f (finv z) = z) ∧ (∀ u ∈ ball 0 r', F u = -finv (-u)) := by
  obtain ⟨G, hGan, hG0, hGd, hG2, hG3, hGl, hGr⟩ := exists_local_inverse_of_parabolicBounds hb
  -- the reflected germ
  set F : ℂ → ℂ := fun u => -G (-u) with hFdef
  have hFan : AnalyticAt ℂ F 0 := by
    rw [hFdef]
    exact (AnalyticAt.comp (f := fun u : ℂ => -u) (x := (0 : ℂ)) (g := G)
      (by simpa using hGan) (by fun_prop)).neg
  have hF0 : F 0 = 0 := by simp [hFdef, hG0]
  have hFd : ∀ n : ℕ, iteratedDeriv n F 0 = -((-1 : ℂ) ^ n * iteratedDeriv n G 0) := by
    intro n
    rw [hFdef, iteratedDeriv_fun_neg, iteratedDeriv_comp_neg]
    simp
  have hF1 : iteratedDeriv 1 F 0 = 1 := by rw [hFd 1, iteratedDeriv_one, hGd]; norm_num
  have hF2 : iteratedDeriv 2 F 0 = 2 := by rw [hFd 2, hG2]; norm_num
  have hF3 : iteratedDeriv 3 F 0 = 12 - 6 * a := by rw [hFd 3, hG3]; ring
  obtain ⟨hF, r', A'', A''', hr', hA'', hA''', hEq, hDiff, hClose, hBound, hDeriv⟩ :=
    exists_parabolic_germ_bounds (b := 2 - a) hFan hF0 hF1 hF2 (by rw [hF3]; ring)
  -- the inverse conditions hold on a disc
  obtain ⟨δ, hδpos, hδl, hδr⟩ : ∃ δ > 0, (∀ z ∈ ball 0 δ, G (f z) = z) ∧
      (∀ z ∈ ball 0 δ, f (G z) = z) := by
    have hh : ∀ᶠ z in 𝓝 (0 : ℂ), G (f z) = z ∧ f (G z) = z := hGl.and hGr
    rw [Metric.eventually_nhds_iff] at hh
    obtain ⟨ε, hε, h'⟩ := hh
    exact ⟨ε, hε, fun z hz => (h' (mem_ball.mp hz)).1, fun z hz => (h' (mem_ball.mp hz)).2⟩
  have hsub : ball (0 : ℂ) (min r' δ) ⊆ ball 0 r' := ball_subset_ball (min_le_left _ _)
  have hsub' : ball (0 : ℂ) (min r' δ) ⊆ ball 0 δ := ball_subset_ball (min_le_right _ _)
  refine ⟨G, F, hF, min r' δ, A'', A''',
    ⟨lt_min hr' hδpos, hA'', hA''', fun z hz => hEq z (hsub hz), hDiff.mono hsub,
      fun z hz => hClose z (hsub hz), fun z hz => hBound z (hsub hz),
      fun z hz => hDeriv z (hsub hz)⟩,
    fun z hz => hδl z (hsub' hz), fun z hz => hδr z (hsub' hz), fun u _ => rfl⟩

end

end Work.FatouCoord.Petal
