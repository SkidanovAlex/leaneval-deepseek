import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals
import Submission.Commons.Geometry.Ulam.ball_cap_first_moment_eq
import Submission.Work.OddCaps.odd_moment_integral_hasDerivAt_smooth
import Submission.Work.OddCaps.odd_cap_volume_hasDerivAt_smooth
import Submission.Work.OddCaps.smooth_basic
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_volume_half_of_interval
import Submission.Commons.Geometry.Ulam.odd_floating_of_family
import Submission.Commons.Geometry.Ulam.cap_slice_hasDerivAt

/-!
# The odd cap centroid-span identity, with smooth (not analytic) regularity

This is a copy of `Submission/Commons/Geometry/Ulam/odd_profile_cap_centroid_span.lean` in which the
analytic regularity hypothesis `ContDiffOn ℝ (⊤ : WithTop ℕ∞)` (`ω`) on the profile `f` and on the
offset function `h` has been replaced by the *smooth* hypothesis `ContDiffOn ℝ ∞`
(`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` under `open scoped ContDiff`, the smooth level of `ℕ∞ω`).

The odd profile produced by the constructive part of the proof of Ulam's problem 19 is only smooth,
never analytic, so the analytic statement in the commons is unusable by the consumer; the statement
below is the one that can be applied.  Nothing else was changed: the proof steps that used the
analytic hypothesis only need continuity / differentiability of `h` and of `deriv h`, all of which
follow from smoothness, so the proofs go through verbatim.

Main result: `Work.OddCaps.odd_cap_centroid_span` (conclusion and the `hvol` hypothesis phrased
with `Commons.Geometry.Ulam.lastFin d`; this is the same index as `⟨d - 1, by omega⟩` used in the
commons copy).
-/

namespace Work.OddCaps

open Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

private lemma mem_span_e0_elast {d : ℕ} [NeZero d] (hd : 2 ≤ d) (s lam : ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (h0 : v 0 = -s * lam) (hlast : v (lastFin d) = lam)
    (hmiddle : ∀ i, i ≠ 0 → i ≠ lastFin d → v i = 0) :
    v ∈ ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) + (EuclideanSpace.single (lastFin d) (1:ℝ))) := by
  have hlast_ne : lastFin d ≠ 0 := by
    dsimp [lastFin]
    exact Fin.ne_of_val_ne (by simp; omega)
  rw [Submodule.mem_span_singleton]
  refine ⟨lam, ?_⟩
  ext i
  change (lam • ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) + (EuclideanSpace.single (lastFin d) (1:ℝ)))).ofLp i = v.ofLp i
  by_cases hi0 : i = 0
  · subst i
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, h0]
    rw [if_neg (Ne.symm hlast_ne)]
    simp
    ring
  · by_cases hilast : i = lastFin d
    · subst i
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, hlast]
      rw [if_neg hi0]
      simp
    · have hv := hmiddle i hi0 hilast
      rw [hv]
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply]
      rw [if_neg hi0, if_neg hilast]
      simp

private lemma integral_id_apply {d : ℕ} [NeZero d] (K : Set (EuclideanSpace ℝ (Fin d))) (i : Fin d)
    (hK_meas : MeasurableSet K) (hK_bdd : Bornology.IsBounded K) :
    (∫ x in K, x) i = ∫ x in K, x i := by
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (volume.restrict K) :=
    (integrableOn_id_bounded_measurable (d := d) hK_meas hK_bdd).integrable
  have h := ContinuousLinearMap.integral_comp_comm L hInt
  simpa [L, PiLp.proj_apply] using h.symm

private lemma setAverage_id_apply {d : ℕ} [NeZero d] (K : Set (EuclideanSpace ℝ (Fin d))) (i : Fin d)
    (hK_meas : MeasurableSet K) (hK_bdd : Bornology.IsBounded K) :
    ((⨍ x in K, x) i) = ⨍ x in K, (x i) := by
  rw [setAverage_eq, setAverage_eq]
  rw [PiLp.smul_apply]
  rw [integral_id_apply K i hK_meas hK_bdd]

-- Odd centroid moment relation

private lemma hasDerivAt_const_div_sqrt_one_add_sq (C s : ℝ) :
    HasDerivAt (fun r : ℝ => C / Real.sqrt (1 + r ^ 2))
      (-(C * s) / Real.sqrt (1 + s ^ 2) ^ 3) s := by
  have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * s) s := by
    have h := (hasDerivAt_const s (1:ℝ)).add (hasDerivAt_pow 2 s)
    have hd : HasDerivAt ((fun x : ℝ => 1) + fun x : ℝ => x ^ 2) (2 * s) s := by
      simpa [show (0 : ℝ) + 2 * s ^ (2 - 1) = 2 * s by ring] using h
    exact hd.congr_of_eventuallyEq (by
      filter_upwards [] with r
      simp [Pi.add_apply])
  have hpos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  have hsqrt : HasDerivAt (fun r : ℝ => Real.sqrt (1 + r ^ 2))
      ((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) s := by
    exact h1.sqrt (ne_of_gt hpos)
  have hden_ne : Real.sqrt (1 + s ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hdiv : HasDerivAt (fun r : ℝ => C / Real.sqrt (1 + r ^ 2))
      (-(C * ((2 * s) / (2 * Real.sqrt (1 + s ^ 2)))) / (Real.sqrt (1 + s ^ 2) ^ 2)) s := by
    have hc : HasDerivAt (fun _ : ℝ => C) 0 s := hasDerivAt_const s C
    have h := HasDerivAt.div (𝕜 := ℝ) (𝕜' := ℝ) hc hsqrt hden_ne
    have hd : HasDerivAt ((fun _ : ℝ => C) / fun r : ℝ => Real.sqrt (1 + r ^ 2))
        (-(C * ((2 * s) / (2 * Real.sqrt (1 + s ^ 2)))) / (Real.sqrt (1 + s ^ 2) ^ 2)) s := by
      simpa [sub_eq_add_neg, zero_mul, zero_sub] using h
    exact hd.congr_of_eventuallyEq (by
      filter_upwards [] with r
      simp [Pi.div_apply])
  convert hdiv using 1
  have hsq_sqrt : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := by
    rw [Real.sq_sqrt (by nlinarith [sq_nonneg s])]
  field_simp [hsq_sqrt, hden_ne]

private lemma odd_pow_clamp_integral_eq_interval_of_active {n : ℕ} {f : ℝ → ℝ} {s h a b : ℝ}
    (hn : 1 ≤ n) (hs : 0 < s)
    (ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1) (hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hfa_sq : f a ^ 2 = (s * a + h) ^ 2)
    (hfb_sq : f b ^ 2 = (s * b + h) ^ 2) :
    (∫ t in (-1 : ℝ)..1,
        (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2) ^ n *
          Real.sqrt (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2)) =
      ∫ t in a..b, (f t ^ 2 - (s * t + h) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h) ^ 2) := by
  let L : ℝ → ℝ := fun t => s * t + h
  let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (L t))
  let F : ℝ → ℝ := fun t => (f t ^ 2 - (U t) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (U t) ^ 2)
  let G : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then (f t ^ 2 - (L t) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (L t) ^ 2) else 0
  have hactive := active_nonneg_outside_of_roots_inside (f := f) (s := s) (h := h) (a := a) (b := b)
    hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hFG : Set.EqOn F G (Set.Icc (-1 : ℝ) 1) := by
    intro t ht
    dsimp [F, G, U, L]
    by_cases htab : a ≤ t ∧ t ≤ b
    · have hnonneg := hactive.2 t htab
      have hL_lower : -f t ≤ s * t + h := by linarith
      have hL_upper : s * t + h ≤ f t := by linarith
      have hU : max (-f t) (min (f t) (s * t + h)) = s * t + h := by
        rw [min_eq_right hL_upper, max_eq_right hL_lower]
      rw [if_pos htab, hU]
    · have hact_false : ¬ (-f t < s * t + h ∧ s * t + h < f t) := by
        intro hact
        exact htab (hactive.1 t ht hact)
      have hU_zero : f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2 = 0 := by
        have hle_or : s * t + h ≤ -f t ∨ f t ≤ s * t + h := by
          by_contra hboth
          have hnot := not_or.mp hboth
          have hlt_lower : -f t < s * t + h := lt_of_not_ge hnot.1
          have hlt_upper : s * t + h < f t := lt_of_not_ge hnot.2
          exact hact_false ⟨hlt_lower, hlt_upper⟩
        rcases hle_or with hL_low | hL_high
        · have hmin : min (f t) (s * t + h) = s * t + h := by
            rw [min_eq_right (le_trans hL_low (by linarith [hf_nonneg t ht]))]
          have hU : max (-f t) (min (f t) (s * t + h)) = -f t := by
            rw [hmin]
            exact max_eq_left hL_low
          rw [hU]
          ring
        · have hmin : min (f t) (s * t + h) = f t := by
            rw [min_eq_left hL_high]
          have hU : max (-f t) (min (f t) (s * t + h)) = f t := by
            rw [hmin]
            exact max_eq_right (by linarith [hf_nonneg t ht])
          rw [hU]
          ring
      have hF0 : (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2) ^ n *
          Real.sqrt (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2) = 0 := by
        rw [hU_zero]
        simp
      rw [if_neg htab, hF0]
  have hF_eq_G : (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hFG
  have hab : a < b := lt_trans ha_neg hb_pos
  have hG_a : G a = 0 := by
    have htab : a ≤ a ∧ a ≤ b := ⟨le_rfl, hab.le⟩
    have hbase : f a ^ 2 - (s * a + h) ^ 2 = 0 := by rw [hfa_sq]; ring
    dsimp [G, L]
    rw [if_pos htab, hbase]
    simp
  have hG_b : G b = 0 := by
    have htab : a ≤ b ∧ b ≤ b := ⟨hab.le, le_rfl⟩
    have hbase : f b ^ 2 - (s * b + h) ^ 2 = 0 := by rw [hfb_sq]; ring
    dsimp [G, L]
    rw [if_pos htab, hbase]
    simp
  have hsuppG_m1 : Function.support G ⊆ Set.Ioc (-1 : ℝ) 1 := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : a ≤ t ∧ t ≤ b
    · have ht_gt : -1 < t := lt_of_lt_of_le ha_mem.1 htab.1
      have ht_le : t ≤ 1 := le_trans htab.2 (le_of_lt hb_mem.2)
      exact ⟨ht_gt, ht_le⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hsuppG_ab : Function.support G ⊆ Set.Ioc a b := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : a ≤ t ∧ t ≤ b
    · have hta_ne : t ≠ a := by
        intro hta
        have hG0 : G t = 0 := by
          subst t
          exact hG_a
        exact (ht hG0).elim
      have hta_lt : a < t := lt_of_le_of_ne htab.1 (Ne.symm hta_ne)
      exact ⟨hta_lt, htab.2⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := -1) (b := 1) hsuppG_m1
  have hIab := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_ab
  calc
    (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := hF_eq_G
    _ = ∫ t, G t := hI1
    _ = ∫ t in a..b, G t := hIab.symm
    _ = ∫ t in a..b, (f t ^ 2 - (s * t + h) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htab : a ≤ t ∧ t ≤ b := by
        rwa [Set.uIcc_of_le hab.le] at ht
      dsimp [G]
      rw [if_pos htab]


private lemma cap_slice_hasDerivAt_of_cont {F s t dh : ℝ} {h : ℝ → ℝ}
    {g : ℝ → ℝ} (hg_cont : Continuous g)
    (hg_zero_left : g (-F) = 0) (hg_zero_right : g F = 0)
    (hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z)
      (if -F < s * t + h s ∧ s * t + h s < F then
          g (s * t + h s) * (t + dh)
        else 0) s := by
  let a : ℝ := -F
  let b : ℝ := F
  let x : ℝ → ℝ := fun r => r * t + h r
  let u : ℝ → ℝ := fun r => max a (min b (x r))
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hx : HasDerivAt x (t + dh) s := by
    have h1 : HasDerivAt (fun r : ℝ => r * t) t s := by
      simpa using (hasDerivAt_id s).mul_const t
    exact h1.add hh
  have hx_cont : ContinuousAt x s := hx.continuousAt
  have hxO : (fun r : ℝ => x r - x s) =O[𝓝 s] (fun r : ℝ => r - s) :=
    hx.isBigO_sub
  have hu_cont : ContinuousAt u s := by
    dsimp [u, a, b]
    have hmin : ContinuousAt (fun r : ℝ => min F (x r)) s :=
      continuous_min.continuousAt.comp₂ continuousAt_const hx_cont
    have hmax : ContinuousAt (fun r : ℝ => max (-F) (min F (x r))) s :=
      continuous_max.continuousAt.comp₂ continuousAt_const hmin
    simpa using hmax
  have huO : (fun r : ℝ => u r - u s) =O[𝓝 s] (fun r : ℝ => r - s) := by
    dsimp [u, a, b]
    exact isBigO_clamp_sub hxO
  have hP_left : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) 0 a := by
    have h := (hg_cont.integral_hasStrictDerivAt a a).hasDerivAt
    simpa [a, hg_zero_left] using h
  have hP_right : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) 0 b := by
    have h := (hg_cont.integral_hasStrictDerivAt a b).hasDerivAt
    simpa [b, hg_zero_right] using h
  by_cases hcond : -F < s * t + h s ∧ s * t + h s < F
  · have hxs_lower : a < x s := by
      dsimp [x, a]
      simpa using hcond.1
    have hxs_upper : x s < b := by
      dsimp [x, b]
      simpa using hcond.2
    have h_event_lower : ∀ᶠ r in 𝓝 s, a < x r := by
      have hmem : {r : ℝ | a < x r} ∈ 𝓝 s :=
        hx_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hxs_lower)
      exact Filter.eventually_iff.mpr hmem
    have h_event_upper : ∀ᶠ r in 𝓝 s, x r < b := by
      have hmem : {r : ℝ | x r < b} ∈ 𝓝 s :=
        hx_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hxs_upper)
      exact Filter.eventually_iff.mpr hmem
    have h_event_u : ∀ᶠ r in 𝓝 s, u r = x r := by
      filter_upwards [h_event_lower, h_event_upper] with r hr_lower hr_upper
      dsimp [u, a, b]
      rw [min_eq_right hr_upper.le, max_eq_right hr_lower.le]
    have hP_deriv : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) (g (x s)) (x s) :=
      (hg_cont.integral_hasStrictDerivAt a (x s)).hasDerivAt
    have hcomp : HasDerivAt ((fun y : ℝ => ∫ z in a..y, g z) ∘ x)
        (g (x s) * (t + dh)) s := by
      simpa [Function.comp_def] using hP_deriv.comp s hx
    have h_event : (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z) =ᶠ[𝓝 s]
        ((fun y : ℝ => ∫ z in a..y, g z) ∘ x) := by
      filter_upwards [h_event_u] with r hr
      have hr' : max (-F) (min F (r * t + h r)) = r * t + h r := by
        simpa [u, x, a, b] using hr
      simp [a, x, hr']
    have hmain : HasDerivAt
        (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z)
        (g (x s) * (t + dh)) s :=
      HasDerivAt.congr_of_eventuallyEq hcomp h_event
    simpa [x, hcond] using hmain
  · have hcond_false : ¬ (-F < s * t + h s ∧ s * t + h s < F) := hcond
    by_cases hle_lower : s * t + h s ≤ -F
    · have hxs_lower : x s ≤ a := by
        dsimp [x, a]
        simpa using hle_lower
      have hqs : u s = a := by
        dsimp [u, a, b]
        rw [min_eq_right (le_trans hxs_lower hab)]
        rw [max_eq_left hxs_lower]
      have hqO : (fun r : ℝ => u r - a) =O[𝓝 s] (fun r : ℝ => r - s) := by
        simpa [hqs] using huO
      have hderiv0 : HasDerivAt (fun r : ℝ => ∫ z in a..(u r), g z) 0 s := by
        simpa using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
          (P := fun y : ℝ => ∫ z in a..y, g z) (q := u) (s := s) (b := a)
          hP_left hu_cont hqs hqO
      have hmain : HasDerivAt
          (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z) 0 s := by
        simpa [u, a, b] using hderiv0
      simpa [hcond_false] using hmain
    · have h_upper : F ≤ s * t + h s := by
        have h_not_lower : -F < s * t + h s := lt_of_not_ge hle_lower
        have h_not_upper : ¬ s * t + h s < F := by
          intro hup
          exact hcond_false ⟨h_not_lower, hup⟩
        exact le_of_not_gt h_not_upper
      have hxs_upper : b ≤ x s := by
        dsimp [x, b]
        simpa using h_upper
      have hqs : u s = b := by
        dsimp [u, a, b]
        rw [min_eq_left hxs_upper]
        rw [max_eq_right hab]
      have hqO : (fun r : ℝ => u r - b) =O[𝓝 s] (fun r : ℝ => r - s) := by
        simpa [hqs] using huO
      have hderiv0 : HasDerivAt (fun r : ℝ => ∫ z in a..(u r), g z) 0 s := by
        simpa using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
          (P := fun y : ℝ => ∫ z in a..y, g z) (q := u) (s := s) (b := b)
          hP_right hu_cont hqs hqO
      have hmain : HasDerivAt
          (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z) 0 s := by
        simpa [u, a, b] using hderiv0
      simpa [hcond_false] using hmain

private lemma odd_cap_centroid_slice_hasDerivAt {n : ℕ} {F s t dh : ℝ} {h : ℝ → ℝ}
    (hn : 1 ≤ n) (hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))
      (if -F < s * t + h s ∧ s * t + h s < F then
          (t + s * (s * t + h s)) * ((F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) * (t + dh) -
          ((F ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0) s := by
  let W : ℝ → ℝ := fun z => (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)
  let g1 : ℝ → ℝ := W
  let g2 : ℝ → ℝ := fun z => z * W z
  have hg1_cont : Continuous g1 := by
    dsimp [g1, W]
    continuity
  have hg2_cont : Continuous g2 := by
    dsimp [g2, W]
    continuity
  have hW_left : W (-F) = 0 := by
    dsimp [W]
    ring_nf
    simp
  have hW_right : W F = 0 := by
    dsimp [W]
    ring_nf
    simp
  have hg1_left : g1 (-F) = 0 := by simpa [g1] using hW_left
  have hg1_right : g1 F = 0 := by simpa [g1] using hW_right
  have hg2_left : g2 (-F) = 0 := by
    dsimp [g2]
    rw [hW_left]
    simp
  have hg2_right : g2 F = 0 := by
    dsimp [g2]
    rw [hW_right]
    simp
  have hG1 := cap_slice_hasDerivAt_of_cont (F := F) (s := s) (t := t) (dh := dh) (h := h)
    (g := g1) hg1_cont hg1_left hg1_right hF hh
  have hG2 := cap_slice_hasDerivAt_of_cont (F := F) (s := s) (t := t) (dh := dh) (h := h)
    (g := g2) hg2_cont hg2_left hg2_right hF hh
  let G1 : ℝ → ℝ := fun r =>
    ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g1 z
  let G2 : ℝ → ℝ := fun r =>
    ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g2 z
  have hfun : (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) =
      fun r : ℝ => t * G1 r + r * G2 r := by
    funext r
    dsimp [G1, G2, g1, g2, W]
    have hpoint : (fun z : ℝ => (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) =
        fun z : ℝ => t * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)) +
          r * (z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) := by
      funext z
      ring
    calc
      (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))
          = ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              (t * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)) +
                r * (z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))) := by
              rw [hpoint]
      _ = (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              t * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) +
            ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              r * (z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) := by
              rw [intervalIntegral.integral_add]
              · exact (by continuity : Continuous (fun z : ℝ => t * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))).intervalIntegrable _ _
              · exact (by continuity : Continuous (fun z : ℝ => r * (z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))))).intervalIntegrable _ _
      _ = t * (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
                ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) +
            r * (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
                z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) := by
              rw [intervalIntegral.integral_const_mul]
              rw [intervalIntegral.integral_const_mul]
  have hderiv_aux : HasDerivAt (fun r : ℝ => t * G1 r + r * G2 r)
      (t * (if -F < s * t + h s ∧ s * t + h s < F then
          g1 (s * t + h s) * (t + dh) else 0) +
        (G2 s + s * (if -F < s * t + h s ∧ s * t + h s < F then
          g2 (s * t + h s) * (t + dh) else 0))) s := by
    have hprod : HasDerivAt (fun r : ℝ => r * G2 r) (G2 s + s * (if -F < s * t + h s ∧ s * t + h s < F then
        g2 (s * t + h s) * (t + dh) else 0)) s := by
      simpa [G2, Pi.mul_def] using (hasDerivAt_id s).mul hG2
    have hconst := hG1.const_mul t
    have hsum := hconst.add hprod
    simpa [G1, G2, Pi.add_def, Pi.mul_def, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hmain : HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))
      (t * (if -F < s * t + h s ∧ s * t + h s < F then
          g1 (s * t + h s) * (t + dh) else 0) +
        (G2 s + s * (if -F < s * t + h s ∧ s * t + h s < F then
          g2 (s * t + h s) * (t + dh) else 0))) s := by
    rw [hfun]
    exact hderiv_aux
  by_cases hcond : -F < s * t + h s ∧ s * t + h s < F
  · have hL_lower : -F ≤ s * t + h s := le_of_lt hcond.1
    have hL_upper : s * t + h s ≤ F := le_of_lt hcond.2
    have hup : max (-F) (min F (s * t + h s)) = s * t + h s := by
      rw [min_eq_right hL_upper, max_eq_right hL_lower]
    have hG2_val : G2 s = - ((F ^ 2 - (s * t + h s) ^ 2) ^ n *
        Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) / (2 * (n : ℝ) + 1) := by
      dsimp [G2, g2, W]
      rw [hup]
      have hball := ball_cap_first_moment_eq (n := n) (r := F) (L := s * t + h s) hn hF hL_lower hL_upper
      simpa [mul_assoc] using hball
    have hderiv_eq : t * (g1 (s * t + h s) * (t + dh)) +
        (G2 s + s * (g2 (s * t + h s) * (t + dh))) =
        (t + s * (s * t + h s)) * ((F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) * (t + dh) -
        ((F ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) /
          (2 * (n : ℝ) + 1) := by
      have hg1val : g1 (s * t + h s) =
          (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2) := by
        dsimp [g1, W]
      have hg2val : g2 (s * t + h s) =
          (s * t + h s) * ((F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) := by
        dsimp [g2, W]
      rw [hg1val, hg2val, hG2_val]
      ring
    simpa [hcond, hderiv_eq] using hmain
  · have hmain' : HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))
      (t * 0 + (G2 s + s * 0)) s := by
      simpa [hcond] using hmain
    have hG2_zero : G2 s = 0 := by
      by_cases hle_lower : s * t + h s ≤ -F
      · have hup : max (-F) (min F (s * t + h s)) = -F := by
          have hmin : min F (s * t + h s) = s * t + h s := min_eq_right (le_trans hle_lower (by linarith [hF]))
          rw [hmin]
          exact max_eq_left hle_lower
        dsimp [G2, g2, W]
        rw [hup]
        simp
      · have h_upper : F ≤ s * t + h s := by
          have h_not_lower : -F < s * t + h s := lt_of_not_ge hle_lower
          have h_not_upper : ¬ s * t + h s < F := by
            intro hup
            exact hcond ⟨h_not_lower, hup⟩
          exact le_of_not_gt h_not_upper
        have hup : max (-F) (min F (s * t + h s)) = F := by
          have hmin : min F (s * t + h s) = F := min_eq_left h_upper
          rw [hmin]
          exact max_eq_right (by linarith [hF])
        have h_int := ball_cap_first_moment_eq (n := n) (r := F) (L := F) hn hF (by linarith) (by rfl)
        have hzero : F ^ 2 - F ^ 2 = 0 := by ring
        dsimp [G2, g2, W]
        rw [hup]
        have h_int' : (∫ z in (-F)..F, z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) =
            -((F ^ 2 - F ^ 2) ^ n * Real.sqrt (F ^ 2 - F ^ 2)) / (2 * (n : ℝ) + 1) := by
          simpa [mul_assoc] using h_int
        rw [h_int']
        simp [hzero]
    have hderiv_zero : t * 0 + (G2 s + s * 0) = 0 := by
      rw [hG2_zero]
      ring
    have hmain_zero : HasDerivAt
        (fun r : ℝ =>
          ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
            (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) 0 s := by
      simpa [hG2_zero] using hmain'
    simpa [hcond] using hmain_zero


private lemma norm_odd_cap_centroid_slice_integral_le {n : ℕ} {f h : ℝ → ℝ} {M : ℝ}
    (hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hM_nonneg : 0 ≤ M) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (t + r * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))‖ ≤
        (|t| + |r| * M) * (2 * M) * ((M ^ 2) ^ (n - 1) * M) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
  have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  let a : ℝ := -f t
  let b : ℝ := f t
  let U : ℝ := max a (min b (r * t + h r))
  let g : ℝ → ℝ := fun z => (t + r * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))
  have ha_le_b : a ≤ b := by dsimp [a, b]; linarith
  have hU_mem : U ∈ Set.Icc a b := by
    dsimp [U]
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le ha_le_b (min_le_left _ _)
  have hUa : a ≤ U := hU_mem.1
  have hUb : U ≤ b := hU_mem.2
  have hg_bound : ∀ z ∈ Ι a U, ‖g z‖ ≤ (|t| + |r| * M) * ((M ^ 2) ^ (n - 1) * M) := by
    intro z hz
    have hzIoc : z ∈ Set.Ioc a U := by
      simpa [Set.uIoc_of_le hUa] using hz
    have hz_lower : -M ≤ z := by
      have ha_lower : -M ≤ a := by dsimp [a]; linarith
      exact le_trans ha_lower (le_of_lt hzIoc.1)
    have hz_upper : z ≤ M := by
      have hb_upper : b ≤ M := by dsimp [b]; exact hft_le
      exact le_trans (le_trans hzIoc.2 hUb) hb_upper
    have hz_abs : |z| ≤ M := abs_le.mpr ⟨hz_lower, hz_upper⟩
    have hG_nonneg : 0 ≤ f t ^ 2 - z ^ 2 := by
      have hz_le_f : z ≤ f t := le_trans hzIoc.2 hUb
      have hz_ge_negf : -f t ≤ z := le_of_lt hzIoc.1
      have h1 : 0 ≤ f t - z := sub_nonneg.mpr hz_le_f
      have h2 : 0 ≤ f t + z := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hG_le : f t ^ 2 - z ^ 2 ≤ M ^ 2 := by
      have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
      nlinarith [sq_nonneg z]
    have hpow : |(f t ^ 2 - z ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
      rw [abs_pow, abs_of_nonneg hG_nonneg]
      exact pow_le_pow_left₀ hG_nonneg hG_le (n - 1)
    have hsqrt : |Real.sqrt (f t ^ 2 - z ^ 2)| ≤ M := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (Real.sqrt_le_left hM_nonneg).2 hG_le
    have hW_le : |((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))| ≤
        (M ^ 2) ^ (n - 1) * M := by
      simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
    have hlin : |t + r * z| ≤ |t| + |r| * M := by
      calc
        |t + r * z| ≤ |t| + |r * z| := abs_add_le _ _
        _ = |t| + |r| * |z| := by rw [abs_mul]
        _ ≤ |t| + |r| * M := by
          nlinarith [mul_le_mul_of_nonneg_left hz_abs (abs_nonneg r)]
    dsimp [g]
    simpa [abs_mul] using mul_le_mul hlin hW_le (abs_nonneg _) (by positivity)
  have hlen : |U - a| ≤ 2 * M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hUa)]
    calc U - a ≤ b - a := sub_le_sub hUb le_rfl
      _ = 2 * f t := by dsimp [a, b]; ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := U)
      (C := (|t| + |r| * M) * ((M ^ 2) ^ (n - 1) * M)) (f := g) hg_bound
  calc
    ‖∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        (t + r * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))‖
        = ‖∫ z in a..U, g z‖ := by simp [a, b, U, g]
    _ ≤ ((|t| + |r| * M) * ((M ^ 2) ^ (n - 1) * M)) * |U - a| := hnorm
    _ ≤ ((|t| + |r| * M) * ((M ^ 2) ^ (n - 1) * M)) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = (|t| + |r| * M) * (2 * M) * ((M ^ 2) ^ (n - 1) * M) := by ring


private lemma odd_cap_centroid_moment_hasDerivAt_aux {n : ℕ} {f h : ℝ → ℝ}
    (hn : 1 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1))
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (t + r * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
          ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0) s := by
  classical
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  let U : ℝ → ℝ → ℝ := fun r t => max (-f t) (min (f t) (r * t + h r))
  let F : ℝ → ℝ → ℝ := fun r t =>
    ∫ z in (-f t)..(U r t), (t + r * z) * W t z
  let F' : ℝ → ℝ → ℝ := fun r t =>
    if -f t < r * t + h r ∧ r * t + h r < f t then
      (t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
        Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r) -
      ((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
        (2 * (n : ℝ) + 1)
    else 0
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  have hM_nonneg : 0 ≤ M := le_of_lt hMpos
  have h_deriv_cont_on_univ : ContinuousOn (deriv h) Set.univ := by
    exact hh_cont.continuousOn_deriv_of_isOpen isOpen_univ (by simp)
  have h_deriv_cont : Continuous (deriv h) := by
    rwa [continuousOn_univ] at h_deriv_cont_on_univ
  have h_cont_on_univ : ContinuousOn h Set.univ := hh_cont.continuousOn
  have h_cont : Continuous h := by
    rwa [continuousOn_univ] at h_cont_on_univ
  have hh_meas : Measurable h := h_cont.measurable
  have hderiv_meas : Measurable (deriv h) := h_deriv_cont.measurable
  let S : Set ℝ := Set.Icc (s - 1) (s + 1)
  have hS_mem : S ∈ 𝓝 s := by
    dsimp [S]
    rw [Metric.mem_nhds_iff]
    refine ⟨1, by norm_num, ?_⟩
    intro r hr
    have hdist : dist r s < 1 := by simpa [Metric.mem_ball] using hr
    rw [Real.dist_eq] at hdist
    have habs := abs_lt.mp hdist
    constructor <;> linarith
  have h_deriv_cont_on_S : ContinuousOn (deriv h) S := h_deriv_cont.continuousOn
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc : IsCompact (Set.Icc (s - 1) (s + 1))).exists_bound_of_continuousOn
    h_deriv_cont_on_S
  let C : ℝ := max Ch 1
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  have hderiv_bound : ∀ r ∈ S, |deriv h r| ≤ C := by
    intro r hr
    have := hCh r hr
    exact le_trans this (le_max_left _ _)
  have h_cont_on_S : ContinuousOn h S := h_cont.continuousOn
  obtain ⟨Hh, hHh⟩ := (isCompact_Icc : IsCompact (Set.Icc (s - 1) (s + 1))).exists_bound_of_continuousOn
    h_cont_on_S
  let H : ℝ := max |Hh| 1
  have hH_nonneg : 0 ≤ H := by dsimp [H]; positivity
  have h_bound : ∀ r ∈ S, |h r| ≤ H := by
    intro r hr
    have hle := hHh r hr
    have hle' : |h r| ≤ |Hh| := by
      simpa [Real.norm_eq_abs] using le_trans hle (le_abs_self Hh)
    exact le_trans hle' (le_max_left _ _)
  let R : ℝ := |s| + 1
  have hR_nonneg : 0 ≤ R := by dsimp [R]; positivity
  have hR_mem : ∀ r ∈ S, |r| ≤ R := by
    intro r hr
    have hdist : |r - s| ≤ 1 := by
      rcases hr with ⟨h1, h2⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hle : |r| ≤ |s| + |r - s| := by
      calc |r| = |s + (r - s)| := by ring_nf
        _ ≤ |s| + |r - s| := abs_add_le _ _
    dsimp [R]
    nlinarith
  let Kline : ℝ := 1 + R * (R + H)
  let Wbase : ℝ := (M ^ 2) ^ (n - 1) * M
  have hKline_nonneg : 0 ≤ Kline := by dsimp [Kline]; positivity
  have hWbase_nonneg : 0 ≤ Wbase := by dsimp [Wbase]; positivity
  let B : ℝ := Kline * Wbase * (1 + C) + (M ^ 2) ^ n * M / (2 * (n : ℝ) + 1)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hL_bound : ∀ r ∈ S, ∀ t ∈ Set.Icc (-1 : ℝ) 1, |r * t + h r| ≤ R + H := by
    intro r hr t ht
    have ht_abs : |t| ≤ 1 := by
      exact abs_le.mpr ⟨ht.1, by norm_num at ht ⊢; exact ht.2⟩
    calc
      |r * t + h r| ≤ |r * t| + |h r| := abs_add_le _ _
      _ = |r| * |t| + |h r| := by rw [abs_mul]
      _ ≤ R * 1 + H := by
        exact add_le_add (mul_le_mul (hR_mem r hr) ht_abs (abs_nonneg t) hR_nonneg) (h_bound r hr)
      _ = R + H := by ring
  have hF_meas : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable (F r) (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    filter_upwards [hS_mem] with r hr
    have hLm : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hUm : Measurable (fun t : ℝ => max (-f t) (min (f t) (r * t + h r))) := by fun_prop
    have hg : Measurable (Function.uncurry (fun t z : ℝ => (t + r * z) * W t z)) := by fun_prop
    exact (aeStronglyMeasurable_intervalIntegral_param hLm hUm hg).restrict
  have hF_int : IntervalIntegrable (F s) volume (-1 : ℝ) 1 := by
    rw [intervalIntegrable_iff]
    have hmeas : AEStronglyMeasurable (F s) (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
      exact hF_meas.self_of_nhds
    let Bint : ℝ := (1 + |s| * M) * (2 * M) * Wbase
    have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint]; positivity
    have hbnd' := norm_odd_cap_centroid_slice_integral_le (n := n) (f := f) (h := h) (M := M)
      hf_le_M hf_nonneg hM_nonneg s
    have hbnd : ∀ᵐ t ∂volume.restrict (Set.uIoc (-1 : ℝ) 1), ‖F s t‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      intro htIoc
      have htIoc' : t ∈ Set.Ioc (-1 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using htIoc
      have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc'
      have ht_abs : |t| ≤ 1 := by
        exact abs_le.mpr ⟨htcc.1, by norm_num at htcc ⊢; exact htcc.2⟩
      have hle : |t| + |s| * M ≤ 1 + |s| * M := by nlinarith [ht_abs]
      have hbound_t := ht htIoc
      calc
        ‖F s t‖ ≤ (|t| + |s| * M) * (2 * M) * Wbase := by
          simpa [F, U, W, Wbase] using hbound_t
        _ ≤ (1 + |s| * M) * (2 * M) * Wbase := by
          nlinarith [hle, (by positivity : 0 ≤ (2 * M) * Wbase)]
        _ = Bint := by dsimp [Bint]
    exact IntegrableOn.of_bound (by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top) hmeas _ hbnd
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    have h_cond_meas : MeasurableSet {t : ℝ | -f t < s * t + h s ∧ s * t + h s < f t} := by
      apply MeasurableSet.inter
      · exact measurableSet_lt hf_meas.neg (by fun_prop)
      · exact measurableSet_lt (by fun_prop) hf_meas
    have h_then_meas : Measurable (fun t : ℝ =>
        (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
        ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
          (2 * (n : ℝ) + 1)) := by
      fun_prop
    exact (Measurable.ite h_cond_meas h_then_meas measurable_const).aestronglyMeasurable.restrict
  have h_bound' : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ r ∈ S, ‖F' r t‖ ≤ B := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hft_le : f t ≤ M := hf_le_M t htcc
    by_cases hcond : -f t < r * t + h r ∧ r * t + h r < f t
    · have hL_abs : |r * t + h r| ≤ R + H := hL_bound r hr t htcc
      have hG_nonneg : 0 ≤ f t ^ 2 - (r * t + h r) ^ 2 := by
        have hL_abs_lt : |r * t + h r| < f t := by
          rw [abs_lt]
          exact ⟨hcond.1, hcond.2⟩
        nlinarith
      have hG_le : f t ^ 2 - (r * t + h r) ^ 2 ≤ M ^ 2 := by
        have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
        nlinarith [sq_nonneg (r * t + h r)]
      have hWbase_le : |((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2))| ≤ Wbase := by
        have hpow : |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
          rw [abs_pow, abs_of_nonneg hG_nonneg]
          exact pow_le_pow_left₀ hG_nonneg hG_le (n - 1)
        have hsqrt : |Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)| ≤ M := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          exact (Real.sqrt_le_left hM_nonneg).2 hG_le
        dsimp [Wbase]
        simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
      have hWn_le : |((f t ^ 2 - (r * t + h r) ^ 2) ^ n *
          Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2))| ≤ (M ^ 2) ^ n * M := by
        have hpow : |(f t ^ 2 - (r * t + h r) ^ 2) ^ n| ≤ (M ^ 2) ^ n := by
          rw [abs_pow, abs_of_nonneg hG_nonneg]
          exact pow_le_pow_left₀ hG_nonneg hG_le n
        have hsqrt : |Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)| ≤ M := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          exact (Real.sqrt_le_left hM_nonneg).2 hG_le
        simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
      have ht_abs : |t| ≤ 1 := by
        exact abs_le.mpr ⟨htcc.1, by norm_num at htcc ⊢; exact htcc.2⟩
      have hlin : |t + r * (r * t + h r)| ≤ Kline := by
        calc
          |t + r * (r * t + h r)| ≤ |t| + |r * (r * t + h r)| := abs_add_le _ _
          _ = |t| + |r| * |r * t + h r| := by rw [abs_mul]
          _ ≤ 1 + R * (R + H) := by
            exact add_le_add ht_abs (mul_le_mul (hR_mem r hr) hL_abs (abs_nonneg (r * t + h r)) hR_nonneg)
          _ = Kline := by dsimp [Kline]
      have hderiv_le : |t + deriv h r| ≤ 1 + C := by
        calc
          |t + deriv h r| ≤ |t| + |deriv h r| := abs_add_le _ _
          _ ≤ 1 + C := by exact add_le_add ht_abs (hderiv_bound r hr)
      have hfirst : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r)| ≤
          Kline * Wbase * (1 + C) := by
        have hprod1 : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2))| ≤ Kline * Wbase := by
          simpa [abs_mul] using mul_le_mul hlin hWbase_le (abs_nonneg _) hKline_nonneg
        have hprod2 : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r)| ≤
            (Kline * Wbase) * (1 + C) := by
          simpa [abs_mul] using mul_le_mul hprod1 hderiv_le (abs_nonneg _) (by positivity)
        simpa [mul_assoc] using hprod2
      have hsecond : |((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
          (2 * (n : ℝ) + 1)| ≤ (M ^ 2) ^ n * M / (2 * (n : ℝ) + 1) := by
        have hden_nonneg : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
        rw [abs_div, abs_of_nonneg hden_nonneg]
        exact div_le_div_of_nonneg_right hWn_le hden_nonneg
      have hsum_le : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r) -
        ((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
          (2 * (n : ℝ) + 1)| ≤ B := by
        have htri := abs_sub_le ((t + r * (r * t + h r)) *
            ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) *
            (t + deriv h r)) 0
            (((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
              (2 * (n : ℝ) + 1))
        have htri' : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r) -
          ((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
            (2 * (n : ℝ) + 1)| ≤
            |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
              Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r)| +
            |((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
              (2 * (n : ℝ) + 1)| := by
          simpa [sub_zero, zero_sub] using htri
        dsimp [B]
        nlinarith [htri', hfirst, hsecond]
      dsimp [F']
      rw [if_pos hcond]
      exact hsum_le
    · dsimp [F']
      rw [if_neg hcond, abs_zero]
      exact hB_nonneg
  have h_bound_int : IntervalIntegrable (fun _ : ℝ => B) volume (-1 : ℝ) 1 := by
    exact intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ r ∈ S,
      HasDerivAt (fun r => F r t) (F' r t) r := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hh_deriv : HasDerivAt h (deriv h r) r := by
      have hd : DifferentiableAt ℝ h r := by
        exact (hh_cont.contDiffAt (by simp)).differentiableAt (by simp)
      exact hd.hasDerivAt
    have hslice := odd_cap_centroid_slice_hasDerivAt (n := n) (F := f t) (s := r) (t := t)
      (dh := deriv h r) (h := h) hn hft_nonneg hh_deriv
    simpa [F, F', U, W] using hslice
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := F) (F' := F') (x₀ := s) (s := S) (μ := volume) (a := (-1 : ℝ)) (b := 1)
    hS_mem hF_meas hF_int hF'_meas h_bound' h_bound_int h_diff).2

private lemma odd_cap_centroid_moment_hasDerivAt {n : ℕ} {f h : ℝ → ℝ}
    (hn : 1 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1))
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (t + r * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
          ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0) s := by
  exact odd_cap_centroid_moment_hasDerivAt_aux hn hf_nonneg hf_meas hf_bdd hh_cont s


private lemma odd_active_integral_eq_interval {f : ℝ → ℝ} {s h a b : ℝ} {D : ℝ → ℝ}
    (hs : 0 < s)
    (ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1) (hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hfa_sq : f a ^ 2 = (s * a + h) ^ 2)
    (hfb_sq : f b ^ 2 = (s * b + h) ^ 2)
    (hD_zero_out : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ¬ (-f t < s * t + h ∧ s * t + h < f t) → D t = 0)
    (hD_a : D a = 0) (hD_b : D b = 0) :
    (∫ t in (-1 : ℝ)..1, if -f t < s * t + h ∧ s * t + h < f t then D t else 0) =
      ∫ t in a..b, D t := by
  have hactive := active_nonneg_outside_of_roots_inside (f := f) (s := s) (h := h) (a := a) (b := b)
    hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  let L : ℝ → ℝ := fun t => s * t + h
  let F : ℝ → ℝ := fun t => if -f t < L t ∧ L t < f t then D t else 0
  let G : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then D t else 0
  have hFG : Set.EqOn F G (Set.Icc (-1 : ℝ) 1) := by
    intro t ht
    by_cases htab : a ≤ t ∧ t ≤ b
    · dsimp [F, G, L]
      rw [if_pos htab]
      by_cases hact : -f t < s * t + h ∧ s * t + h < f t
      · rw [if_pos hact]
      · rw [if_neg hact, hD_zero_out t ht hact]
    · dsimp [F, G, L]
      have hact_false : ¬ (-f t < s * t + h ∧ s * t + h < f t) := by
        intro hact
        exact htab (hactive.1 t ht hact)
      rw [if_neg htab, if_neg hact_false]
  have hF_eq_G : (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hFG
  have hab : a < b := lt_trans ha_neg hb_pos
  have hsuppG_m1 : Function.support G ⊆ Set.Ioc (-1 : ℝ) 1 := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : a ≤ t ∧ t ≤ b
    · have ht_gt : -1 < t := lt_of_lt_of_le ha_mem.1 htab.1
      have ht_le : t ≤ 1 := le_trans htab.2 (le_of_lt hb_mem.2)
      exact ⟨ht_gt, ht_le⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hsuppG_ab : Function.support G ⊆ Set.Ioc a b := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : a ≤ t ∧ t ≤ b
    · have hta_ne : t ≠ a := by
        intro hta
        have hG0 : G t = 0 := by
          subst t
          simp [G, hD_a]
        exact (ht hG0).elim
      have hta_lt : a < t := lt_of_le_of_ne htab.1 (Ne.symm hta_ne)
      exact ⟨hta_lt, htab.2⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := -1) (b := 1) hsuppG_m1
  have hIab := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_ab
  calc
    (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := hF_eq_G
    _ = ∫ t, G t := hI1
    _ = ∫ t in a..b, G t := hIab.symm
    _ = ∫ t in a..b, D t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htab : a ≤ t ∧ t ≤ b := by
        rwa [Set.uIcc_of_le hab.le] at ht
      dsimp [G]
      rw [if_pos htab]


private lemma odd_weight_eq_zero_of_not_active {n : ℕ} {f L : ℝ}
    (hf_nonneg : 0 ≤ f)
    (hnot : ¬ (-f < L ∧ L < f)) :
    (f ^ 2 - L ^ 2) ^ (n - 1) * Real.sqrt (f ^ 2 - L ^ 2) = 0 := by
  have hbase_nonpos : f ^ 2 - L ^ 2 ≤ 0 := by
    by_cases hL_le : L ≤ -f
    · have hf_le_negL : f ≤ -L := by linarith
      have hL_nonneg_neg : 0 ≤ -L := by linarith
      have hsq : f ^ 2 ≤ L ^ 2 := by
        rw [← neg_sq L]
        exact (sq_le_sq₀ hf_nonneg hL_nonneg_neg).2 hf_le_negL
      nlinarith
    · have hnegf_lt_L : -f < L := lt_of_not_ge hL_le
      have hf_le_L : f ≤ L := le_of_not_gt (by
        intro hLf
        exact hnot ⟨hnegf_lt_L, hLf⟩)
      have hL_nonneg : 0 ≤ L := le_trans hf_nonneg hf_le_L
      have hsq : f ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hf_nonneg hL_nonneg).2 hf_le_L
      nlinarith
  rw [Real.sqrt_eq_zero_of_nonpos hbase_nonpos, mul_zero]

private lemma odd_pow_weight_eq_zero_of_not_active {n : ℕ} {f L : ℝ}
    (hf_nonneg : 0 ≤ f)
    (hnot : ¬ (-f < L ∧ L < f)) :
    (f ^ 2 - L ^ 2) ^ n * Real.sqrt (f ^ 2 - L ^ 2) = 0 := by
  have hbase_nonpos : f ^ 2 - L ^ 2 ≤ 0 := by
    by_cases hL_le : L ≤ -f
    · have hf_le_negL : f ≤ -L := by linarith
      have hL_nonneg_neg : 0 ≤ -L := by linarith
      have hsq : f ^ 2 ≤ L ^ 2 := by
        rw [← neg_sq L]
        exact (sq_le_sq₀ hf_nonneg hL_nonneg_neg).2 hf_le_negL
      nlinarith
    · have hnegf_lt_L : -f < L := lt_of_not_ge hL_le
      have hf_le_L : f ≤ L := le_of_not_gt (by
        intro hLf
        exact hnot ⟨hnegf_lt_L, hLf⟩)
      have hL_nonneg : 0 ≤ L := le_trans hf_nonneg hf_le_L
      have hsq : f ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hf_nonneg hL_nonneg).2 hf_le_L
      nlinarith
  rw [Real.sqrt_eq_zero_of_nonpos hbase_nonpos, mul_zero]


private lemma odd_cap_centroid_moment_deriv_eq_zero {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1)
    (h_moment : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
          ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0) = 0 := by
  intro s hs
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  rcases hxy_inside s hs with ⟨hp_mem, hq_mem⟩
  let p : ℝ := -x s
  let q : ℝ := y s
  have hp_neg : p < 0 := by dsimp [p]; linarith
  have hq_pos : 0 < q := by dsimp [q]; exact hypos
  have hfp_sq : f p ^ 2 = (s * p + h s) ^ 2 := by simpa [p] using hfx_sq
  have hfq_sq : f q ^ 2 = (s * q + h s) ^ 2 := by simpa [q] using hfy_sq
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    profile_nonneg_Icc_general hab hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    cap_profile_measurable_of_smooth hab hf_support hf_cont hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) :=
    concaveOn_Icc_bounded hab hf_conc
  have hactive := active_nonneg_outside_of_roots_inside (f := f) (s := s) (h := h s)
    (a := p) (b := q) hs hp_mem hq_mem hp_neg hq_pos hf_conc hf_nonneg hf_pos hfp_sq hfq_sq
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (L t) ^ 2)
  let Gpow : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (L t) ^ 2)
  let Cder : ℝ := deriv h s
  let D : ℝ → ℝ := fun t => (t + s * (L t)) * W t * (t + Cder) - Gpow t / (2 * (n : ℝ) + 1)
  have hD_zero_out : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ¬ (-f t < L t ∧ L t < f t) → D t = 0 := by
    intro t ht hnot
    have hW0 : W t = 0 := by
      dsimp [W, L]
      exact odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := s * t + h s) (hf_nonneg t ht) hnot
    have hG0 : Gpow t = 0 := by
      dsimp [Gpow, L]
      exact odd_pow_weight_eq_zero_of_not_active (n := n) (f := f t) (L := s * t + h s) (hf_nonneg t ht) hnot
    dsimp [D]
    rw [hW0, hG0]
    simp
  have hD_p : D p = 0 := by
    have hbase : f p ^ 2 - (L p) ^ 2 = 0 := by
      dsimp [L]
      rw [hfp_sq]
      ring
    have hWp : W p = 0 := by
      dsimp [W, L]
      rw [hbase]
      simp
    have hGp : Gpow p = 0 := by
      dsimp [Gpow, L]
      rw [hbase]
      simp
    dsimp [D]
    rw [hWp, hGp]
    simp
  have hD_q : D q = 0 := by
    have hbase : f q ^ 2 - (L q) ^ 2 = 0 := by
      dsimp [L]
      rw [hfq_sq]
      ring
    have hWq : W q = 0 := by
      dsimp [W, L]
      rw [hbase]
      simp
    have hGq : Gpow q = 0 := by
      dsimp [Gpow, L]
      rw [hbase]
      simp
    dsimp [D]
    rw [hWq, hGq]
    simp
  have hconv : (∫ t in (-1 : ℝ)..1, if -f t < L t ∧ L t < f t then D t else 0) =
      ∫ t in p..q, D t := by
    simpa [L] using odd_active_integral_eq_interval (f := f) (s := s) (h := h s) (a := p) (b := q)
      (D := D) hs hp_mem hq_mem hp_neg hq_pos hf_conc hf_nonneg hf_pos hfp_sq hfq_sq hD_zero_out hD_p hD_q
  have hI : (∫ t in p..q, Gpow t) = C / Real.sqrt (1 + s ^ 2) := by
    have hI0 := h_moment s hs
    simpa [p, q, Gpow, L] using hI0
  have hJcenter : (∫ t in p..q, W t * (t + Cder)) = 0 := by
    have hJ0 := h_center s hs
    simpa [p, q, W, L, Cder] using hJ0
  have hpq_le : p ≤ q := le_of_lt (lt_trans hp_neg hq_pos)
  have hf_cont_ab : ContinuousOn f (Set.Icc p q) := by
    exact hf_cont.continuousOn.mono (by
      intro t ht
      exact ⟨lt_of_lt_of_le hp_mem.1 ht.1, lt_of_le_of_lt ht.2 hq_mem.2⟩)
  have hG_nonneg_on : ∀ t ∈ Set.Icc p q, 0 ≤ f t ^ 2 - L t ^ 2 := by
    intro t ht
    have hnonneg := hactive.2 t ht
    have h1 : 0 ≤ f t - L t := hnonneg.1
    have h2 : 0 ≤ f t + L t := hnonneg.2
    nlinarith [mul_nonneg h1 h2]
  have hG_cont : ContinuousOn (fun t : ℝ => f t ^ 2 - L t ^ 2) (Set.Icc p q) := by
    dsimp [L]
    have hf_sq : ContinuousOn (fun t : ℝ => f t ^ 2) (Set.Icc p q) := hf_cont_ab.pow 2
    have hL_aff : ContinuousOn (fun t : ℝ => (s * t + h s) ^ 2) (Set.Icc p q) := by
      fun_prop
    exact hf_sq.sub hL_aff
  have hW_cont : ContinuousOn W (Set.Icc p q) := by
    dsimp [W]
    exact (hG_cont.pow (n - 1)).mul hG_cont.sqrt
  have hGpow_cont : ContinuousOn Gpow (Set.Icc p q) := by
    dsimp [Gpow]
    exact (hG_cont.pow n).mul hG_cont.sqrt
  have hL_cont : ContinuousOn L (Set.Icc p q) := by
    dsimp [L]
    fun_prop
  have hid_cont : ContinuousOn (fun t : ℝ => t) (Set.Icc p q) := continuousOn_id
  have hD_interval : (∫ t in p..q, D t) =
      (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) -
        (∫ t in p..q, Gpow t) / (2 * (n : ℝ) + 1) := by
    have hfun : Set.EqOn (fun t : ℝ => (t + s * L t) * W t * (t + Cder)) (fun t : ℝ =>
        (1 + s ^ 2) * (W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (W t * (t + Cder))) (Set.Icc p q) := by
      intro t ht
      dsimp [L]
      ring
    have h_int1 : (∫ t in p..q, (t + s * L t) * W t * (t + Cder)) =
        ∫ t in p..q, ((1 + s ^ 2) * (W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (W t * (t + Cder))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc p q := by
        rwa [Set.uIcc_of_le hpq_le] at ht
      exact hfun htIcc
    have h_int2 : (∫ t in p..q, ((1 + s ^ 2) * (W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (W t * (t + Cder)))) =
        (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (∫ t in p..q, W t * (t + Cder)) := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const_mul]
      · have h1 : ContinuousOn (fun t : ℝ => W t * (t + Cder) ^ 2) (Set.Icc p q) := by
          exact hW_cont.mul ((hid_cont.add continuousOn_const).pow 2)
        exact (continuousOn_const.mul h1).intervalIntegrable_of_Icc hpq_le
      · have h2 : ContinuousOn (fun t : ℝ => W t * (t + Cder)) (Set.Icc p q) := by
          exact hW_cont.mul (hid_cont.add continuousOn_const)
        exact (continuousOn_const.mul h2).intervalIntegrable_of_Icc hpq_le
    have h_int3 : (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (∫ t in p..q, W t * (t + Cder)) =
        (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) := by
      rw [hJcenter]
      simp
    have hD_eq : (∫ t in p..q, D t) =
        (∫ t in p..q, (t + s * L t) * W t * (t + Cder)) -
          (∫ t in p..q, Gpow t) / (2 * (n : ℝ) + 1) := by
      dsimp [D]
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_div]
      · have h1 : ContinuousOn (fun t : ℝ => (t + s * L t) * W t * (t + Cder)) (Set.Icc p q) := by
          exact ((hid_cont.add (continuousOn_const.mul hL_cont)).mul hW_cont).mul
            (hid_cont.add continuousOn_const)
        exact h1.intervalIntegrable_of_Icc hpq_le
      · exact (hGpow_cont.div_const (2 * (n : ℝ) + 1)).intervalIntegrable_of_Icc hpq_le
    rw [hD_eq, h_int1, h_int2, h_int3]
  have hQ_deriv := odd_moment_integral_hasDerivAt_smooth (n := n) (f := f) (h := h) (a := -1) (b := 1)
    hn (by norm_num) hf_nonneg hf_meas hf_bdd hh_cont s
  have hR_deriv := hasDerivAt_const_div_sqrt_one_add_sq C s
  let Qfun : ℝ → ℝ := fun r => ∫ t in (-1 : ℝ)..1,
      (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2) ^ n *
        Real.sqrt (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2)
  let Qfun_unclamped : ℝ → ℝ := fun r => ∫ t in (-1 : ℝ)..1, (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)
  let Rfun : ℝ → ℝ := fun r => C / Real.sqrt (1 + r ^ 2)
  have hQ_eq_event : Qfun =ᶠ[𝓝 s] Rfun := by
    have hpos_ev : ∀ᶠ r in 𝓝 s, 0 < r := by
      exact (isOpen_Ioi.mem_nhds hs)
    filter_upwards [hpos_ev] with r hr
    have hrxy := hxy r hr
    have hrinside := hxy_inside r hr
    rcases hrxy with ⟨hxr, hyr, hfy_r, hfx_r⟩
    let ar : ℝ := -x r
    let br : ℝ := y r
    have har_mem : ar ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [ar] using hrinside.1
    have hbr_mem : br ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [br] using hrinside.2
    have har_neg : ar < 0 := by dsimp [ar]; linarith
    have hbr_pos : 0 < br := by dsimp [br]; exact hyr
    have hfar_sq : f ar ^ 2 = (r * ar + h r) ^ 2 := by simpa [ar] using hfx_r
    have hfbr_sq : f br ^ 2 = (r * br + h r) ^ 2 := by simpa [br] using hfy_r
    have hpow_eq := odd_pow_clamp_integral_eq_interval_of_active (n := n) (f := f) (s := r) (h := h r)
      (a := ar) (b := br) hn hr har_mem hbr_mem har_neg hbr_pos hf_conc hf_nonneg hf_pos hfar_sq hfbr_sq
    have hI_r := h_moment r hr
    calc
      Qfun r = ∫ t in ar..br, (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) := by
        dsimp [Qfun]
        simpa using hpow_eq
      _ = C / Real.sqrt (1 + r ^ 2) := by
        simpa [ar, br] using hI_r
      _ = Rfun r := by dsimp [Rfun]
  have hQfun_eq_unclamped : Qfun =ᶠ[𝓝 s] Qfun_unclamped := by
    have hpos_ev : ∀ᶠ r in 𝓝 s, 0 < r := by
      exact (isOpen_Ioi.mem_nhds hs)
    filter_upwards [hpos_ev] with r hr
    dsimp [Qfun, Qfun_unclamped]
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases hact : -f t < r * t + h r ∧ r * t + h r < f t
    · have hU : max (-f t) (min (f t) (r * t + h r)) = r * t + h r := by
        rw [min_eq_right hact.2.le, max_eq_right hact.1.le]
      simp [hU]
    · have hU_base_zero : f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2 = 0 := by
        have hle_or : r * t + h r ≤ -f t ∨ f t ≤ r * t + h r := by
          by_contra hboth
          have hnot := not_or.mp hboth
          have hlt_lower : -f t < r * t + h r := lt_of_not_ge hnot.1
          have hlt_upper : r * t + h r < f t := lt_of_not_ge hnot.2
          exact hact ⟨hlt_lower, hlt_upper⟩
        rcases hle_or with hL_low | hL_high
        · have hmin : min (f t) (r * t + h r) = r * t + h r := by
            rw [min_eq_right (le_trans hL_low (by
              have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
                simpa [Set.uIcc_of_le hab] using ht
              linarith [hf_nonneg t htIcc]))]
          have hU : max (-f t) (min (f t) (r * t + h r)) = -f t := by
            rw [hmin]
            exact max_eq_left hL_low
          rw [hU]
          ring
        · have hmin : min (f t) (r * t + h r) = f t := by
            rw [min_eq_left hL_high]
          have hU : max (-f t) (min (f t) (r * t + h r)) = f t := by
            rw [hmin]
            exact max_eq_right (by
              have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
                simpa [Set.uIcc_of_le hab] using ht
              linarith [hf_nonneg t htIcc])
          rw [hU]
          ring
      have h_unclamped_zero : (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) = 0 := by
        have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
          simpa [Set.uIcc_of_le hab] using ht
        exact odd_pow_weight_eq_zero_of_not_active (n := n) (f := f t) (L := r * t + h r) (hf_nonneg t htIcc) hact
      simp [hU_base_zero, h_unclamped_zero]
  have hQ_derivQ : HasDerivAt Qfun (-(2 * (n : ℝ) + 1) * (∫ t in (-1 : ℝ)..1,
        (s * t + h s) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) * (t + deriv h s))) s := by
    have heq : Qfun =ᶠ[𝓝 s] (fun r : ℝ => ∫ t in (-1 : ℝ)..1, (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) := by
      simpa [Qfun_unclamped] using hQfun_eq_unclamped
    exact hQ_deriv.congr_of_eventuallyEq heq
  have hQ_deriv' : HasDerivAt Qfun (-(C * s) / Real.sqrt (1 + s ^ 2) ^ 3) s :=
    hR_deriv.congr_of_eventuallyEq hQ_eq_event
  have hder_eq : -(2 * (n : ℝ) + 1) * (∫ t in (-1 : ℝ)..1,
        (s * t + h s) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) * (t + deriv h s)) =
      -(C * s) / Real.sqrt (1 + s ^ 2) ^ 3 := by
    have huniq := hQ_derivQ.unique hQ_deriv'
    simpa [Qfun_unclamped, L, W, Cder] using huniq
  have hJL_full : (∫ t in (-1 : ℝ)..1, L t * W t * (t + Cder)) =
      C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
    have hcoef_pos : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hsqrt_pos : 0 < Real.sqrt (1 + s ^ 2) := by
      exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg s])
    have hsqrt3_ne : Real.sqrt (1 + s ^ 2) ^ 3 ≠ 0 := by
      exact pow_ne_zero 3 (ne_of_gt hsqrt_pos)
    have hder_pos : (2 * (n : ℝ) + 1) * (∫ t in (-1 : ℝ)..1, L t * W t * (t + Cder)) =
        (C * s) / Real.sqrt (1 + s ^ 2) ^ 3 := by
      have hder_eq' := hder_eq
      field_simp [hsqrt3_ne] at hder_eq'
      field_simp [hsqrt3_ne]
      simpa [L, W, Cder, mul_comm, mul_left_comm, mul_assoc] using hder_eq'
    have hder_mul : (2 * (n : ℝ) + 1) * (∫ t in (-1 : ℝ)..1, L t * W t * (t + Cder)) *
        Real.sqrt (1 + s ^ 2) ^ 3 = C * s := by
      rw [hder_pos]
      field_simp [hsqrt3_ne]
    field_simp [hcoef_pos, hsqrt3_ne]
    nlinarith [hder_mul]
  have hWzero_out : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ¬ (-f t < L t ∧ L t < f t) → L t * W t * (t + Cder) = 0 := by
    intro t ht hnot
    have hW0 : W t = 0 := by
      dsimp [W, L]
      exact odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := s * t + h s) (hf_nonneg t ht) hnot
    rw [hW0]
    simp
  have hJL_end_p : L p * W p * (p + Cder) = 0 := by
    have hbase : f p ^ 2 - (L p) ^ 2 = 0 := by
      dsimp [L]
      rw [hfp_sq]
      ring
    have hWp : W p = 0 := by
      dsimp [W, L]
      rw [hbase]
      simp
    rw [hWp]
    simp
  have hJL_end_q : L q * W q * (q + Cder) = 0 := by
    have hbase : f q ^ 2 - (L q) ^ 2 = 0 := by
      dsimp [L]
      rw [hfq_sq]
      ring
    have hWq : W q = 0 := by
      dsimp [W, L]
      rw [hbase]
      simp
    rw [hWq]
    simp
  have hJL_interval : (∫ t in p..q, L t * W t * (t + Cder)) =
      C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
    have hfull := hJL_full
    have hconv2 : (∫ t in (-1 : ℝ)..1, if -f t < L t ∧ L t < f t then L t * W t * (t + Cder) else 0) =
        ∫ t in p..q, L t * W t * (t + Cder) := by
      simpa [L] using odd_active_integral_eq_interval (f := f) (s := s) (h := h s) (a := p) (b := q)
        (D := fun t => L t * W t * (t + Cder)) hs hp_mem hq_mem hp_neg hq_pos hf_conc hf_nonneg hf_pos hfp_sq hfq_sq hWzero_out hJL_end_p hJL_end_q
    have hfull' : (∫ t in (-1 : ℝ)..1, if -f t < L t ∧ L t < f t then L t * W t * (t + Cder) else 0) =
        C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
      calc
        (∫ t in (-1 : ℝ)..1, if -f t < L t ∧ L t < f t then L t * W t * (t + Cder) else 0)
            = ∫ t in (-1 : ℝ)..1, L t * W t * (t + Cder) := by
              apply intervalIntegral.integral_congr
              intro t ht
              by_cases hact : -f t < L t ∧ L t < f t
              · simp [hact]
              · have hW0 : W t = 0 := by
                  have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
                    simpa [Set.uIcc_of_le hab] using ht
                  dsimp [W, L]
                  exact odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := s * t + h s) (hf_nonneg t htIcc) hact
                simp [hact, hW0]
        _ = C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := hfull
    rwa [hconv2] at hfull'
  have hJ2 : (∫ t in p..q, W t * (t + Cder) ^ 2) =
      C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
    have hL_int : (∫ t in p..q, L t * W t * (t + Cder)) =
        s * (∫ t in p..q, W t * (t + Cder) ^ 2) := by
      calc
        (∫ t in p..q, L t * W t * (t + Cder))
            = ∫ t in p..q, (s * t + h s) * W t * (t + Cder) := by
                simp [L]
        _ = ∫ t in p..q, (s * ((t + Cder) * W t * (t + Cder)) + (h s - s * Cder) * (W t * (t + Cder))) := by
                apply intervalIntegral.integral_congr
                intro t ht
                ring_nf
        _ = s * (∫ t in p..q, (t + Cder) * W t * (t + Cder)) + (h s - s * Cder) * (∫ t in p..q, W t * (t + Cder)) := by
                rw [intervalIntegral.integral_add]
                · rw [intervalIntegral.integral_const_mul]
                  rw [intervalIntegral.integral_const_mul]
                · have h1 : ContinuousOn (fun t : ℝ => s * ((t + Cder) * W t * (t + Cder))) (Set.Icc p q) := by
                    exact continuousOn_const.mul (((hid_cont.add continuousOn_const).mul hW_cont).mul (hid_cont.add continuousOn_const))
                  exact h1.intervalIntegrable_of_Icc hpq_le
                · have h2 : ContinuousOn (fun t : ℝ => (h s - s * Cder) * (W t * (t + Cder))) (Set.Icc p q) := by
                    exact continuousOn_const.mul (hW_cont.mul (hid_cont.add continuousOn_const))
                  exact h2.intervalIntegrable_of_Icc hpq_le
        _ = s * (∫ t in p..q, W t * (t + Cder) ^ 2) := by
                rw [hJcenter]
                simp only [mul_zero, add_zero]
                apply congrArg (fun q : ℝ => s * q)
                apply intervalIntegral.integral_congr
                intro t ht
                ring
    have hs_ne : s ≠ 0 := ne_of_gt hs
    calc
      (∫ t in p..q, W t * (t + Cder) ^ 2)
          = (∫ t in p..q, L t * W t * (t + Cder)) / s := by
            rw [hL_int]
            field_simp [hs_ne]
      _ = (C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3)) / s := by rw [hJL_interval]
      _ = C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
            field_simp [hs_ne]
  have hD_zero : (∫ t in p..q, D t) = 0 := by
    rw [hD_interval]
    have hsq : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := by
      rw [Real.sq_sqrt (by nlinarith [sq_nonneg s])]
    have hden_ne : Real.sqrt (1 + s ^ 2) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [sq_nonneg s]))
    have hcoef_pos : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    calc
      (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) -
          (∫ t in p..q, Gpow t) / (2 * (n : ℝ) + 1)
          = (1 + s ^ 2) * (C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3)) -
              (C / Real.sqrt (1 + s ^ 2)) / (2 * (n : ℝ) + 1) := by
            rw [hJ2, hI]
      _ = 0 := by
            have hsqrt3_eq : Real.sqrt (1 + s ^ 2) ^ 3 = (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) := by
              rw [pow_succ, hsq]
            calc
              (1 + s ^ 2) * (C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3)) -
                  (C / Real.sqrt (1 + s ^ 2)) / (2 * (n : ℝ) + 1)
                  = (1 + s ^ 2) * (C / ((2 * (n : ℝ) + 1) * ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)))) -
                      (C / Real.sqrt (1 + s ^ 2)) / (2 * (n : ℝ) + 1) := by
                    rw [hsqrt3_eq]
              _ = C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2)) -
                    C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2)) := by
                    field_simp [hsq, hden_ne, hcoef_pos]
              _ = 0 := by ring
  calc
    (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
          ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0)
        = ∫ t in p..q, D t := by
          simpa [D, L, W, Gpow, Cder] using hconv
    _ = 0 := hD_zero


private lemma odd_cap_centroid_moment_at_zero {n : ℕ} {f : ℝ → ℝ}
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t) :
    (∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..0, t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))) =
      (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(f t), t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)) := by
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  have hinner : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      (∫ z in (-f t)..0, t * W t z) =
        (1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z := by
    intro t ht
    have hft_nonneg : 0 ≤ f t := hf_nonneg t ht
    have hg_cont : Continuous (fun z : ℝ => W t z) := by
      dsimp [W]
      continuity
    have hg_even : ∀ z : ℝ, W t (-z) = W t z := by
      intro z
      dsimp [W]
      have harg : f t ^ 2 - (-z) ^ 2 = f t ^ 2 - z ^ 2 := by ring
      rw [harg]
    have hhalf := (intervalIntegral_half_even hft_nonneg hg_cont hg_even).2
    calc
      (∫ z in (-f t)..0, t * W t z) = t * ∫ z in (-f t)..0, W t z := by
        rw [intervalIntegral.integral_const_mul]
      _ = t * ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), W t z) := by
        rw [hhalf]
        ring
      _ = (1 / 2 : ℝ) * (t * ∫ z in (-f t)..(f t), W t z) := by ring
      _ = (1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z := by
        rw [intervalIntegral.integral_const_mul]
  have hcongr : (∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..0, t * W t z) =
      ∫ t in (-1 : ℝ)..1, ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    exact hinner t htIcc
  calc
    (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, t * W t z)
        = ∫ t in (-1 : ℝ)..1, ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z) := hcongr
    _ = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), t * W t z := by
        rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(f t), t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)) := by
        simp [W]

private lemma odd_profile_cap_centroid_moment_eq {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1)
    (h_moment : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h s))),
            (t + s * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))) =
        (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(f t), t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)) := by
  classical
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  let A : ℝ → ℝ := fun r =>
    ∫ t in (-1 : ℝ)..1,
      ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))), (t + r * z) * W t z
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    profile_nonneg_Icc_general hab hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    cap_profile_measurable_of_smooth hab hf_support hf_cont hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) :=
    concaveOn_Icc_bounded hab hf_conc
  have hcont : ContinuousOn A (Set.Ici 0) := by
    intro r hr
    exact (odd_cap_centroid_moment_hasDerivAt (n := n) (f := f) (h := h)
      hn hf_nonneg hf_meas hf_bdd hh_cont r).continuousAt.continuousWithinAt
  have hderiv : ∀ r > 0, HasDerivAt A 0 r := by
    intro r hr
    have hd := odd_cap_centroid_moment_hasDerivAt (n := n) (f := f) (h := h)
      hn hf_nonneg hf_meas hf_bdd hh_cont r
    have hz := odd_cap_centroid_moment_deriv_eq_zero (n := n) hn (C := C)
      hf_support hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hxy hxy_inside h_moment h_center r hr
    simpa [A, W] using hd.congr_deriv hz
  have hconst : ∀ r > 0, A r = A 0 := const_on_Ioi_of_deriv_zero hderiv hcont
  have hA0 : A 0 = ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, t * W t z := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le hab] using ht
    have hf_nonneg_t : 0 ≤ f t := hf_nonneg t htIcc
    have hup : max (-f t) (min (f t) (0 * t + h 0)) = 0 := by
      rw [h0]
      simp [hf_nonneg_t]
    change (∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + h 0))),
        (t + 0 * z) * W t z) = ∫ z in (-f t)..0, t * W t z
    rw [hup]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  have hhalf := odd_cap_centroid_moment_at_zero (n := n) (f := f) hf_nonneg
  intro s hs
  calc
    (∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h s))),
          (t + s * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))
        = A s := by simp [A, W]
    _ = A 0 := hconst s hs
    _ = ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, t * W t z := hA0
    _ = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(f t), t * W t z := hhalf
    _ = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(f t), t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)) := by
        simp [W]


private lemma odd_inner_integral_min_eq_max {f L : ℝ} {φ : ℝ → ℝ}
    (hφ_zero : ∀ z ∈ Set.Icc (min f L) (-f), φ z = 0) :
    (∫ z in (-f)..(min f L), φ z) = ∫ z in (-f)..(max (-f) (min f L)), φ z := by
  by_cases hle : min f L ≤ -f
  · have hmax : max (-f) (min f L) = -f := max_eq_left hle
    rw [hmax]
    have hba : (∫ z in (-f)..(min f L), φ z) = -∫ z in Set.Ioc (min f L) (-f), φ z := by
      rw [intervalIntegral.integral_of_ge hle]
    have hzero : (∫ z in Set.Ioc (min f L) (-f), φ z) = 0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      filter_upwards [Measure.ae_ne volume (-f)] with z hzne hzmem
      have hzIcc : z ∈ Set.Icc (min f L) (-f) := Set.Ioc_subset_Icc_self hzmem
      exact hφ_zero z hzIcc
    rw [hba, hzero]
    simp
  · have hmax : max (-f) (min f L) = min f L := max_eq_right (le_of_lt (lt_of_not_ge hle))
    rw [hmax]


private lemma norm_odd_cap_zW_slice_integral_le {n : ℕ} {f h : ℝ → ℝ} {M : ℝ}
    (hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hM_nonneg : 0 ≤ M) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          z * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))‖ ≤
        M * (2 * M) * ((M ^ 2) ^ (n - 1) * M) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
  have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  let a : ℝ := -f t
  let b : ℝ := f t
  let U : ℝ := max a (min b (r * t + h r))
  let g : ℝ → ℝ := fun z => z * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))
  have ha_le_b : a ≤ b := by dsimp [a, b]; linarith
  have hU_mem : U ∈ Set.Icc a b := by
    dsimp [U]
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le ha_le_b (min_le_left _ _)
  have hUa : a ≤ U := hU_mem.1
  have hUb : U ≤ b := hU_mem.2
  have hg_bound : ∀ z ∈ Ι a U, ‖g z‖ ≤ M * ((M ^ 2) ^ (n - 1) * M) := by
    intro z hz
    have hzIoc : z ∈ Set.Ioc a U := by
      simpa [Set.uIoc_of_le hUa] using hz
    have hz_lower : -M ≤ z := by
      have ha_lower : -M ≤ a := by dsimp [a]; linarith
      exact le_trans ha_lower (le_of_lt hzIoc.1)
    have hz_upper : z ≤ M := by
      have hb_upper : b ≤ M := by dsimp [b]; exact hft_le
      exact le_trans (le_trans hzIoc.2 hUb) hb_upper
    have hz_abs : |z| ≤ M := abs_le.mpr ⟨hz_lower, hz_upper⟩
    have hG_nonneg : 0 ≤ f t ^ 2 - z ^ 2 := by
      have hz_le_f : z ≤ f t := le_trans hzIoc.2 hUb
      have hz_ge_negf : -f t ≤ z := le_of_lt hzIoc.1
      have h1 : 0 ≤ f t - z := sub_nonneg.mpr hz_le_f
      have h2 : 0 ≤ f t + z := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hG_le : f t ^ 2 - z ^ 2 ≤ M ^ 2 := by
      have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
      nlinarith [sq_nonneg z]
    have hpow : |(f t ^ 2 - z ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
      rw [abs_pow, abs_of_nonneg hG_nonneg]
      exact pow_le_pow_left₀ hG_nonneg hG_le (n - 1)
    have hsqrt : |Real.sqrt (f t ^ 2 - z ^ 2)| ≤ M := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (Real.sqrt_le_left hM_nonneg).2 hG_le
    have hW_le : |((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))| ≤
        (M ^ 2) ^ (n - 1) * M := by
      simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
    dsimp [g]
    simpa [abs_mul] using mul_le_mul hz_abs hW_le (abs_nonneg _) (by positivity)
  have hlen : |U - a| ≤ 2 * M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hUa)]
    calc U - a ≤ b - a := sub_le_sub hUb le_rfl
      _ = 2 * f t := by dsimp [a, b]; ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := U)
      (C := M * ((M ^ 2) ^ (n - 1) * M)) (f := g) hg_bound
  calc
    ‖∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        z * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))‖
        = ‖∫ z in a..U, g z‖ := by simp [a, b, U, g]
    _ ≤ (M * ((M ^ 2) ^ (n - 1) * M)) * |U - a| := hnorm
    _ ≤ (M * ((M ^ 2) ^ (n - 1) * M)) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = M * (2 * M) * ((M ^ 2) ^ (n - 1) * M) := by ring


private lemma norm_odd_cap_tW_slice_integral_le {n : ℕ} {f h : ℝ → ℝ} {M : ℝ}
    (hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hM_nonneg : 0 ≤ M) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))‖ ≤
        (2 * M) * ((M ^ 2) ^ (n - 1) * M) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
  have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  have ht_abs : |t| ≤ 1 := by
    exact abs_le.mpr ⟨htcc.1, by norm_num at htcc ⊢; exact htcc.2⟩
  let a : ℝ := -f t
  let b : ℝ := f t
  let U : ℝ := max a (min b (r * t + h r))
  let g : ℝ → ℝ := fun z => t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))
  have ha_le_b : a ≤ b := by dsimp [a, b]; linarith
  have hU_mem : U ∈ Set.Icc a b := by
    dsimp [U]
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le ha_le_b (min_le_left _ _)
  have hUa : a ≤ U := hU_mem.1
  have hUb : U ≤ b := hU_mem.2
  have hg_bound : ∀ z ∈ Ι a U, ‖g z‖ ≤ (M ^ 2) ^ (n - 1) * M := by
    intro z hz
    have hzIoc : z ∈ Set.Ioc a U := by
      simpa [Set.uIoc_of_le hUa] using hz
    have hz_le_f : z ≤ f t := le_trans hzIoc.2 hUb
    have hz_ge_negf : -f t ≤ z := le_of_lt hzIoc.1
    have hG_nonneg : 0 ≤ f t ^ 2 - z ^ 2 := by
      have h1 : 0 ≤ f t - z := sub_nonneg.mpr hz_le_f
      have h2 : 0 ≤ f t + z := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hG_le : f t ^ 2 - z ^ 2 ≤ M ^ 2 := by
      have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
      nlinarith [sq_nonneg z]
    have hpow : |(f t ^ 2 - z ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
      rw [abs_pow, abs_of_nonneg hG_nonneg]
      exact pow_le_pow_left₀ hG_nonneg hG_le (n - 1)
    have hsqrt : |Real.sqrt (f t ^ 2 - z ^ 2)| ≤ M := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (Real.sqrt_le_left hM_nonneg).2 hG_le
    have hW_le : |((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))| ≤
        (M ^ 2) ^ (n - 1) * M := by
      simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
    dsimp [g]
    simpa [abs_mul] using mul_le_mul ht_abs hW_le (abs_nonneg _) (by positivity)
  have hlen : |U - a| ≤ 2 * M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hUa)]
    calc U - a ≤ b - a := sub_le_sub hUb le_rfl
      _ = 2 * f t := by dsimp [a, b]; ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := U)
      (C := (M ^ 2) ^ (n - 1) * M) (f := g) hg_bound
  calc
    ‖∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))‖
        = ‖∫ z in a..U, g z‖ := by simp [a, b, U, g]
    _ ≤ ((M ^ 2) ^ (n - 1) * M) * |U - a| := hnorm
    _ ≤ ((M ^ 2) ^ (n - 1) * M) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = (2 * M) * ((M ^ 2) ^ (n - 1) * M) := by ring

lemma odd_cap_centroid_span {d : ℕ} [NeZero d] (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {C : ℝ} {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-1) 1 ∧ y s ∈ Set.Ioo (-1) 1)
    (h_moment : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0)
    (hvol : ∀ s : ℝ, 0 < s →
      let K : Set (EuclideanSpace ℝ (Fin d)) :=
        {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      MeasureTheory.volume.real (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}) =
        MeasureTheory.volume.real K / 2) :
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ∀ s : ℝ, 0 < s →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) +
          (EuclideanSpace.single (lastFin d) (1:ℝ))) := by
  classical
  intro K s hs
  let last : Fin d := lastFin d
  let e0 : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) (1:ℝ)
  let elast : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (lastFin d) (1:ℝ)
  let H : Set (EuclideanSpace ℝ (Fin d)) := {x | x (lastFin d) ≤ s * x 0 + h s}
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h s))
  let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
  have hdpos : 2 ≤ d := by omega
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    profile_nonneg_Icc_general hab hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    cap_profile_measurable_of_smooth hab hf_support hf_cont hf_left hf_right
  have hlast0_eq : (⟨d - 1, by omega⟩ : Fin d) = lastFin d := by
    ext; simp [lastFin]
  have hcap_body := body_of_revolution_cap_integrals (d := d) (n := n) (a := (-1 : ℝ)) (b := (1 : ℝ))
    (s := s) (h := h s) hdn hn hab hf_nonneg hf_meas
  rcases hcap_body with ⟨hVcap, hI0cap, hIlastcap, hmidcap⟩
  have hW_zero_of_le_neg : ∀ t, ∀ z : ℝ, z ≤ -f t → W t z = 0 := by
    intro t z hz
    dsimp [W]
    apply odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := z)
    · by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
      · exact hf_nonneg t ht
      · have hf0 : f t = 0 := by
          rw [Function.support_subset_iff'] at hf_support
          exact hf_support t ht
        rw [hf0]
    · intro hact
      linarith
  have hI0cap' : (∫ x in K ∩ H, x 0) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z := by
    have hset : K ∩ H = K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ s * x 0 + h s} := by
      ext x
      simp only [K, H, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hlast0_eq]
    rw [hset]
    have hbody0 := hI0cap
    -- hI0cap has min; convert to max pointwise
    have houter : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(min (f t) (s * t + h s)), t * W t z) =
        ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply odd_inner_integral_min_eq_max
      intro z hz
      have hz_le : z ≤ -f t := hz.2
      rw [hW_zero_of_le_neg t z hz_le]
      simp
    simpa [K, W, U, c, hlast0_eq] using hbody0.trans (congrArg (fun q : ℝ => c * q) houter)
  have hIlastcap' : (∫ x in K ∩ H, x (lastFin d)) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z := by
    have hset : K ∩ H = K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ s * x 0 + h s} := by
      ext x
      simp only [K, H, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hlast0_eq]
    rw [hset]
    have hbody := hIlastcap
    have houter : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(min (f t) (s * t + h s)), z * W t z) =
        ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply odd_inner_integral_min_eq_max
      intro z hz
      have hz_le : z ≤ -f t := hz.2
      rw [hW_zero_of_le_neg t z hz_le]
      simp
    simpa [K, W, U, c, hlast0_eq] using hbody.trans (congrArg (fun q : ℝ => c * q) houter)
  have hmidcap' : ∀ i : Fin d, i ≠ 0 → i ≠ lastFin d → (∫ x in K ∩ H, x i) = 0 := by
    intro i hi0 hilast
    have hset : K ∩ H = K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ s * x 0 + h s} := by
      ext x
      simp only [K, H, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hlast0_eq]
    rw [hset]
    have hilast0 : i ≠ (⟨d - 1, by omega⟩ : Fin d) := by
      intro h
      apply hilast
      simpa [hlast0_eq] using h
    simpa [K, W, U, c] using hmidcap i hi0 hilast0

  -- total body integrals with a large halfspace containing K
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) :=
    concaveOn_Icc_bounded hab hf_conc
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  let R : ℝ := M + 1
  have hR_gt : M < R := by dsimp [R]; linarith
  have hf_le_R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ R := by
    intro t ht
    exact le_of_lt (lt_of_le_of_lt (hf_le_M t ht) hR_gt)
  have hK_subset_R : K ⊆ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R} := by
    simpa [K] using K_subset_H_large_general (d := d) (a := -1) (b := 1) (f := f) (M := M) (R := R)
      hab hdpos hR_gt hf_nonneg hf_le_M
  have hK_inter_R : K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R} = K := by
    exact Set.inter_eq_left.mpr hK_subset_R
  have htotal_body := body_of_revolution_cap_integrals (d := d) (n := n) (a := (-1 : ℝ)) (b := (1 : ℝ))
    (s := 0) (h := R) hdn hn hab hf_nonneg hf_meas
  rcases htotal_body with ⟨hVtot0, hI0tot0, hIlasttot0, hmidtot0⟩
  have hI0tot0' : (∫ x in K, x 0) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) R)), t * W t z := by
    rw [← hK_inter_R]
    have houter : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(min (f t) (0 * t + R)), t * W t z) =
        ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), t * W t z := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
        simpa [Set.uIcc_of_le hab] using ht
      have hmin : min (f t) (0 * t + R) = f t := by
        simp [min_eq_left (hf_le_R t htIcc)]
      have hmax : max (-f t) (min (f t) (0 * t + R)) = f t := by
        rw [hmin]
        exact max_eq_right (by linarith [hf_nonneg t htIcc])
      change (∫ z in (-f t)..(min (f t) (0 * t + R)), t * W t z) =
        ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), t * W t z
      rw [hmax, hmin]
    simpa [K, W, c] using hI0tot0.trans (congrArg (fun q : ℝ => c * q) houter)
  have hIlasttot0' : (∫ x in K, x (⟨d - 1, by omega⟩ : Fin d)) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z := by
    rw [← hK_inter_R]
    have houter : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(min (f t) (0 * t + R)), z * W t z) =
        ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), z * W t z := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
        simpa [Set.uIcc_of_le hab] using ht
      have hmin : min (f t) (0 * t + R) = f t := by
        simp [min_eq_left (hf_le_R t htIcc)]
      have hmax : max (-f t) (min (f t) (0 * t + R)) = f t := by
        rw [hmin]
        exact max_eq_right (by linarith [hf_nonneg t htIcc])
      change (∫ z in (-f t)..(min (f t) (0 * t + R)), z * W t z) =
        ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), z * W t z
      rw [hmax, hmin]
    simpa [K, W, c] using hIlasttot0.trans (congrArg (fun q : ℝ => c * q) houter)
  have hIlasttot : (∫ x in K, x (lastFin d)) = 0 := by
    have h := hIlasttot0'
    have hinner : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        (∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z) = 0 := by
      intro t ht
      have hmax : max (-f t) (min (f t) R) = f t := by
        exact max_min_eq_of_nonneg_le (hf_nonneg t ht) (hf_le_R t ht)
      rw [hmax]
      have hodd : (∫ z in (-f t)..(f t), z * W t z) = 0 := by
        let g : ℝ → ℝ := fun z => z * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))
        have hcomp := intervalIntegral.integral_comp_neg (a := -f t) (b := f t) (f := g)
        have hneg : (∫ z in (-f t)..(f t), g (-z)) = - ∫ z in (-f t)..(f t), g z := by
          have hfun : (fun z => g (-z)) = (fun z => - g z) := by
            ext z
            dsimp [g]
            ring_nf
          rw [hfun, intervalIntegral.integral_neg]
        have hsame : (∫ z in (-f t)..(f t), g (-z)) = ∫ z in (-f t)..(f t), g z := by
          simpa [g] using hcomp
        linarith
      simpa [W] using hodd
    have hI0tot_full : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z) = 0 := by
      calc
        (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z)
            = ∫ t in (-1 : ℝ)..1, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              intro t ht
              have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
                simpa [Set.uIcc_of_le hab] using ht
              change (∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z) = (0 : ℝ)
              rw [hinner t htIcc]
        _ = 0 := by simp
    rw [← hlast0_eq]
    rw [hIlasttot0']
    rw [hI0tot_full]
    simp
  have hmidtot : ∀ i : Fin d, i ≠ 0 → i ≠ lastFin d → (∫ x in K, x i) = 0 := by
    intro i hi0 hilast
    have hilast0 : i ≠ (⟨d - 1, by omega⟩ : Fin d) := by
      intro h
      apply hilast
      simpa [hlast0_eq] using h
    rw [← hK_inter_R]
    simpa [K, W, c] using hmidtot0 i hi0 hilast0

  -- moment relation from the odd centroid moment lemma
  have hmoment : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), (t + s * z) * W t z) =
      (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), t * W t z := by
    simpa [W, U] using
      (odd_profile_cap_centroid_moment_eq (n := n) hn (C := C) hf_support hf_cont hf_conc hf_left hf_right hf_pos
        hh_cont h0 hxy hxy_inside h_moment h_center s hs)

  have hI0tot_full : (∫ x in K, x 0) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), t * W t z := by
    rw [hI0tot0']
    apply congrArg (fun q : ℝ => c * q)
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le hab] using ht
    have hmax : max (-f t) (min (f t) R) = f t := by
      exact max_min_eq_of_nonneg_le (hf_nonneg t htIcc) (hf_le_R t htIcc)
    change (∫ z in (-f t)..(max (-f t) (min (f t) R)), t * W t z) =
      ∫ z in (-f t)..(f t), t * W t z
    rw [hmax]

  have hA_int : IntervalIntegrable (fun t => ∫ z in (-f t)..(U t), t * W t z) volume (-1 : ℝ) 1 := by
    rw [intervalIntegrable_iff]
    have hL_meas : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU_meas : Measurable U := by
      dsimp [U]
      fun_prop
    have hF_meas : Measurable (Function.uncurry (fun t z : ℝ => t * W t z)) := by
      dsimp [W]
      fun_prop
    have hA_ae : AEStronglyMeasurable (fun t => ∫ z in (-f t)..(U t), t * W t z) volume := by
      exact aeStronglyMeasurable_intervalIntegral_param hL_meas hU_meas hF_meas
    let Wbase : ℝ := (M ^ 2) ^ (n - 1) * M
    let Bint : ℝ := (2 * M) * Wbase
    have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint, Wbase]; positivity
    have hbnd' := norm_odd_cap_tW_slice_integral_le (n := n) (f := f) (h := h) (M := M)
      hf_le_M hf_nonneg (le_of_lt hMpos) s
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)),
        ‖∫ z in (-f t)..(U t), t * W t z‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      intro htIoc
      have hbound_t := ht htIoc
      simpa [U, Bint, Wbase] using hbound_t
    have hvol_fin : volume (Set.uIoc (-1 : ℝ) 1) < ⊤ := by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_lt_top
    have hIntOn : IntegrableOn (fun t => ∫ z in (-f t)..(U t), t * W t z) (Set.uIoc (-1 : ℝ) 1) volume := by
      exact IntegrableOn.of_bound hvol_fin hA_ae.restrict Bint h_bound
    exact hIntOn
  have hB_int : IntervalIntegrable (fun t => ∫ z in (-f t)..(U t), z * W t z) volume (-1 : ℝ) 1 := by
    rw [intervalIntegrable_iff]
    have hL_meas : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU_meas : Measurable U := by
      dsimp [U]
      fun_prop
    have hF_meas : Measurable (Function.uncurry (fun t z : ℝ => z * W t z)) := by
      dsimp [W]
      fun_prop
    have hB_ae : AEStronglyMeasurable (fun t => ∫ z in (-f t)..(U t), z * W t z) volume := by
      exact aeStronglyMeasurable_intervalIntegral_param hL_meas hU_meas hF_meas
    let Wbase : ℝ := (M ^ 2) ^ (n - 1) * M
    let Bint : ℝ := M * (2 * M) * Wbase
    have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint, Wbase]; positivity
    have hbnd' := norm_odd_cap_zW_slice_integral_le (n := n) (f := f) (h := h) (M := M)
      hf_le_M hf_nonneg (le_of_lt hMpos) s
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)),
        ‖∫ z in (-f t)..(U t), z * W t z‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      intro htIoc
      have htIoc' : t ∈ Set.Ioc (-1 : ℝ) 1 := by
        simpa [Set.uIoc_of_le hab] using htIoc
      have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc'
      have hbound_t := ht htIoc
      simpa [U, Bint, Wbase] using hbound_t
    have hvol_fin : volume (Set.uIoc (-1 : ℝ) 1) < ⊤ := by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_lt_top
    have hIntOn : IntegrableOn (fun t => ∫ z in (-f t)..(U t), z * W t z) (Set.uIoc (-1 : ℝ) 1) volume := by
      exact IntegrableOn.of_bound hvol_fin hB_ae.restrict Bint h_bound
    exact hIntOn
  have hinner_add : ∀ t : ℝ,
      (∫ z in (-f t)..(U t), t * W t z) + s * (∫ z in (-f t)..(U t), z * W t z) =
        ∫ z in (-f t)..(U t), (t + s * z) * W t z := by
    intro t
    have hc1 : IntervalIntegrable (fun z => t * W t z) volume (-f t) (U t) := by
      have hcont : Continuous (fun z => t * W t z) := by
        dsimp [W]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hc2 : IntervalIntegrable (fun z => z * W t z) volume (-f t) (U t) := by
      have hcont : Continuous (fun z => z * W t z) := by
        dsimp [W]
        fun_prop
      exact hcont.intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul]
    have hc2s : IntervalIntegrable (fun z => s * (z * W t z)) volume (-f t) (U t) :=
      hc2.const_mul s
    rw [← intervalIntegral.integral_add hc1 hc2s]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  have houter_add : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z) +
        s * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z) =
      ∫ t in (-1 : ℝ)..1, (∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
    rw [← intervalIntegral.integral_const_mul]
    have hB_smul : IntervalIntegrable (fun t => s * (∫ z in (-f t)..(U t), z * W t z)) volume (-1 : ℝ) 1 :=
      hB_int.const_mul s
    rw [← intervalIntegral.integral_add hA_int hB_smul]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hinner_add t
  have hcap_moment : (∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d)) =
      c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
    calc
      (∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d))
          = c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z) +
              s * (c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z)) := by
            rw [hI0cap', hIlastcap']
      _ = c * ((∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z) +
              s * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z)) := by ring
      _ = c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
            rw [houter_add]
  have hrelation : (∫ x in K, x 0) = 2 * ((∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d))) := by
    rw [hI0tot_full, hcap_moment, hmoment]
    ring
  have hvolK : volume.real K = volume.real K := rfl
  have hvolcap : volume.real (K ∩ H) = volume.real K / 2 := by
    simpa [K, H] using hvol s hs
  let D : EuclideanSpace ℝ (Fin d) := (⨍ x in K, x) - (⨍ x in (K ∩ H), x)
  have hDav : D = (volume.real K)⁻¹ • (∫ x in K, x) - (volume.real (K ∩ H))⁻¹ • (∫ x in K ∩ H, x) := by
    dsimp [D]
    rw [setAverage_eq, setAverage_eq]
  have hD_scale : D = (volume.real K)⁻¹ • ((∫ x in K, x) - 2 • (∫ x in K ∩ H, x)) := by
    rw [hDav, hvolcap]
    module
  have hf_cont_inf : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1) := hf_cont
  have hK_meas : MeasurableSet K := by
    simpa [K] using body_of_revolution_measurable (d := d) (R₁ := 1) (R₂ := 1) (f := f)
      hf_support hf_cont_inf hf_left hf_right
  have hK_bdd : Bornology.IsBounded K := by
    simpa [K] using body_of_revolution_bounded (d := d) (R₁ := 1) (R₂ := 1) (f := f)
      hf_conc hf_left hf_right
  have hH_meas : MeasurableSet H := by
    dsimp [H]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hC_meas : MeasurableSet (K ∩ H) := hK_meas.inter hH_meas
  have hC_bdd : Bornology.IsBounded (K ∩ H) := hK_bdd.subset (by intro x hx; exact hx.1)
  have hAvg0K : ((⨍ x in K, x) 0) = (volume.real K)⁻¹ * (∫ x in K, x 0) := by
    rw [setAverage_id_apply K 0 hK_meas hK_bdd]
    rw [setAverage_eq]
    simp [smul_eq_mul]
  have hAvg0C : ((⨍ x in K ∩ H, x) 0) = (volume.real (K ∩ H))⁻¹ * (∫ x in K ∩ H, x 0) := by
    rw [setAverage_id_apply (K ∩ H) 0 hC_meas hC_bdd]
    rw [setAverage_eq]
    simp [smul_eq_mul]
  have hAvgLastK : ((⨍ x in K, x) (lastFin d)) = (volume.real K)⁻¹ * (∫ x in K, x (lastFin d)) := by
    rw [setAverage_id_apply K (lastFin d) hK_meas hK_bdd]
    rw [setAverage_eq]
    simp [smul_eq_mul]
  have hAvgLastC : ((⨍ x in K ∩ H, x) (lastFin d)) = (volume.real (K ∩ H))⁻¹ * (∫ x in K ∩ H, x (lastFin d)) := by
    rw [setAverage_id_apply (K ∩ H) (lastFin d) hC_meas hC_bdd]
    rw [setAverage_eq]
    simp [smul_eq_mul]
  let lam : ℝ := -2 * (volume.real K)⁻¹ * (∫ x in K ∩ H, x (lastFin d))
  have hDlast : D (lastFin d) = lam := by
    dsimp [D, lam]
    rw [hAvgLastK, hAvgLastC]
    rw [hIlasttot]
    rw [hvolcap]
    field_simp
    ring
  have hD0 : D 0 = -s * lam := by
    dsimp [D, lam]
    rw [hAvg0K, hAvg0C]
    rw [hvolcap]
    rw [hrelation]
    field_simp
    ring
  have hDmid : ∀ i : Fin d, i ≠ 0 → i ≠ lastFin d → D i = 0 := by
    intro i hi0 hilast
    dsimp [D]
    rw [setAverage_id_apply K i hK_meas hK_bdd]
    rw [setAverage_id_apply (K ∩ H) i hC_meas hC_bdd]
    rw [setAverage_eq, setAverage_eq]
    simp [smul_eq_mul]
    rw [hmidtot i hi0 hilast, hmidcap' i hi0 hilast]
    rw [hvolcap]
    field_simp
    ring
  have hmem := mem_span_e0_elast hdpos s lam hD0 hDlast hDmid
  -- match target's index and vector
  have hlast_eq : (⟨d - 1, by omega⟩ : Fin d) = lastFin d := by
    ext; simp [lastFin]
  simpa [D, H, hlast_eq, last] using hmem

end Work.OddCaps
