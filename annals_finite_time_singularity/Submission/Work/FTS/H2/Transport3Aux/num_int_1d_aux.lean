import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.Transport3Aux.sin_weight_hardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary estimates for `num_int_1d`

This file collects the one-dimensional analytic material used by the proof of
`Work.FTS.H2.Transport3Aux.num_int_1d`:

* `hardy_power_weak` : the weighted Hardy inequality with a boundary term, stated for a
  function which is only assumed continuous on `[0,b]`, differentiable on `(0,b)` with
  `deriv f` bounded there (no `C¹`-on-the-closed-interval hypothesis).  The proof is the
  one of `Submission/Work/FTS/H2/Transport3Aux/power_hardy_boundary` with the smoothness
  hypothesis replaced by the weaker ones used here.
* `sq_integral_le` : Cauchy–Schwarz for interval integrals, proved by completing the square.
* `young_pt`, `good_weight_pt`, `bad_conv` : pointwise `sin (2θ)`-weight comparisons.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option maxHeartbeats 1000000

/-! ## 1. The weighted Hardy inequality with a boundary term, weak hypotheses -/

theorem hardy_power_weak {a b C : ℝ} (ha : -1 < a) (hb : 0 < b) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 b))
    (hder : ∀ t ∈ Set.Ioo 0 b, HasDerivAt f (deriv f t) t)
    (hbdd : ∀ t ∈ Set.Ioo 0 b, |deriv f t| ≤ C) :
    (∫ t in (0 : ℝ)..b, f t ^ 2 * t ^ a)
      ≤ 4 / (a + 1) ^ 2 * (∫ t in (0 : ℝ)..b, (deriv f t) ^ 2 * t ^ (a + 2))
        + 2 / (a + 1) * b ^ (a + 1) * (f b) ^ 2 := by
  have ha1 : 0 < a + 1 := by linarith
  -- ## Step 1: the two bounds on `f` and `deriv f` on `(0,b)`
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max C₁ (max C 0) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hfK : ∀ t ∈ Set.Ioo 0 b, |f t| ≤ K := by
    intro t ht
    have h := hC₁ t ⟨ht.1.le, ht.2.le⟩
    simp only [Real.norm_eq_abs] at h
    rw [hKdef]
    exact le_trans h (le_max_left _ _)
  have hdK : ∀ t ∈ Set.Ioo 0 b, |deriv f t| ≤ K := by
    intro t ht
    rw [hKdef]
    exact le_trans (hbdd t ht) (le_trans (le_max_left _ _) (le_max_right _ _))
  -- ## Step 2: the two limits at `0⁺` and `b⁻`
  have htend0 : Tendsto (fun t : ℝ => f t ^ 2 * t ^ (a + 1)) (𝓝[>] 0) (𝓝 0) := by
    have hmem : Set.Ioo 0 b ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin_iff_eventually]
      filter_upwards [Iio_mem_nhds hb] with t ht h0t
      exact ⟨h0t, ht⟩
    have hpoly : Tendsto (fun t : ℝ => t ^ (a + 1)) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => t ^ (a + 1)) 0 :=
        Real.continuousAt_rpow_const 0 (a + 1) (Or.inr ha1.le)
      have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
      rwa [Real.zero_rpow ha1.ne'] at h2
    have hg : Tendsto (fun t : ℝ => K ^ 2 * t ^ (a + 1)) (𝓝[>] 0) (𝓝 0) := by
      have h2 := (tendsto_const_nhds (x := K ^ 2) (f := 𝓝[>] (0 : ℝ))).mul hpoly
      simpa using h2
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [hmem] with t ht
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _)
    · filter_upwards [hmem] with t ht
      have h1 : f t ^ 2 ≤ K ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hK0]
        exact hfK t ht
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le _)
  have htendb : Tendsto (fun t : ℝ => f t ^ 2 * t ^ (a + 1)) (𝓝[<] b)
      (𝓝 (f b ^ 2 * b ^ (a + 1))) := by
    have hle : 𝓝[<] b ≤ 𝓝[Set.Icc 0 b] b := by
      rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_eventually]
      filter_upwards [Ioi_mem_nhds (show b / 2 < b by linarith)] with t ht hlt
      simp only [Set.mem_Ioi, Set.mem_Iio, Set.mem_Icc] at ht hlt ⊢
      exact ⟨by linarith, le_of_lt hlt⟩
    have hfb : Tendsto f (𝓝[<] b) (𝓝 (f b)) :=
      (hcont.continuousWithinAt ⟨hb.le, le_refl b⟩).mono_left hle
    have hft : Tendsto (fun t : ℝ => f t ^ 2) (𝓝[<] b) (𝓝 (f b ^ 2)) := hfb.pow 2
    have hrp : Tendsto (fun t : ℝ => t ^ (a + 1)) (𝓝[<] b) (𝓝 (b ^ (a + 1))) :=
      (Real.continuousAt_rpow_const b (a + 1) (Or.inl hb.ne')).tendsto.mono_left
        (nhdsWithin_le_nhds (a := b) (s := Set.Iio b))
    exact hft.mul hrp
  -- ## Step 3: integrability of the three integrands
  have hcont1 : ContinuousOn (fun t : ℝ => f t ^ 2 * t ^ a) (Set.Ioo 0 b) :=
    ((hcont.mono Set.Ioo_subset_Icc_self).pow 2).mul
      (continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne'))
  have hmeas2 : AEStronglyMeasurable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (a + 2))
      (volume.restrict (Set.Ioo 0 b)) :=
    (((measurable_deriv f).pow_const 2).aestronglyMeasurable).mul
      ((continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')).aestronglyMeasurable
        measurableSet_Ioo)
  have hmeas3 : AEStronglyMeasurable (fun t : ℝ => f t * deriv f t * t ^ (a + 1))
      (volume.restrict (Set.Ioo 0 b)) :=
    (((hcont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo).mul
      (measurable_deriv f).aestronglyMeasurable).mul
      ((continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')).aestronglyMeasurable
        measurableSet_Ioo)
  have key : ∀ {G : ℝ → ℝ} {r D : ℝ}, -1 < r → 0 ≤ D →
      AEStronglyMeasurable G (volume.restrict (Set.Ioo 0 b)) →
      (∀ t ∈ Set.Ioo 0 b, |G t| ≤ D * t ^ r) → IntervalIntegrable G volume 0 b := by
    intro G r D hr hD hmeas hbound
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    have hg : IntegrableOn (fun t : ℝ => D * t ^ r) (Set.Ioo 0 b) volume := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1
        ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := b) hr).const_mul D)
    refine Integrable.mono' hg hmeas ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbound)]
      with t ht
    simpa only [Real.norm_eq_abs] using ht
  have hIp1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 * t ^ a) volume 0 b :=
    key ha (sq_nonneg K) (hcont1.aestronglyMeasurable measurableSet_Ioo) (fun t ht => by
      have h1 : f t ^ 2 ≤ K ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hK0]
        exact hfK t ht
      rw [abs_mul, abs_of_nonneg (sq_nonneg (f t)),
        abs_of_nonneg (Real.rpow_nonneg ht.1.le a)]
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le a))
  have hIp2 : IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (a + 2)) volume 0 b :=
    key (by linarith : -1 < a + 2) (sq_nonneg K) hmeas2 (fun t ht => by
      have h1 : (deriv f t) ^ 2 ≤ K ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hK0]
        exact hdK t ht
      rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f t)),
        abs_of_nonneg (Real.rpow_nonneg ht.1.le (a + 2))]
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le (a + 2)))
  have hIp3 : IntervalIntegrable (fun t : ℝ => f t * deriv f t * t ^ (a + 1)) volume 0 b :=
    key (by linarith : -1 < a + 1) (sq_nonneg K) hmeas3 (fun t ht => by
      have h1 : |f t| * |deriv f t| ≤ K ^ 2 := by
        calc |f t| * |deriv f t| ≤ K * K :=
              mul_le_mul (hfK t ht) (hdK t ht) (abs_nonneg _) hK0
          _ = K ^ 2 := by ring
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le (a + 1))]
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le (a + 1)))
  -- ## Step 4: notation
  set A : ℝ := ∫ t in (0 : ℝ)..b, f t ^ 2 * t ^ a with hAdef
  set B : ℝ := ∫ t in (0 : ℝ)..b, (deriv f t) ^ 2 * t ^ (a + 2) with hBdef
  set S : ℝ := ∫ t in (0 : ℝ)..b, f t * deriv f t * t ^ (a + 1) with hSdef
  set L : ℝ := ∫ t in (0 : ℝ)..b, |f t * deriv f t * t ^ (a + 1)| with hLdef
  -- ## Step 5: the fundamental theorem of calculus for `φ t = f t ^ 2 * t ^ (a+1)`
  have hφderiv : ∀ x ∈ Set.Ioo 0 b, HasDerivAt (fun s : ℝ => f s ^ 2 * s ^ (a + 1))
      (2 * (f x * deriv f x * x ^ (a + 1)) + (a + 1) * (f x ^ 2 * x ^ a)) x := by
    intro x hx
    have hd : HasDerivAt f (deriv f x) x := hder x hx
    have h1 : HasDerivAt (fun s : ℝ => f s ^ 2) (2 * f x ^ 1 * deriv f x) x := hd.pow 2
    have h2 : HasDerivAt (fun s : ℝ => s ^ (a + 1)) ((a + 1) * x ^ ((a + 1) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')
    have h3 := h1.mul h2
    rw [show (a + 1) - 1 = a by ring] at h3
    refine h3.congr_deriv ?_
    ring
  have hφint : IntervalIntegrable
      (fun t : ℝ => 2 * (f t * deriv f t * t ^ (a + 1)) + (a + 1) * (f t ^ 2 * t ^ a))
      volume 0 b :=
    (hIp3.const_mul 2).add (hIp1.const_mul (a + 1))
  have hFTC : ∫ t in (0 : ℝ)..b,
      (2 * (f t * deriv f t * t ^ (a + 1)) + (a + 1) * (f t ^ 2 * t ^ a))
      = f b ^ 2 * b ^ (a + 1) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hb hφderiv hφint
      htend0 htendb
    rwa [sub_zero] at h
  have hsplit : (∫ t in (0 : ℝ)..b,
      (2 * (f t * deriv f t * t ^ (a + 1)) + (a + 1) * (f t ^ 2 * t ^ a)))
      = 2 * S + (a + 1) * A := by
    rw [intervalIntegral.integral_add (hIp3.const_mul 2) (hIp1.const_mul (a + 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- ## Step 6: the identity `(a+1) A = f b ^ 2 * b ^ (a+1) - 2 S`
  have hAB : (a + 1) * A = f b ^ 2 * b ^ (a + 1) - 2 * S := by
    rw [hsplit] at hFTC
    linarith
  -- ## Step 7: the weighted arithmetic--geometric mean inequality
  have hpt : ∀ t ∈ Set.Ioo 0 b,
      2 * |f t * deriv f t * t ^ (a + 1)|
        ≤ (a + 1) / 2 * (f t ^ 2 * t ^ a)
          + 2 / (a + 1) * ((deriv f t) ^ 2 * t ^ (a + 2)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have hta : 0 ≤ t ^ a := Real.rpow_nonneg ht0.le a
    have hpow1 : t ^ (a + 1) = t ^ a * t := by
      rw [Real.rpow_add ht0 a 1, Real.rpow_one]
    have hpow2 : t ^ (a + 2) = t ^ a * t ^ 2 := by
      rw [Real.rpow_add ht0 a 2, Real.rpow_two]
    have hL : |f t * deriv f t * (t ^ a * t)| = (|f t| * |deriv f t| * t) * t ^ a := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hta, abs_of_pos ht0]
      ring
    have hkey : 4 * (a + 1) * (|f t| * |deriv f t| * t)
        ≤ (a + 1) ^ 2 * f t ^ 2 + 4 * (deriv f t) ^ 2 * t ^ 2 := by
      have htwo := two_mul_le_add_sq ((a + 1) * |f t|) (2 * |deriv f t| * t)
      have hfa : |f t| ^ 2 = f t ^ 2 := sq_abs (f t)
      have hga : |deriv f t| ^ 2 = (deriv f t) ^ 2 := sq_abs (deriv f t)
      nlinarith [htwo, hfa, hga]
    have hred : 2 * (|f t| * |deriv f t| * t)
        ≤ (a + 1) / 2 * f t ^ 2 + 2 / (a + 1) * ((deriv f t) ^ 2 * t ^ 2) := by
      have hc : (0 : ℝ) < 2 * (a + 1) := by linarith
      refine le_of_mul_le_mul_right ?_ hc
      have h1 : ((a + 1) / 2 * f t ^ 2 + 2 / (a + 1) * ((deriv f t) ^ 2 * t ^ 2))
          * (2 * (a + 1)) = (a + 1) ^ 2 * f t ^ 2 + 4 * (deriv f t) ^ 2 * t ^ 2 := by
        field_simp
        ring
      have h2 : 2 * (|f t| * |deriv f t| * t) * (2 * (a + 1))
          = 4 * (a + 1) * (|f t| * |deriv f t| * t) := by ring
      rw [h1, h2]
      exact hkey
    rw [hpow1, hpow2, hL]
    have hmul := mul_le_mul_of_nonneg_right hred hta
    nlinarith [hmul]
  -- ## Step 8: integrate the pointwise bound
  have hIL : IntervalIntegrable (fun t : ℝ => 2 * |f t * deriv f t * t ^ (a + 1)|)
      volume 0 b := hIp3.abs.const_mul 2
  have hIR : IntervalIntegrable (fun t : ℝ =>
      (a + 1) / 2 * (f t ^ 2 * t ^ a) + 2 / (a + 1) * ((deriv f t) ^ 2 * t ^ (a + 2)))
      volume 0 b :=
    (hIp1.const_mul ((a + 1) / 2)).add (hIp2.const_mul (2 / (a + 1)))
  have hAMGM : 2 * L ≤ (a + 1) / 2 * A + 2 / (a + 1) * B := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hb.le hIL hIR hpt
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hIp1.const_mul ((a + 1) / 2))
        (hIp2.const_mul (2 / (a + 1))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  have hSL : |S| ≤ L := by
    rw [hSdef, hLdef]
    exact intervalIntegral.abs_integral_le_integral_abs hb.le
  -- ## Step 9: finish
  have hstep : (a + 1) / 2 * A ≤ f b ^ 2 * b ^ (a + 1) + 2 / (a + 1) * B := by
    have h1 : -2 * S ≤ 2 * L := by
      have h2 := neg_abs_le S
      linarith
    nlinarith [hAB, h1, hAMGM]
  have hfin : A ≤ 2 / (a + 1) * (f b ^ 2 * b ^ (a + 1)) + 4 / (a + 1) ^ 2 * B := by
    have hc : (0 : ℝ) < (a + 1) / 2 := by linarith
    have h1 : A * ((a + 1) / 2) ≤ f b ^ 2 * b ^ (a + 1) + 2 / (a + 1) * B := by
      linarith
    have h2 := (le_div_iff₀ hc).2 h1
    have h3 : (f b ^ 2 * b ^ (a + 1) + 2 / (a + 1) * B) / ((a + 1) / 2)
        = 2 / (a + 1) * (f b ^ 2 * b ^ (a + 1)) + 4 / (a + 1) ^ 2 * B := by
      field_simp
      ring
    rw [h3] at h2
    exact h2
  have hgoal : 2 / (a + 1) * (f b ^ 2 * b ^ (a + 1)) + 4 / (a + 1) ^ 2 * B
      = 4 / (a + 1) ^ 2 * B + 2 / (a + 1) * b ^ (a + 1) * (f b) ^ 2 := by
    ring
  linarith [hfin, hgoal]

/-! ## 2. Cauchy–Schwarz for interval integrals (by completing the square) -/

theorem sq_integral_le {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp
  · have hlt : 0 < b - a := by linarith
    set c : ℝ := (∫ x in a..b, g x) / (b - a) with hc
    have hconst : (∫ _x in a..b, c ^ 2) = (b - a) * c ^ 2 := by
      rw [intervalIntegral.integral_const]; simp
    have hsq : (∫ x in a..b, (g x - c) ^ 2) = (∫ x in a..b, g x ^ 2) - 2 * c * (∫ x in a..b, g x)
        + (b - a) * c ^ 2 := by
      have h1 : (fun x : ℝ => (g x - c) ^ 2)
          = fun x : ℝ => g x ^ 2 - 2 * c * g x + c ^ 2 := by
        funext x; ring
      rw [h1]
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_sub]
        · rw [intervalIntegral.integral_const_mul, hconst]
        · exact hg2
        · exact hg.const_mul (2 * c)
      · exact hg2.sub (hg.const_mul (2 * c))
      · exact intervalIntegrable_const
    have hnn : 0 ≤ ∫ x in a..b, (g x - c) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hkey : 0 ≤ (∫ x in a..b, g x ^ 2) - 2 * c * (∫ x in a..b, g x) + (b - a) * c ^ 2 := by
      rw [← hsq]; exact hnn
    have hmain : (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
      have hmult : (∫ x in a..b, g x) ^ 2 = (b - a) * (2 * c * (∫ x in a..b, g x) - (b - a) * c ^ 2) := by
        rw [hc]; field_simp; ring
      nlinarith [hkey, hmult, hlt]
    exact hmain

/-! ## 3. Pointwise weight comparisons -/

/-- Pointwise Young inequality: the integrand of `num_int_1d` is dominated by the two weighted
terms which appear on the right hand side. -/
theorem young_pt {α s x y : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |x| * |y| * (α + s) * s ^ (α/10)
      ≤ (1/2) * (x^2 * (α+s)^2 * s^(3*(α/10) - 1) + y^2 * s^(1 - α/10)) := by
  have hβ : 0 < α/10 := by linarith
  have hβ' : 1 - α/10 ≠ 0 := by intro h; linarith
  have hβ'' : 3*(α/10) - 1 ≠ 0 := by intro h; linarith
  rcases eq_or_lt_of_le hs0 with h | h
  · subst h
    simp only [Real.zero_rpow hβ.ne', Real.zero_rpow hβ', Real.zero_rpow hβ'', mul_zero, add_zero]
    positivity
  · have hspos : 0 < s := h
    have hpow : s ^ (α/10) = s ^ ((3*(α/10) - 1)/2) * s ^ ((1 - α/10)/2) := by
      rw [← Real.rpow_add hspos]
      congr 1
      ring
    have hr1 : (s^((3*(α/10)-1)/2))^2 = s^(3*(α/10)-1) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hspos)]
      congr 1
      ring
    have hr2 : (s^((1-α/10)/2))^2 = s^(1-α/10) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hspos)]
      congr 1
      ring
    have hua : (|x| * (α + s) * s^((3*(α/10)-1)/2))^2 = x^2 * (α+s)^2 * s^(3*(α/10)-1) := by
      calc (|x| * (α + s) * s^((3*(α/10)-1)/2))^2
          = |x|^2 * (α+s)^2 * (s^((3*(α/10)-1)/2))^2 := by ring
        _ = x^2 * (α+s)^2 * s^(3*(α/10)-1) := by rw [sq_abs, hr1]
    have hva : (|y| * s^((1-α/10)/2))^2 = y^2 * s^(1-α/10) := by
      calc (|y| * s^((1-α/10)/2))^2 = |y|^2 * (s^((1-α/10)/2))^2 := by ring
        _ = y^2 * s^(1-α/10) := by rw [sq_abs, hr2]
    have huv : (|x| * (α+s) * s^((3*(α/10)-1)/2)) * (|y| * s^((1-α/10)/2))
        = |x| * |y| * (α+s) * s^(α/10) := by
      rw [hpow]
      ring
    have huv2 : 2 * (|x| * (α+s) * s^((3*(α/10)-1)/2)) * (|y| * s^((1-α/10)/2))
        = 2 * (|x| * |y| * (α+s) * s^(α/10)) := by rw [mul_assoc, huv]
    have h2 := two_mul_le_add_sq (|x| * (α+s) * s^((3*(α/10)-1)/2)) (|y| * s^((1-α/10)/2))
    rw [huv2, hua, hva] at h2
    linarith [h2]

/-- On the region `sin α ≤ s ≤ 1` the weight `(α+s)^2 s^(3α/10-1)` is dominated by `8 s^{-η}`. -/
theorem good_weight_pt {α s : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hs0 : Real.sin α ≤ s)
    (hs1 : s ≤ 1) :
    (α + s)^2 * s^(3*(α/10) - 1) ≤ 8 * s^(-(Work.Spaces.eta)) := by
  have hαπ : α < Real.pi := by linarith [Real.pi_gt_three]
  have hsinα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have hspos : 0 < s := lt_of_lt_of_le hsinα hs0
  have hsnn : 0 ≤ s := le_of_lt hspos
  have hexp : 3*(α/10) - 1 + Work.Spaces.eta = 3*(α/10) - 1/100 := by
    unfold Work.Spaces.eta; ring
  have key : (α+s)^2 * s^(3*(α/10) - 1 + Work.Spaces.eta) ≤ 8 := by
    rw [hexp]
    rcases lt_or_ge s α with h | h
    · -- s < α : use `(α+s)^2 ≤ 4α^2`
      have h1 : (α+s)^2 ≤ 4*α^2 := by nlinarith
      rcases lt_or_ge (3*(α/10)) (1/100 : ℝ) with hlt | hge
      · -- 3α/10 < 1/100 : the deep bound
        have hexp_neg : 3*(α/10) - 1/100 < 0 := by linarith
        have hb1 : s^(3*(α/10) - 1/100) ≤ (Real.sin α)^(3*(α/10) - 1/100) :=
          Real.rpow_le_rpow_of_nonpos hsinα hs0 (le_of_lt hexp_neg)
        have hsin_lb : 2*α/Real.pi ≤ Real.sin α := by
          have h' := Real.mul_le_sin (le_of_lt hα0)
            (by linarith [hα1, Real.pi_gt_three] : α ≤ Real.pi/2)
          calc 2*α/Real.pi = 2/Real.pi * α := by ring
            _ ≤ Real.sin α := h'
        have hb2 : (Real.sin α)^(3*(α/10) - 1/100) ≤ (2*α/Real.pi)^(3*(α/10) - 1/100) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hsin_lb (le_of_lt hexp_neg)
        have hb3 : (2*α/Real.pi)^(3*(α/10) - 1/100)
            = (2/Real.pi)^(3*(α/10) - 1/100) * α^(3*(α/10) - 1/100) := by
          rw [show 2*α/Real.pi = (2/Real.pi)*α by ring,
            Real.mul_rpow (by positivity : (0:ℝ) ≤ 2/Real.pi) (le_of_lt hα0)]
        have hb4 : (2/Real.pi)^(3*(α/10) - 1/100) ≤ (Real.pi/2)^((1:ℝ)/100) := by
          have hconv : (2/Real.pi)^(3*(α/10) - 1/100)
              = (Real.pi/2)^(-(3*(α/10) - 1/100)) := by
            rw [show (2:ℝ)/Real.pi = (Real.pi/2)⁻¹ by ring,
              Real.inv_rpow (by positivity : (0:ℝ) ≤ Real.pi/2)]
            exact (Real.rpow_neg (by positivity : (0:ℝ) ≤ Real.pi/2) _).symm
          rw [hconv]
          exact Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi/2)
            (by linarith : -(3*(α/10) - 1/100) ≤ 1/100)
        have hpow : (Real.pi/2)^((1:ℝ)/100) ≤ 2 := by
          have h2 : (1:ℝ) ≤ Real.pi/2 := by linarith [Real.pi_gt_three]
          have h3 := Real.rpow_le_rpow_of_exponent_le h2 (show ((1:ℝ)/100) ≤ 1 by norm_num)
          rw [Real.rpow_one] at h3
          linarith [h3, Real.pi_le_four]
        have hαlb : α^(2 + (3*(α/10) - 1/100)) ≤ 1 :=
          Real.rpow_le_one (le_of_lt hα0) hα1 (by linarith)
        have halg : α^2 * (2*α/Real.pi)^(3*(α/10) - 1/100)
            = (2/Real.pi)^(3*(α/10) - 1/100) * α^(2 + (3*(α/10) - 1/100)) := by
          rw [hb3, show α^2 = α^(2:ℝ) by exact (Real.rpow_two α).symm]
          have h3 : α^(2:ℝ) * ((2/Real.pi)^(3*(α/10) - 1/100) * α^(3*(α/10) - 1/100))
              = (2/Real.pi)^(3*(α/10) - 1/100) * (α^(2:ℝ) * α^(3*(α/10) - 1/100)) := by ring
          rw [h3, ← Real.rpow_add (show (0:ℝ) < α by linarith)]
        have hchain : α^2 * s^(3*(α/10) - 1/100) ≤ 2 := by
          have hstep : α^2 * s^(3*(α/10) - 1/100)
              ≤ α^2 * (2*α/Real.pi)^(3*(α/10) - 1/100) :=
            mul_le_mul_of_nonneg_left (le_trans hb1 hb2) (sq_nonneg α)
          rw [halg] at hstep
          calc α^2 * s^(3*(α/10) - 1/100)
              ≤ (2/Real.pi)^(3*(α/10) - 1/100) * α^(2 + (3*(α/10) - 1/100)) := hstep
            _ ≤ (Real.pi/2)^((1:ℝ)/100) * 1 :=
                mul_le_mul hb4 hαlb (Real.rpow_nonneg (le_of_lt hα0) _)
                  (Real.rpow_nonneg (by positivity) _)
            _ ≤ 2 := by linarith [hpow]
        have hsq : (0:ℝ) ≤ s^(3*(α/10) - 1/100) := Real.rpow_nonneg hsnn _
        nlinarith [h1, hchain, hsq]
      · -- 3α/10 ≥ 1/100 : `s^(3α/10-1/100) ≤ 1`
        have hb : s^(3*(α/10) - 1/100) ≤ 1 := Real.rpow_le_one hsnn hs1 (by linarith)
        nlinarith [h1, hb, sq_nonneg α]
    · -- α ≤ s : use `(α+s)^2 ≤ 4s^2`
      have h1 : (α+s)^2 ≤ 4*s^2 := by nlinarith
      have h2 : s^2 * s^(3*(α/10) - 1/100) = s^(2 + (3*(α/10) - 1/100)) := by
        rw [← Real.rpow_two, ← Real.rpow_add hspos]
      have h3 : s^(2 + (3*(α/10) - 1/100)) ≤ 1 :=
        Real.rpow_le_one hsnn hs1 (by linarith)
      have h4 : (0:ℝ) ≤ s^(3*(α/10) - 1/100) := Real.rpow_nonneg hsnn _
      nlinarith [h1, h2, h3, h4]
  have hs_inv : s^(3*(α/10) - 1)
      = s^(3*(α/10) - 1 + Work.Spaces.eta) * s^(-(Work.Spaces.eta)) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  calc (α+s)^2 * s^(3*(α/10) - 1)
      = (α+s)^2 * (s^(3*(α/10) - 1 + Work.Spaces.eta) * s^(-(Work.Spaces.eta))) := by
        rw [hs_inv]
    _ = ((α+s)^2 * s^(3*(α/10) - 1 + Work.Spaces.eta)) * s^(-(Work.Spaces.eta)) := by ring
    _ ≤ 8 * s^(-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right key (Real.rpow_nonneg hsnn _)

/-- On the region `s ≤ sin α` (i.e. `θ ≤ α/2`), the weights convert to the power weights in `θ`. -/
theorem bad_conv {α θ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ α/2) :
    (Real.sin (2*θ))^(3*(α/10) - 1) ≤ (Real.pi/4)^(1 - 3*(α/10)) * θ^(3*(α/10) - 1)
      ∧ θ^(3*(α/10) + 1) ≤ (Real.sin (2*θ))^(1 - α/10) := by
  have hβ1 : 3*(α/10) - 1 ≤ 0 := by linarith
  have h2θ : 0 < 2*θ := by linarith
  have h2θπ : 2*θ ≤ Real.pi/2 := by linarith [hθ1, hα1, Real.pi_gt_three]
  have hs_pos : 0 < Real.sin (2*θ) :=
    Real.sin_pos_of_pos_of_lt_pi h2θ (by linarith [Real.pi_pos, h2θπ])
  have hJ : 4/Real.pi * θ ≤ Real.sin (2*θ) := by
    have h := Real.mul_le_sin (le_of_lt h2θ) h2θπ
    have he : 2/Real.pi * (2*θ) = 4/Real.pi * θ := by ring
    rwa [he] at h
  constructor
  · have h1 : (Real.sin (2*θ))^(3*(α/10) - 1) ≤ ((4/Real.pi) * θ)^(3*(α/10) - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hJ hβ1
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (le_of_lt hθ0)] at h1
    have h2 : (4/Real.pi)^(3*(α/10) - 1) = (Real.pi/4)^(1 - 3*(α/10)) := by
      calc (4/Real.pi)^(3*(α/10) - 1)
          = ((Real.pi/4)⁻¹)^(3*(α/10) - 1) := by rw [show (4:ℝ)/Real.pi = (Real.pi/4)⁻¹ by ring]
        _ = ((Real.pi/4)^(3*(α/10) - 1))⁻¹ := Real.inv_rpow (by positivity) _
        _ = (Real.pi/4)^(-(3*(α/10) - 1)) := (Real.rpow_neg (by positivity) _).symm
        _ = (Real.pi/4)^(1 - 3*(α/10)) := by
              rw [show -(3*(α/10) - 1) = 1 - 3*(α/10) by ring]
    rw [h2] at h1
    exact h1
  · have hθ1' : θ ≤ 1 := by linarith only [hθ1, hα1]
    have h1 : θ^(3*(α/10) + 1) = θ^(4*(α/10)) * θ^(1 - α/10) := by
      rw [← Real.rpow_add hθ0]
      congr 1
      ring
    have h2 : θ^(4*(α/10)) ≤ 1 := Real.rpow_le_one (le_of_lt hθ0) hθ1' (by linarith)
    have hθle : θ ≤ Real.pi/4 * Real.sin (2*θ) := by
      have hπ : (0:ℝ) < Real.pi := Real.pi_pos
      have hmult := mul_le_mul_of_nonneg_left hJ (le_of_lt (by positivity : (0:ℝ) < Real.pi/4))
      have he : Real.pi/4 * (4/Real.pi * θ) = θ := by field_simp
      linarith [hmult, he]
    have h3 : θ^(1 - α/10) ≤ ((Real.pi/4) * Real.sin (2*θ))^(1 - α/10) :=
      Real.rpow_le_rpow (le_of_lt hθ0) hθle (by linarith)
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ Real.pi/4) (le_of_lt hs_pos)] at h3
    have h4 : (Real.pi/4)^(1 - α/10) ≤ 1 :=
      Real.rpow_le_one (by positivity) (by linarith [Real.pi_le_four] : Real.pi/4 ≤ 1) (by linarith)
    calc θ^(3*(α/10) + 1) = θ^(4*(α/10)) * θ^(1 - α/10) := h1
      _ ≤ 1 * ((Real.pi/4)^(1 - α/10) * (Real.sin (2*θ))^(1 - α/10)) := by
          exact mul_le_mul h2 h3 (Real.rpow_nonneg (le_of_lt hθ0) _) (by norm_num)
      _ ≤ (Real.sin (2*θ))^(1 - α/10) := by
          have h5 : (0:ℝ) ≤ (Real.sin (2*θ))^(1 - α/10) := Real.rpow_nonneg (le_of_lt hs_pos) _
          nlinarith [h4, h5]



end Work.FTS.H2.Transport3Aux
