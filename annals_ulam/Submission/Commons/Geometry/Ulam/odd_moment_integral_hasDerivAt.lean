import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum.RealSqrt

namespace Commons.Geometry.Ulam

open Set Filter
open MeasureTheory
open scoped Topology Interval

private abbrev HasDerivAtR (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule
    Real.pseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (inferInstance : ContinuousSMul ℝ ℝ) f f' x

private lemma pow_sqrt_hasDerivAtR {n : ℕ} {x : ℝ} (hn : 1 ≤ n) :
    HasDerivAtR (fun y : ℝ => y ^ n * Real.sqrt y)
      (((2 * (n : ℝ) + 1) / 2) * x ^ (n - 1) * Real.sqrt x) x := by
  by_cases hx0 : x = 0
  · subst x
    let φ : ℝ → ℝ := fun y => y ^ n * Real.sqrt y
    have hφ0 : φ 0 = 0 := by
      dsimp [φ]
      simp
    have h_cont : Continuous fun y : ℝ => y ^ (n - 1) * Real.sqrt y := by
      continuity
    have h_cont0 : ContinuousAt (fun y : ℝ => y ^ (n - 1) * Real.sqrt y) 0 :=
      h_cont.continuousAt
    have h_val : (fun y : ℝ => y ^ (n - 1) * Real.sqrt y) 0 = 0 := by
      simp
    have h_tendsto : Tendsto (fun y : ℝ => y ^ (n - 1) * Real.sqrt y) (𝓝 0) (𝓝 0) := by
      simpa [h_val] using h_cont0.tendsto
    have h_slope_event : (fun y : ℝ => (φ y - φ 0 - (y - 0) * 0) / (y - 0)) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun y : ℝ => y ^ (n - 1) * Real.sqrt y) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy0 : y ≠ 0 := hy
      dsimp [φ]
      have hpow : y ^ n = y ^ (n - 1) * y := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        simp [pow_succ]
      field_simp [hy0]
      rw [hpow]
      ring
    have h_tendsto' : Tendsto (fun y : ℝ => y ^ (n - 1) * Real.sqrt y) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      h_tendsto.mono_left nhdsWithin_le_nhds
    have h_slope_tendsto : Tendsto
        (fun y : ℝ => (φ y - φ 0 - (y - 0) * 0) / (y - 0)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      exact h_tendsto'.congr' h_slope_event.symm
    change HasDerivAt (fun y : ℝ => y ^ n * Real.sqrt y)
      (((2 * (n : ℝ) + 1) / 2) * 0 ^ (n - 1) * Real.sqrt 0) (0 : ℝ)
    rw [hasDerivAt_iff_tendsto_slope]
    convert h_slope_tendsto using 1
    · ext y
      simp [φ, slope, div_eq_mul_inv]
      ring
    · simp
  · have hx_ne : x ≠ 0 := hx0
    have hpow : HasDerivAtR (fun y : ℝ => y ^ n) ((n : ℝ) * x ^ (n - 1)) x := by
      simpa [HasDerivAtR] using (hasDerivAt_pow n x : HasDerivAt (fun y : ℝ => y ^ n) ((n : ℝ) * x ^ (n - 1)) x)
    have hsqrt : HasDerivAtR (fun y : ℝ => Real.sqrt y) (1 / (2 * Real.sqrt x)) x := by
      simpa [HasDerivAtR] using (Real.hasDerivAt_sqrt hx_ne : HasDerivAt (fun y : ℝ => Real.sqrt y) (1 / (2 * Real.sqrt x)) x)
    have hprod := hpow.mul hsqrt
    have hder_unsimpl : HasDerivAtR (fun y : ℝ => y ^ n * Real.sqrt y)
        ((n : ℝ) * x ^ (n - 1) * Real.sqrt x + x ^ n * (1 / (2 * Real.sqrt x))) x := by
      convert hprod using 1
      all_goals first
        | (ext y; simp)
        | rfl
    refine hder_unsimpl.congr_deriv ?_
    by_cases hx_neg : x < 0
    · have hsqrt0 : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hx_neg.le
      simp [hsqrt0]
    · have hx_pos : 0 < x := lt_of_le_of_ne (not_lt.mp hx_neg) (Ne.symm hx_ne)
      have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx_pos)
      have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx_pos)
      have hsucc : x ^ n = x ^ (n - 1) * x := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        simp [pow_succ]
      field_simp [hsqrt_ne]
      rw [hsq]
      rw [hsucc]
      ring

private lemma pow_sqrt_hasDerivAt {n : ℕ} {x : ℝ} (hn : 1 ≤ n) :
    HasDerivAt (fun y : ℝ => y ^ n * Real.sqrt y)
      (((2 * (n : ℝ) + 1) / 2) * x ^ (n - 1) * Real.sqrt x) x := by
  simpa [HasDerivAtR] using pow_sqrt_hasDerivAtR hn

private lemma odd_moment_slice_hasDerivAtR {n : ℕ} {F s t dh : ℝ} {h : ℝ → ℝ}
    (hn : 1 ≤ n) (_hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAtR
      (fun r : ℝ =>
        (F ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (F ^ 2 - (r * t + h r) ^ 2))
      (-(2 * (n : ℝ) + 1) * (s * t + h s) *
        (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2) *
          (t + dh)) s := by
  let u : ℝ → ℝ := fun r => F ^ 2 - (r * t + h r) ^ 2
  let φ : ℝ → ℝ := fun y => y ^ n * Real.sqrt y
  have hline : HasDerivAtR (fun r : ℝ => r * t + h r) (t + dh) s := by
    have h1std : HasDerivAt (fun r : ℝ => r * t) t s := by
      simpa using (hasDerivAt_id s).mul_const t
    have h1 : HasDerivAtR (fun r : ℝ => r * t) t s := by
      simpa [HasDerivAtR] using h1std
    have hhR : HasDerivAtR h dh s := by
      simpa [HasDerivAtR] using hh
    exact h1.add hhR
  have hsq : HasDerivAtR (fun r : ℝ => (r * t + h r) ^ 2) (2 * (s * t + h s) * (t + dh)) s := by
    have hpow := hline.pow 2
    convert hpow using 1
    all_goals first
      | (ext r; simp [Pi.pow_apply])
      | (norm_num)
      | rfl
  have hu : HasDerivAtR u (-(2 * (s * t + h s) * (t + dh))) s := by
    have hconst : HasDerivAtR (fun _ : ℝ => F ^ 2) (0 : ℝ) s := by
      simpa [HasDerivAtR] using (hasDerivAt_const s (F ^ 2) : HasDerivAt (fun _ : ℝ => F ^ 2) 0 s)
    have hsub := hconst.sub hsq
    convert hsub using 1
    all_goals first
      | (ext r; simp [u, Pi.sub_apply])
      | (ring)
      | rfl
  have hφ : HasDerivAtR φ (((2 * (n : ℝ) + 1) / 2) * (u s) ^ (n - 1) * Real.sqrt (u s)) (u s) := by
    exact pow_sqrt_hasDerivAtR hn
  have hcomp := hφ.comp s hu
  have hmain : HasDerivAtR (fun r : ℝ => φ (u r))
      (-(2 * (n : ℝ) + 1) * (s * t + h s) * (u s) ^ (n - 1) * Real.sqrt (u s) * (t + dh)) s := by
    refine hcomp.congr_deriv ?_
    have hcoef : ((2 * (n : ℝ) + 1) / 2) * (-(2 * (s * t + h s) * (t + dh))) =
        -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + dh) := by
      ring
    calc
      ((2 * (n : ℝ) + 1) / 2) * (u s) ^ (n - 1) * Real.sqrt (u s) *
          (-(2 * (s * t + h s) * (t + dh)))
          = ((2 * (n : ℝ) + 1) / 2) * (-(2 * (s * t + h s) * (t + dh))) *
              (u s) ^ (n - 1) * Real.sqrt (u s) := by ring
      _ = (-(2 * (n : ℝ) + 1) * (s * t + h s) * (t + dh)) * (u s) ^ (n - 1) * Real.sqrt (u s) := by
          rw [hcoef]
      _ = -(2 * (n : ℝ) + 1) * (s * t + h s) * (u s) ^ (n - 1) * Real.sqrt (u s) * (t + dh) := by ring
  simpa [φ, u] using hmain

private lemma odd_moment_slice_hasDerivAt {n : ℕ} {F s t dh : ℝ} {h : ℝ → ℝ}
    (hn : 1 ≤ n) (_hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        (F ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (F ^ 2 - (r * t + h r) ^ 2))
      (-(2 * (n : ℝ) + 1) * (s * t + h s) *
        (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2) *
          (t + dh)) s := by
  simpa [HasDerivAtR] using odd_moment_slice_hasDerivAtR hn _hF hh

lemma odd_moment_integral_hasDerivAt {n : ℕ} {f h : ℝ → ℝ} {a b : ℝ}
    (hn : 1 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc a b))
    (hh_cont : ContDiffOn ℝ ⊤ h Set.univ) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in a..b,
          (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2))
      (-(2 * (n : ℝ) + 1) *
        ∫ t in a..b,
          (s * t + h s) *
            (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) * (t + deriv h s)) s := by
  classical
  let F : ℝ → ℝ → ℝ := fun r t =>
    (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)
  let F' : ℝ → ℝ → ℝ := fun r t =>
    -(2 * (n : ℝ) + 1) * (r * t + h r) *
      (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) *
        (t + deriv h r)
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc a b, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  have h_deriv_cont_on_univ : ContinuousOn (deriv h) Set.univ := by
    exact hh_cont.continuousOn_deriv_of_isOpen isOpen_univ (by simp)
  have h_deriv_cont : Continuous (deriv h) := by
    rwa [continuousOn_univ] at h_deriv_cont_on_univ
  have h_cont_on_univ : ContinuousOn h Set.univ := hh_cont.continuousOn
  have h_cont : Continuous h := by
    rwa [continuousOn_univ] at h_cont_on_univ
  have hderiv_meas : Measurable (deriv h) := h_deriv_cont.measurable
  let S : Set ℝ := Set.Icc (s - 1) (s + 1)
  have hS_mem : S ∈ nhds s := by
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
  let B : ℝ := (M ^ 2) ^ (n - 1) * M
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  let bound : ℝ → ℝ := fun t => (2 * (n : ℝ) + 1) * M * B * (|t| + C)
  have hbound_nonneg : ∀ t, 0 ≤ bound t := by
    intro t; dsimp [bound]; positivity
  have hF_meas : ∀ᶠ r in nhds s, AEStronglyMeasurable (F r) (volume.restrict (Ι a b)) := by
    filter_upwards [hS_mem] with r hr
    have h_meas : Measurable (fun t : ℝ =>
        (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) := by
      fun_prop
    exact h_meas.aestronglyMeasurable.restrict
  have hF_int : IntervalIntegrable (F s) volume a b := by
    rw [intervalIntegrable_iff]
    have hmeas : AEStronglyMeasurable (F s) (volume.restrict (Ι a b)) := by
      exact hF_meas.self_of_nhds
    let Bint : ℝ := (M ^ 2) ^ n * M
    have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint]; positivity
    have hbnd : ∀ᵐ t ∂volume.restrict (Ι a b), ‖F s t‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [] with t ht
      have htIoc : t ∈ Ioc a b := by
        simpa [Set.uIoc_of_le hab] using ht
      have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
      have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
      have hft_le : f t ≤ M := hf_le_M t htcc
      by_cases hnonpos : f t ^ 2 - (s * t + h s) ^ 2 ≤ 0
      · have hsqrt : Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos hnonpos
        dsimp [F]
        rw [hsqrt, mul_zero]
        simpa using hBint_nonneg
      · have hbase_nonneg : 0 ≤ f t ^ 2 - (s * t + h s) ^ 2 := le_of_lt (lt_of_not_ge hnonpos)
        have hbase_le : f t ^ 2 - (s * t + h s) ^ 2 ≤ M ^ 2 := by
          have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
          nlinarith [sq_nonneg (s * t + h s)]
        have hpow : |(f t ^ 2 - (s * t + h s) ^ 2) ^ n| ≤ (M ^ 2) ^ n := by
          rw [abs_pow, abs_of_nonneg hbase_nonneg]
          exact pow_le_pow_left₀ hbase_nonneg hbase_le n
        have hsqrt : |Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)| ≤ M := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          have hle_arg : f t ^ 2 - (s * t + h s) ^ 2 ≤ M ^ 2 := hbase_le
          exact (Real.sqrt_le_left (le_of_lt hMpos)).2 hle_arg
        dsimp [F]
        have hmul : |(f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)| ≤ Bint := by
          dsimp [Bint]
          simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
        simpa using hmul
    exact IntegrableOn.of_bound (by
        rw [Set.uIoc_of_le hab]
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top) hmeas _ hbnd
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Ι a b)) := by
    have h_meas : Measurable (fun t : ℝ =>
        -(2 * (n : ℝ) + 1) * (s * t + h s) *
          (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
            (t + deriv h s)) := by
      fun_prop
    exact h_meas.aestronglyMeasurable.restrict
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ r ∈ S, ‖F' r t‖ ≤ bound t := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Ioc a b := by
      simpa [Set.uIoc_of_le hab] using ht
    have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hft_le : f t ≤ M := hf_le_M t htcc
    by_cases hnonpos : f t ^ 2 - (r * t + h r) ^ 2 ≤ 0
    · have hsqrt : Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos hnonpos
      dsimp [F', bound]
      rw [hsqrt, mul_zero, zero_mul, abs_zero]
      exact hbound_nonneg t
    · have hbase_nonneg : 0 ≤ f t ^ 2 - (r * t + h r) ^ 2 := le_of_lt (lt_of_not_ge hnonpos)
      have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
      have hline_sq_lt : (r * t + h r) ^ 2 < f t ^ 2 := by nlinarith
      have hline_sq_le : (r * t + h r) ^ 2 ≤ M ^ 2 := le_trans (le_of_lt hline_sq_lt) hftsq
      have hline_abs_le : |r * t + h r| ≤ M := abs_le_of_sq_le_sq hline_sq_le (le_of_lt hMpos)
      have hbase_le : f t ^ 2 - (r * t + h r) ^ 2 ≤ M ^ 2 := by nlinarith
      have hpow : |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
        rw [abs_pow, abs_of_nonneg hbase_nonneg]
        exact pow_le_pow_left₀ hbase_nonneg hbase_le (n - 1)
      have hsqrt : |Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)| ≤ M := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        have hle_arg : f t ^ 2 - (r * t + h r) ^ 2 ≤ M ^ 2 := hbase_le
        exact (Real.sqrt_le_left (le_of_lt hMpos)).2 hle_arg
      have hlin_le : |t + deriv h r| ≤ |t| + C := by
        calc |t + deriv h r| ≤ |t| + |deriv h r| := abs_add_le t (deriv h r)
          _ ≤ |t| + C := by nlinarith [hderiv_bound r hr]
      have hcoef_nonneg : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
      dsimp [F', bound]
      calc
        |-(2 * (n : ℝ) + 1) * (r * t + h r) *
          (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) *
            (t + deriv h r)|
            = (2 * (n : ℝ) + 1) * |r * t + h r| *
                |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| * |Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)| *
                  |t + deriv h r| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul]
              rw [abs_neg, abs_of_nonneg hcoef_nonneg]
        _ ≤ (2 * (n : ℝ) + 1) * M * (M ^ 2) ^ (n - 1) * M * (|t| + C) := by
              gcongr
        _ = (2 * (n : ℝ) + 1) * M * B * (|t| + C) := by
              dsimp [B]
              ring
  have h_bound_int : IntervalIntegrable bound volume a b := by
    dsimp [bound]
    exact ((continuous_abs.intervalIntegrable a b).add intervalIntegrable_const).const_mul _
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ r ∈ S,
      HasDerivAt (fun r => F r t) (F' r t) r := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Ioc a b := by
      simpa [Set.uIoc_of_le hab] using ht
    have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hh_deriv : HasDerivAt h (deriv h r) r := by
      have hd : DifferentiableAt ℝ h r := by
        exact (hh_cont.contDiffAt (by simp)).differentiableAt (by simp)
      exact hd.hasDerivAt
    exact odd_moment_slice_hasDerivAt (n := n) (F := f t) (s := r) (t := t) (dh := deriv h r)
      (h := h) hn hft_nonneg hh_deriv
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := F) (F' := F') (x₀ := s) (s := S) (μ := volume) (a := a) (b := b)
    hS_mem hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  have hder_int : (∫ t in a..b, F' s t) =
      -(2 * (n : ℝ) + 1) *
        ∫ t in a..b,
          (s * t + h s) *
            (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) * (t + deriv h s) := by
    simp [F', mul_assoc]
  simpa [F] using hmain.2.congr_deriv hder_int

end Commons.Geometry.Ulam