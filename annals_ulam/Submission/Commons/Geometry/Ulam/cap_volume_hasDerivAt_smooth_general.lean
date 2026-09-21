import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Submission.Commons.Geometry.Ulam.cap_slice_hasDerivAt
import Submission.Commons.Geometry.Ulam.cap_volume_continuousOn_Ici_zero

namespace Commons.Geometry.Ulam

open Set Filter MeasureTheory
open scoped Topology Interval

private lemma norm_cap_slice_integral_le_general {n : ℕ} {f h : ℝ → ℝ} {M a b : ℝ}
    (hab : a ≤ b)
    (hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι a b →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (f t ^ 2 - z ^ 2) ^ (n - 1))‖ ≤
        (2 * M) * (2 * M ^ 2) ^ (n - 1) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Ioc a b := by
    simpa [Set.uIoc_of_le hab] using ht
  have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  let aa : ℝ := -f t
  let bb : ℝ := f t
  let U : ℝ := max aa (min bb (r * t + h r))
  let g : ℝ → ℝ := fun z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  have ha_le_b : aa ≤ bb := by dsimp [aa, bb]; linarith
  have hU_mem : U ∈ Set.Icc aa bb := by
    dsimp [U]
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le ha_le_b (min_le_left _ _)
  have hUa : aa ≤ U := hU_mem.1
  have hUb : U ≤ bb := hU_mem.2
  have hg_bound : ∀ z ∈ Ι aa U, ‖g z‖ ≤ (2 * M ^ 2) ^ (n - 1) := by
    intro z hz
    have hzIoc : z ∈ Ioc aa U := by
      simpa [Set.uIoc_of_le hUa] using hz
    have hz_lower : -M ≤ z := by
      have ha_lower : -M ≤ aa := by dsimp [aa]; linarith
      exact le_trans ha_lower (le_of_lt hzIoc.1)
    have hz_upper : z ≤ M := by
      have hb_upper : bb ≤ M := by dsimp [bb]; linarith
      exact le_trans (le_trans hzIoc.2 hUb) hb_upper
    have hz_abs : |z| ≤ M := abs_le.mpr ⟨hz_lower, hz_upper⟩
    have hsq_le : |f t ^ 2 - z ^ 2| ≤ 2 * M ^ 2 := by
      have h1 : |f t ^ 2 - z ^ 2| ≤ f t ^ 2 + z ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (f t), sq_nonneg z]
      have hftsq : f t ^ 2 ≤ M ^ 2 := by
        exact pow_le_pow_left₀ hft_nonneg hft_le 2
      have hzsq : z ^ 2 ≤ M ^ 2 := by
        calc z ^ 2 = |z| ^ 2 := by simp [sq_abs]
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg z) hz_abs 2
      have hsum : f t ^ 2 + z ^ 2 ≤ 2 * M ^ 2 := by nlinarith
      exact le_trans h1 hsum
    have hpow : |(f t ^ 2 - z ^ 2) ^ (n - 1)| ≤ (2 * M ^ 2) ^ (n - 1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hsq_le (n - 1)
    dsimp [g]
    simpa [Real.norm_eq_abs] using hpow
  have hlen : |U - aa| ≤ 2 * M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hUa)]
    calc U - aa ≤ bb - aa := sub_le_sub hUb le_rfl
      _ = 2 * f t := by dsimp [aa, bb]; ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := aa) (b := U)
      (C := (2 * M ^ 2) ^ (n - 1)) (f := g) hg_bound
  calc ‖∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        (f t ^ 2 - z ^ 2) ^ (n - 1)‖
      = ‖∫ z in aa..U, g z‖ := by simp [aa, bb, U, g]
    _ ≤ (2 * M ^ 2) ^ (n - 1) * |U - aa| := hnorm
    _ ≤ (2 * M ^ 2) ^ (n - 1) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (pow_nonneg (by nlinarith [sq_nonneg M]) _)
    _ = (2 * M) * (2 * M ^ 2) ^ (n - 1) := by ring

lemma cap_volume_hasDerivAt_smooth_general {n : ℕ} {f h : ℝ → ℝ} {a b : ℝ}
    (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc a b))
    (hh_cont : ContDiffOn ℝ ⊤ h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in a..b,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (f t ^ 2 - z ^ 2) ^ (n - 1))
      (∫ t in a..b,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)
        else 0) s := by
  classical
  let F : ℝ → ℝ → ℝ := fun r t =>
    ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
      (f t ^ 2 - z ^ 2) ^ (n - 1)
  let F' : ℝ → ℝ → ℝ := fun r t =>
    if -f t < r * t + h r ∧ r * t + h r < f t then
      (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * (t + deriv h r)
    else 0
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
  let bound : ℝ → ℝ := fun t => (M ^ 2) ^ (n - 1) * (|t| + C)
  have hbound_nonneg : ∀ t, 0 ≤ bound t := by
    intro t; dsimp [bound]; positivity
  have hF_meas : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable (F r) (volume.restrict (Ι a b)) := by
    filter_upwards [hS_mem] with r hr
    have hL : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU : Measurable (fun t : ℝ => max (-f t) (min (f t) (r * t + h r))) := by fun_prop
    have hg : Measurable (Function.uncurry (fun t z : ℝ => (f t ^ 2 - z ^ 2) ^ (n - 1))) := by fun_prop
    exact (aeStronglyMeasurable_intervalIntegral_param hL hU hg).restrict
  have hF_int : IntervalIntegrable (F s) volume a b := by
    rw [intervalIntegrable_iff]
    have hmeas : AEStronglyMeasurable (F s) (volume.restrict (Ι a b)) := by
      exact hF_meas.self_of_nhds
    have hbnd' := norm_cap_slice_integral_le_general (n := n) (f := f) (h := h) (M := M)
      (a := a) (b := b) hab hf_le_M hf_nonneg s
    have hbnd : ∀ᵐ t ∂volume.restrict (Ι a b), ‖F s t‖ ≤ (2 * M) * (2 * M ^ 2) ^ (n - 1) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      exact ht
    exact IntegrableOn.of_bound (by
        rw [Set.uIoc_of_le hab]
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top) hmeas _ hbnd
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Ι a b)) := by
    have h_cond_meas : MeasurableSet {t : ℝ | -f t < s * t + h s ∧ s * t + h s < f t} := by
      apply MeasurableSet.inter
      · exact measurableSet_lt hf_meas.neg (by fun_prop)
      · exact measurableSet_lt (by fun_prop) hf_meas
    have h_then_meas : Measurable (fun t : ℝ =>
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) := by
      fun_prop
    exact (Measurable.ite h_cond_meas h_then_meas measurable_const).aestronglyMeasurable.restrict
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ r ∈ S, ‖F' r t‖ ≤ bound t := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Ioc a b := by
      simpa [Set.uIoc_of_le hab] using ht
    have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hft_le : f t ≤ M := hf_le_M t htcc
    by_cases hcond : -f t < r * t + h r ∧ r * t + h r < f t
    · have hbase_nonneg : 0 ≤ f t ^ 2 - (r * t + h r) ^ 2 := by
        have hsq := sq_le_sq' (le_of_lt hcond.1) (le_of_lt hcond.2)
        nlinarith
      have hbase_le : f t ^ 2 - (r * t + h r) ^ 2 ≤ M ^ 2 := by
        have hsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
        nlinarith
      have hW_le : |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
        rw [abs_pow, abs_of_nonneg hbase_nonneg]
        exact pow_le_pow_left₀ hbase_nonneg hbase_le (n - 1)
      have hlin_le : |t + deriv h r| ≤ |t| + C := by
        calc |t + deriv h r| ≤ |t| + |deriv h r| := abs_add_le t (deriv h r)
          _ ≤ |t| + C := by nlinarith [hderiv_bound r hr]
      dsimp [F']
      rw [if_pos hcond, abs_mul]
      have hA_nonneg : 0 ≤ (M ^ 2) ^ (n - 1) := by positivity
      dsimp [bound]
      exact mul_le_mul hW_le hlin_le (abs_nonneg _) hA_nonneg
    · dsimp [F']
      rw [if_neg hcond, abs_zero]
      exact hbound_nonneg t
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
    exact cap_slice_hasDerivAt (n := n) (F := f t) (s := r) (t := t) (dh := deriv h r)
      (h := h) hn hft_nonneg hh_deriv
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := F) (F' := F') (x₀ := s) (s := S) (μ := volume) (a := a) (b := b)
    hS_mem hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  exact hmain.2

end Commons.Geometry.Ulam