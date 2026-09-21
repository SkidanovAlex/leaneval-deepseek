import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Submission.Commons.Geometry.Ulam.cap_slice_hasDerivAt

namespace Commons.Geometry.Ulam

open Set Filter MeasureTheory
open scoped Topology Interval

private abbrev HasDerivAtR (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule
    Real.pseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (inferInstance : ContinuousSMul ℝ ℝ) f f' x

private lemma pow_sub_sq_hasDerivAtR {n : ℕ} {F y : ℝ} :
    HasDerivAtR (fun y : ℝ => (F ^ 2 - y ^ 2) ^ n)
      (-(2 * (n : ℝ)) * y * (F ^ 2 - y ^ 2) ^ (n - 1)) y := by
  let u : ℝ → ℝ := fun y => F ^ 2 - y ^ 2
  have hu : HasDerivAtR u (-(2 * y)) y := by
    have hconst : HasDerivAtR (fun _ : ℝ => F ^ 2) (0 : ℝ) y := by
      simpa [HasDerivAtR] using (hasDerivAt_const y (F ^ 2) : HasDerivAt (fun _ : ℝ => F ^ 2) 0 y)
    have hsq : HasDerivAtR (fun y : ℝ => y ^ 2) (2 * y) y := by
      simpa [HasDerivAtR] using (hasDerivAt_pow (n := 2) (x := y))
    have hsub := hconst.sub hsq
    convert hsub using 1
    all_goals first
      | (ext z; simp [u, Pi.sub_apply])
      | (ring)
      | rfl
  have hpow := hu.pow n
  convert hpow using 1
  all_goals first
    | (ext z; simp [u])
    | (ring)
    | rfl

private lemma pow_sub_sq_hasDerivAt {n : ℕ} {F y : ℝ} :
    HasDerivAt (fun y : ℝ => (F ^ 2 - y ^ 2) ^ n)
      (-(2 * (n : ℝ)) * y * (F ^ 2 - y ^ 2) ^ (n - 1)) y := by
  simpa [HasDerivAtR] using pow_sub_sq_hasDerivAtR (n := n) (F := F) (y := y)

private lemma pow_sub_sq_hasDerivAt_zero_left {n : ℕ} {F : ℝ} (hn : 2 ≤ n) :
    HasDerivAt (fun y : ℝ => (F ^ 2 - y ^ 2) ^ n) 0 (-F) := by
  have h := pow_sub_sq_hasDerivAt (n := n) (F := F) (y := -F)
  refine h.congr_deriv ?_
  have hpow0 : (0 : ℝ) ^ (n - 1) = 0 := by
    exact zero_pow (by omega : n - 1 ≠ 0)
  simp [hpow0]

private lemma pow_sub_sq_hasDerivAt_zero_right {n : ℕ} {F : ℝ} (hn : 2 ≤ n) :
    HasDerivAt (fun y : ℝ => (F ^ 2 - y ^ 2) ^ n) 0 F := by
  have h := pow_sub_sq_hasDerivAt (n := n) (F := F) (y := F)
  refine h.congr_deriv ?_
  have hpow0 : (0 : ℝ) ^ (n - 1) = 0 := by
    exact zero_pow (by omega : n - 1 ≠ 0)
  simp [hpow0]

private lemma cap_pow_slice_hasDerivAt {n : ℕ} {F s t dh : ℝ} {h : ℝ → ℝ}
    (hn : 2 ≤ n) (hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        (F ^ 2 - (max (-F) (min F (r * t + h r))) ^ 2) ^ n)
      (if -F < s * t + h s ∧ s * t + h s < F then
          -(2 * (n : ℝ)) * (s * t + h s) *
            (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + dh)
        else 0) s := by
  let a : ℝ := -F
  let b : ℝ := F
  let x : ℝ → ℝ := fun r => r * t + h r
  let u : ℝ → ℝ := fun r => max a (min b (x r))
  let P : ℝ → ℝ := fun y => (F ^ 2 - y ^ 2) ^ n
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
  have hP_left : HasDerivAt P 0 a := by
    dsimp [P, a]
    exact pow_sub_sq_hasDerivAt_zero_left hn
  have hP_right : HasDerivAt P 0 b := by
    dsimp [P, b]
    exact pow_sub_sq_hasDerivAt_zero_right hn
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
    have hP_deriv : HasDerivAt P (-(2 * (n : ℝ)) * (x s) * (F ^ 2 - (x s) ^ 2) ^ (n - 1)) (x s) := by
      dsimp [P]
      simpa using pow_sub_sq_hasDerivAt (n := n) (F := F) (y := x s)
    have hcomp : HasDerivAt (P ∘ x)
        (-(2 * (n : ℝ)) * (x s) * (F ^ 2 - (x s) ^ 2) ^ (n - 1) * (t + dh)) s := by
      simpa [Function.comp_def] using hP_deriv.comp s hx
    have h_event : (fun r : ℝ =>
        (F ^ 2 - (max (-F) (min F (r * t + h r))) ^ 2) ^ n) =ᶠ[𝓝 s]
        (P ∘ x) := by
      filter_upwards [h_event_u] with r hr
      have hr' : max (-F) (min F (r * t + h r)) = r * t + h r := by
        simpa [u, x, a, b] using hr
      simp [P, x, hr']
    have hmain : HasDerivAt
        (fun r : ℝ =>
          (F ^ 2 - (max (-F) (min F (r * t + h r))) ^ 2) ^ n)
        (-(2 * (n : ℝ)) * (x s) * (F ^ 2 - (x s) ^ 2) ^ (n - 1) * (t + dh)) s :=
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
      have hderiv0 : HasDerivAt (P ∘ u) 0 s := by
        simpa [Function.comp_def] using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
          (P := P) (q := u) (s := s) (b := a)
          hP_left hu_cont hqs hqO
      have hmain : HasDerivAt
          (fun r : ℝ =>
            (F ^ 2 - (max (-F) (min F (r * t + h r))) ^ 2) ^ n) 0 s := by
        simpa [u, a, b, P, Function.comp_def] using hderiv0
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
      have hderiv0 : HasDerivAt (P ∘ u) 0 s := by
        simpa [Function.comp_def] using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
          (P := P) (q := u) (s := s) (b := b)
          hP_right hu_cont hqs hqO
      have hmain : HasDerivAt
          (fun r : ℝ =>
            (F ^ 2 - (max (-F) (min F (r * t + h r))) ^ 2) ^ n) 0 s := by
        simpa [u, a, b, P, Function.comp_def] using hderiv0
      simpa [hcond_false] using hmain

private lemma clamp_sq_le_sq {F L : ℝ} (hF : 0 ≤ F) :
    (max (-F) (min F L)) ^ 2 ≤ F ^ 2 := by
  have habs : |max (-F) (min F L)| ≤ F := by
    have hle1 : max (-F) (min F L) ≤ F := by
      exact max_le (by linarith) (min_le_left (a := F) (b := L))
    have hle2 : -F ≤ max (-F) (min F L) := le_max_left (a := -F) (b := min F L)
    exact abs_le.2 ⟨hle2, hle1⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
  simpa [sq_abs] using hsq

private lemma clamp_base_nonneg {F L : ℝ} (hF : 0 ≤ F) :
    0 ≤ F ^ 2 - (max (-F) (min F L)) ^ 2 := by
  have hsq := clamp_sq_le_sq (F := F) (L := L) hF
  linarith

lemma cap_pow_integral_hasDerivAt_smooth {n : ℕ} {f h : ℝ → ℝ} {a b : ℝ}
    (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc a b))
    (hh_cont : ContDiffOn ℝ (WithTop.some (⊤ : ℕ∞)) h Set.univ) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in a..b,
          (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2) ^ n)
      (∫ t in a..b,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          -(2 * (n : ℝ)) * (s * t + h s) *
            (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)
        else 0) s := by
  classical
  let F : ℝ → ℝ → ℝ := fun r t =>
    (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2) ^ n
  let F' : ℝ → ℝ → ℝ := fun r t =>
    if -f t < r * t + h r ∧ r * t + h r < f t then
      -(2 * (n : ℝ)) * (r * t + h r) *
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
  let bound : ℝ → ℝ := fun t => (2 * (n : ℝ)) * M * ((M ^ 2) ^ (n - 1)) * (|t| + C)
  have hbound_nonneg : ∀ t, 0 ≤ bound t := by
    intro t; dsimp [bound]; positivity
  have hF_meas : ∀ᶠ r in nhds s, AEStronglyMeasurable (F r) (volume.restrict (Ι a b)) := by
    filter_upwards [hS_mem] with r hr
    have h_meas : Measurable (fun t : ℝ =>
        (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2) ^ n) := by
      fun_prop
    exact h_meas.aestronglyMeasurable.restrict
  have hF_int : IntervalIntegrable (F s) volume a b := by
    rw [intervalIntegrable_iff]
    have hmeas : AEStronglyMeasurable (F s) (volume.restrict (Ι a b)) := by
      exact hF_meas.self_of_nhds
    let Bint : ℝ := (M ^ 2) ^ n
    have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint]; positivity
    have hbnd : ∀ᵐ t ∂volume.restrict (Ι a b), ‖F s t‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [] with t ht
      have htIoc : t ∈ Ioc a b := by
        simpa [Set.uIoc_of_le hab] using ht
      have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
      have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
      have hft_le : f t ≤ M := hf_le_M t htcc
      have hclamp_sq_le : (max (-f t) (min (f t) (s * t + h s))) ^ 2 ≤ (f t) ^ 2 :=
        clamp_sq_le_sq (F := f t) (L := s * t + h s) hft_nonneg
      have hbase_nonneg : 0 ≤ f t ^ 2 - (max (-f t) (min (f t) (s * t + h s))) ^ 2 := by
        linarith
      have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
      have hbase_le : f t ^ 2 - (max (-f t) (min (f t) (s * t + h s))) ^ 2 ≤ M ^ 2 := by
        nlinarith
      have hpow : |(f t ^ 2 - (max (-f t) (min (f t) (s * t + h s))) ^ 2) ^ n| ≤ (M ^ 2) ^ n := by
        rw [abs_pow, abs_of_nonneg hbase_nonneg]
        exact pow_le_pow_left₀ hbase_nonneg hbase_le n
      dsimp [F]
      simpa using hpow
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
        -(2 * (n : ℝ)) * (s * t + h s) *
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
      have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
      have hbase_le : f t ^ 2 - (r * t + h r) ^ 2 ≤ M ^ 2 := by
        nlinarith [sq_nonneg (r * t + h r)]
      have hline_sq_le : (r * t + h r) ^ 2 ≤ M ^ 2 := by
        have hsq := sq_le_sq' (le_of_lt hcond.1) (le_of_lt hcond.2)
        nlinarith
      have hline_abs_le : |r * t + h r| ≤ M := abs_le_of_sq_le_sq hline_sq_le (le_of_lt hMpos)
      have hpow : |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
        rw [abs_pow, abs_of_nonneg hbase_nonneg]
        exact pow_le_pow_left₀ hbase_nonneg hbase_le (n - 1)
      have hlin_le : |t + deriv h r| ≤ |t| + C := by
        calc |t + deriv h r| ≤ |t| + |deriv h r| := abs_add_le t (deriv h r)
          _ ≤ |t| + C := by nlinarith [hderiv_bound r hr]
      have hcoef_nonneg : 0 ≤ 2 * (n : ℝ) := by positivity
      dsimp [F']
      rw [if_pos hcond]
      dsimp [bound]
      calc
        |-(2 * (n : ℝ)) * (r * t + h r) *
          (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * (t + deriv h r)|
            = (2 * (n : ℝ)) * |r * t + h r| *
                |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| * |t + deriv h r| := by
              simp [abs_mul, abs_of_nonneg hcoef_nonneg]
        _ ≤ (2 * (n : ℝ)) * M * ((M ^ 2) ^ (n - 1)) * (|t| + C) := by
              gcongr
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
    have hs := cap_pow_slice_hasDerivAt (n := n) (F := f t) (s := r) (t := t) (dh := deriv h r)
      (h := h) hn hft_nonneg hh_deriv
    simpa [F, F'] using hs
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := F) (F' := F') (x₀ := s) (s := S) (μ := volume) (a := a) (b := b)
    hS_mem hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  have hder_int : (∫ t in a..b, F' s t) =
      ∫ t in a..b,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          -(2 * (n : ℝ)) * (s * t + h s) *
            (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)
        else 0 := by
    simp [F']
  exact hmain.2.congr_deriv hder_int

end Commons.Geometry.Ulam