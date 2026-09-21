import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even
import Submission.Commons.Geometry.Ulam.cap_volume_continuousOn_Ici_zero
import Submission.Commons.Geometry.Ulam.cap_slice_hasDerivAt
import Submission.Commons.Geometry.Ulam.cap_volume_deriv_integral_eq_zero_smooth

namespace Commons.Geometry.Ulam

open MeasureTheory
open Set Filter
open scoped ContDiff Pointwise RealInnerProductSpace BigOperators Topology Interval

set_option autoImplicit false

/-! Helper lemmas for the even profile cap volume half theorem. -/

lemma const_on_Ioi_of_deriv_zero {f : ℝ → ℝ}
    (hderiv : ∀ s > 0, HasDerivAt f 0 s)
    (hcont : ContinuousOn f (Set.Ici 0)) :
    ∀ s > 0, f s = f 0 := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioi 0) := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hderiv_eq : Set.EqOn (deriv f) 0 (Set.Ioi 0) := by
    intro x hx
    exact (hderiv x hx).deriv
  have hconst : ∃ a, ∀ x ∈ Set.Ioi 0, f x = a :=
    isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hderiv_eq
  rcases hconst with ⟨a, ha⟩
  have hcont0 : ContinuousWithinAt f (Set.Ici 0) 0 := hcont.continuousWithinAt (by simp)
  have htend : Filter.Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := by
    refine tendsto_nhdsWithin_mono_left ?_ hcont0
    intro x hx
    have hx' : 0 < x := by simpa using hx
    exact le_of_lt hx'
  have htend_const : Filter.Tendsto f (𝓝[>] 0) (𝓝 a) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (ha x hx).symm
  have h0a : f 0 = a := tendsto_nhds_unique htend htend_const
  intro s hs
  have hs_eq : f s = a := ha s hs
  rw [hs_eq, h0a]


lemma intervalIntegral_half_even {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ}
    (hg_cont : Continuous g) (hg_even : ∀ z, g (-z) = g z) :
    (∫ z in (-a)..0, g z) = ∫ z in 0..a, g z ∧
    (∫ z in (-a)..a, g z) = 2 * ∫ z in (-a)..0, g z := by
  have hsymm : (∫ z in (-a)..0, g z) = ∫ z in 0..a, g z := by
    have hcomp := intervalIntegral.integral_comp_neg (f := g) (a := 0) (b := a)
    calc
      (∫ z in (-a)..0, g z) = ∫ z in 0..a, g (-z) := by simpa using hcomp.symm
      _ = ∫ z in 0..a, g z := by
        apply intervalIntegral.integral_congr
        intro z hz
        exact hg_even z
  have hint01 : IntervalIntegrable g volume 0 a := hg_cont.intervalIntegrable 0 a
  have hint_neg0 : IntervalIntegrable g volume (-a) 0 := hg_cont.intervalIntegrable (-a) 0
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := g)
    (a := -a) (b := 0) (c := a) hint_neg0 hint01
  constructor
  · exact hsymm
  · calc
      (∫ z in (-a)..a, g z) = (∫ z in (-a)..0, g z) + ∫ z in 0..a, g z := hsum.symm
      _ = (∫ z in (-a)..0, g z) + ∫ z in (-a)..0, g z := by rw [hsymm]
      _ = 2 * ∫ z in (-a)..0, g z := by ring

lemma cap_integral_zero_eq_half_total {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t) :
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, W t z) =
      (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..f t, W t z) / 2 := by
  intro W
  have hinner : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      (∫ z in (-f t)..f t, W t z) = 2 * ∫ z in (-f t)..0, W t z := by
    intro t ht
    have hft_nonneg : 0 ≤ f t := hf_nonneg t ht
    have hg_cont : Continuous (fun z => W t z) := by
      dsimp [W]; fun_prop
    have hg_even : ∀ z, W t (-z) = W t z := by
      intro z; dsimp [W]; ring
    exact (intervalIntegral_half_even hft_nonneg hg_cont hg_even).2
  have htotal_eq : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..f t, W t z) =
      2 * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, W t z) := by
    calc
      (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..f t, W t z)
        = ∫ t in (-1 : ℝ)..1, 2 * (∫ z in (-f t)..0, W t z) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (-1:ℝ)≤1)] using ht
            exact hinner t htIcc
      _ = 2 * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, W t z) := by
            rw [intervalIntegral.integral_const_mul]
  nlinarith

lemma even_profile_measurable_smooth {f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0) :
    Measurable f := by
  classical
  let s : Set ℝ := Set.Ioo (-1 : ℝ) 1
  let g : ℝ → ℝ := s.piecewise f (fun _ => 0)
  have hcont_f : ContinuousOn f s := hf_cont.continuousOn
  have hcont_zero : ContinuousOn (fun _ : ℝ => (0 : ℝ)) sᶜ := continuous_const.continuousOn
  have hg_meas : Measurable g := by
    dsimp [g, s]
    exact ContinuousOn.measurable_piecewise hcont_f hcont_zero measurableSet_Ioo
  have hfg : f = g := by
    ext t
    by_cases ht : t ∈ s
    · simp [g, s, ht]
    · have hzero : f t = 0 := by
        by_cases htc : t ∈ Set.Icc (-1 : ℝ) 1
        · have ht1 : -1 ≤ t := htc.1
          have ht2 : t ≤ 1 := htc.2
          have hnot : ¬ (-1 < t ∧ t < 1) := by simpa [s] using ht
          have hle_or : t = -1 ∨ t = 1 := by
            by_cases hlt : -1 < t
            · right
              have hnotlt : ¬ t < 1 := by
                intro h; exact hnot ⟨hlt, h⟩
              linarith
            · left
              linarith
          rcases hle_or with rfl | rfl <;> simp [hf_left, hf_right]
        · by_contra hz
          have hmem : t ∈ Function.support f := by
            simpa [Function.mem_support] using hz
          exact htc (hf_support hmem)
      simp [g, ht, hzero]
  rw [hfg]
  exact hg_meas

lemma cap_volume_hasDerivAt_smooth {n : ℕ} {f h : ℝ → ℝ}
    (hn : 2 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1))
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (f t ^ 2 - z ^ 2) ^ (n - 1))
      (∫ t in (-1 : ℝ)..1,
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
  have hf_abs_le : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M := by
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
  have hF_meas : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable (F r) (volume.restrict (Ι (-1 : ℝ) 1)) := by
    filter_upwards [hS_mem] with r hr
    have hL : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU : Measurable (fun t : ℝ => max (-f t) (min (f t) (r * t + h r))) := by fun_prop
    have hg : Measurable (Function.uncurry (fun t z : ℝ => (f t ^ 2 - z ^ 2) ^ (n - 1))) := by fun_prop
    exact (aeStronglyMeasurable_intervalIntegral_param hL hU hg).restrict
  have hF_int : IntervalIntegrable (F s) volume (-1 : ℝ) 1 := by
    rw [intervalIntegrable_iff]
    have hmeas : AEStronglyMeasurable (F s) (volume.restrict (Ι (-1 : ℝ) 1)) := by
      exact hF_meas.self_of_nhds
    have hbnd' := norm_cap_slice_integral_le (n := n) (f := f) (h := h) (M := M) hf_le_M hf_nonneg s
    have hbnd : ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ‖F s t‖ ≤ (2 * M) * (2 * M ^ 2) ^ (n - 1) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      exact ht
    exact IntegrableOn.of_bound (by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top) hmeas _ hbnd
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Ι (-1 : ℝ) 1)) := by
    have h_cond_meas : MeasurableSet {t : ℝ | -f t < s * t + h s ∧ s * t + h s < f t} := by
      apply MeasurableSet.inter
      · exact measurableSet_lt hf_meas.neg (by fun_prop)
      · exact measurableSet_lt (by fun_prop) hf_meas
    have h_then_meas : Measurable (fun t : ℝ =>
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) := by
      fun_prop
    exact (Measurable.ite h_cond_meas h_then_meas measurable_const).aestronglyMeasurable.restrict
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 → ∀ r ∈ S, ‖F' r t‖ ≤ bound t := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
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
  have h_bound_int : IntervalIntegrable bound volume (-1 : ℝ) 1 := by
    dsimp [bound]
    exact ((continuous_abs.intervalIntegrable (-1 : ℝ) 1).add intervalIntegrable_const).const_mul _
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 → ∀ r ∈ S,
      HasDerivAt (fun r => F r t) (F' r t) r := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hh_deriv : HasDerivAt h (deriv h r) r := by
      have hd : DifferentiableAt ℝ h r := by
        exact (hh_cont.contDiffAt (by simp)).differentiableAt (by simp)
      exact hd.hasDerivAt
    exact cap_slice_hasDerivAt (n := n) (F := f t) (s := r) (t := t) (dh := deriv h r)
      (h := h) hn hft_nonneg hh_deriv
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := F) (F' := F') (x₀ := s) (s := S) (μ := volume) (a := (-1 : ℝ)) (b := 1)
    hS_mem hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  exact hmain.2

lemma K_subset_H_large {d : ℕ} [NeZero d] {f : ℝ → ℝ} {M R : ℝ}
    (hd : 2 ≤ d)
    (hR : M < R)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    K ⊆ {x | x last ≤ R} := by
  intro last K x hx
  have hlast_pos : (0 : Fin d) < last := by
    dsimp [last]
    rw [Fin.lt_def]
    simp
    omega
  have hsq_nonneg : ∀ i ∈ Finset.Ioi (0 : Fin d), 0 ≤ (x i)^2 := by
    intro i hi; exact sq_nonneg _
  have hmem : last ∈ Finset.Ioi (0 : Fin d) := by simpa using hlast_pos
  have hsingle := Finset.single_le_sum (s := Finset.Ioi (0 : Fin d))
    (f := fun i : Fin d => (x i)^2) hsq_nonneg hmem
  have hx0mem : x 0 ∈ Set.Icc (-1 : ℝ) 1 := hx.1
  have hsum_le : ∑ i > 0, (x i)^2 ≤ f (x 0)^2 := hx.2
  have hlast_sq_le_fsq : (x last)^2 ≤ f (x 0)^2 := le_trans hsingle hsum_le
  have hf0_nonneg : 0 ≤ f (x 0) := hf_nonneg (x 0) hx0mem
  have hf0_le_M : f (x 0) ≤ M := hf_le_M (x 0) hx0mem
  have hfsq_le_Msq : f (x 0)^2 ≤ M^2 := pow_le_pow_left₀ hf0_nonneg hf0_le_M 2
  have hlast_sq_le_Msq : (x last)^2 ≤ M^2 := le_trans hlast_sq_le_fsq hfsq_le_Msq
  have hM_nonneg : 0 ≤ M := le_trans hf0_nonneg hf0_le_M
  have hlast_abs_le_M : |x last| ≤ M := by
    have hsq_abs : |x last| ^ 2 ≤ M ^ 2 := by simpa [sq_abs] using hlast_sq_le_Msq
    have h1 := (sq_le_sq (a := |x last|) (b := M)).1 hsq_abs
    simpa [abs_of_nonneg hM_nonneg, abs_abs] using h1
  have hlast_le_M : x last ≤ M := le_trans (le_abs_self _) hlast_abs_le_M
  simpa using (le_of_lt (lt_of_le_of_lt hlast_le_M hR) : x last ≤ R)

lemma max_min_eq_of_nonneg_le {f M : ℝ}
    (hf_nonneg : 0 ≤ f) (hf_le : f ≤ M) :
    max (-f) (min f M) = f := by
  have hmin : min f M = f := min_eq_left hf_le
  have hmax : max (-f) f = f := max_eq_right (by linarith)
  rw [hmin, hmax]

lemma inner_total_eq {n : ℕ} {f : ℝ → ℝ} {M : ℝ}
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M) :
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) M)), W t z) =
      ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), W t z := by
  intro W
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (-1:ℝ)≤1)] using ht
  have hup : max (-f t) (min (f t) M) = f t :=
    max_min_eq_of_nonneg_le (hf_nonneg t htIcc) (hf_le_M t htIcc)
  simp [hup]

lemma even_profile_cap_volume_half {d : ℕ} [NeZero d] (n : ℕ) (hdn : d = 2 * n) (hn : 2 ≤ n)
    {h x y f : ℝ → ℝ}
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
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ∀ s : ℝ, 0 < s →
      volume.real (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}) = volume.real K / 2 := by
  intro K s hs
  have hdpos : 2 ≤ d := by omega
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    even_profile_nonneg_Icc hf_conc hf_left hf_right
  have hf_meas : Measurable f := even_profile_measurable_smooth hf_support hf_cont hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) :=
    even_profile_bounded hf_conc hf_left hf_right
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  let capIntegral : ℝ → ℝ := fun r =>
    ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))), W t z
  have hderiv_int := cap_volume_deriv_integral_eq_zero_smooth hn hf_support hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hxy hJ
  have hderiv_cap : ∀ r > 0, HasDerivAt capIntegral 0 r := by
    intro r hr
    have hd := cap_volume_hasDerivAt_smooth (n := n) (f := f) (h := h) hn hf_nonneg hf_meas hf_bdd hh_cont r
    have hd' : HasDerivAt capIntegral
        (∫ t in (-1 : ℝ)..1,
          if -f t < r * t + h r ∧ r * t + h r < f t then
            (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * (t + deriv h r)
          else 0) r := by
      simpa [capIntegral, W] using hd
    exact hd'.congr_deriv (by simpa [capIntegral, W] using (hderiv_int r hr))
  have hcont_cap : ContinuousOn capIntegral (Set.Ici 0) := by
    have hcont := cap_volume_continuousOn_Ici_zero (n := n) (f := f) (h := h) (by omega)
      hf_nonneg hf_meas hf_bdd (hh_cont.continuousOn.mono (by intro x hx; simp))
    simpa [capIntegral, W] using hcont
  have hcap_const : ∀ r > 0, capIntegral r = capIntegral 0 :=
    const_on_Ioi_of_deriv_zero hderiv_cap hcont_cap
  let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
  have hlast_eq : (⟨d - 1, by omega⟩ : Fin d) = lastFin d := by
    ext; simp [lastFin]
  have hvol_cap : volume.real (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}) = c * capIntegral s := by
    have hbody := body_of_revolution_cap_integrals_even (d := d) (n := n) (a := -1) (b := 1)
      (s := s) (h := h s) hdn hn (by norm_num) hf_nonneg hf_meas
    simpa [capIntegral, W, c, K, hlast_eq] using hbody.1
  let R : ℝ := M + 1
  have hR_gt : M < R := by dsimp [R]; linarith
  have hK_subset : K ⊆ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R} := by
    simpa [K, R] using K_subset_H_large (d := d) (f := f) (M := M) (R := R) hdpos hR_gt hf_nonneg hf_le_M
  have hvol_total : volume.real K = c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), W t z) := by
    have hbody := body_of_revolution_cap_integrals_even (d := d) (n := n) (a := -1) (b := 1)
      (s := 0) (h := R) hdn hn (by norm_num) hf_nonneg hf_meas
    have hinner := inner_total_eq (n := n) (f := f) (M := R) hf_nonneg (by
      intro t ht
      exact le_of_lt (lt_of_le_of_lt (hf_le_M t ht) hR_gt))
    have hvol_inter : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R}) =
        c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), W t z) := by
      have hbody1 : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R}) =
          c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), W t z) := by
        simpa [W, c, K, lastFin] using hbody.1
      have hinner' := inner_total_eq (n := n) (f := f) (M := R) hf_nonneg (by
        intro t ht
        exact le_of_lt (lt_of_le_of_lt (hf_le_M t ht) hR_gt))
      have hinner_eq :
          (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), W t z) =
            ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), W t z := by
        simpa [W] using hinner'
      calc
        volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R})
            = c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), W t z) := hbody1
        _ = c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), W t z) := by rw [hinner_eq]
    have hvolK : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R}) = volume.real K := by
      rw [Set.inter_eq_left.mpr hK_subset]
    rw [hvolK] at hvol_inter
    simpa [W] using hvol_inter
  have hcap0 : capIntegral 0 = (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, W t z) := by
    have h0line : ∀ t ∈ Set.Icc (-1 : ℝ) 1, max (-f t) (min (f t) (0 * t + h 0)) = 0 := by
      intro t ht
      have hf_nonneg_t : 0 ≤ f t := hf_nonneg t ht
      have hmin : min (f t) (0 * t + h 0) = 0 := by
        rw [h0]
        simp [hf_nonneg_t]
      have hmax : max (-f t) 0 = 0 := by
        rw [max_eq_right]
        linarith
      rw [hmin, hmax]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1:ℝ)≤1)] using ht
    have hup := h0line t htIcc
    change (∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + h 0))), W t z) =
      ∫ z in (-f t)..0, W t z
    rw [hup]
  have hhalf := cap_integral_zero_eq_half_total (n := n) hn hf_nonneg
  have hcap0_half : capIntegral 0 = (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), W t z) / 2 := by
    rw [hcap0]
    simpa [W] using hhalf
  have hs_eq : capIntegral s = capIntegral 0 := hcap_const s hs
  calc
    volume.real (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}) = c * capIntegral s := hvol_cap
    _ = c * capIntegral 0 := by rw [hs_eq]
    _ = c * ((∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), W t z) / 2) := by rw [hcap0_half]
    _ = (c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), W t z)) / 2 := by ring
    _ = volume.real K / 2 := by rw [← hvol_total]


end Commons.Geometry.Ulam
