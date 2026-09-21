import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Submission.Commons.Geometry.Ulam.cap_volume_continuousOn_Ici_zero
import Submission.Commons.Geometry.Ulam.cap_slice_hasDerivAt

/-!
# The cap volume derivative, with smooth (not analytic) regularity

Copy of `Submission.Commons.Geometry.Ulam.odd_cap_volume_hasDerivAt` with the analytic hypothesis
`ContDiffOn ℝ ⊤ h Set.univ` replaced by the smooth one `ContDiffOn ℝ ∞ h Set.univ`.  The proof is
unchanged: only continuity of `h` and of `deriv h` (and differentiability of `h`) are used, and all
of these follow from smoothness.  Public result: `Work.OddCaps.odd_cap_volume_hasDerivAt_smooth`.
-/

namespace Work.OddCaps

open MeasureTheory
open Set Filter
open Commons.Geometry.Ulam
open scoped Topology Interval ContDiff

private lemma isBigO_min_sub {F : ℝ} {x : ℝ → ℝ} {s : ℝ}
    (hxO : (fun r : ℝ => x r - x s) =O[𝓝 s] (fun r : ℝ => r - s)) :
    (fun r : ℝ => min F (x r) - min F (x s)) =O[𝓝 s] (fun r : ℝ => r - s) := by
  have hle : ∀ r : ℝ,
      ‖min F (x r) - min F (x s)‖ ≤ ‖x r - x s‖ := by
    intro r
    calc
      ‖min F (x r) - min F (x s)‖ = |min F (x r) - min F (x s)| := by rfl
      _ ≤ |x r - x s| := by
        have h := abs_min_sub_min_le_max F (x r) F (x s)
        simpa [max_eq_left (abs_nonneg (x r - x s))] using h
      _ = ‖x r - x s‖ := by rfl
  refine (Asymptotics.isBigO_of_le (𝓝 s) hle).trans ?_
  simpa using hxO

private lemma odd_cap_slice_hasDerivAt {n : ℕ} {F s t dh : ℝ} {h : ℝ → ℝ}
    (hn : 1 ≤ n) (hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(min F (r * t + h r)),
          (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))
      ((F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2) * (t + dh)) s := by
  let a : ℝ := -F
  let b : ℝ := F
  let g : ℝ → ℝ := fun z => (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)
  let x : ℝ → ℝ := fun r => r * t + h r
  let u : ℝ → ℝ := fun r => min F (x r)
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
    dsimp [u, x]
    exact continuous_min.continuousAt.comp₂ continuousAt_const hx_cont
  have huO : (fun r : ℝ => u r - u s) =O[𝓝 s] (fun r : ℝ => r - s) := by
    dsimp [u, x]
    exact isBigO_min_sub hxO
  have hg_cont : Continuous g := by
    dsimp [g]
    continuity
  have hg_zero_left : g a = 0 := by
    dsimp [g, a]
    have hsqrt : Real.sqrt (F ^ 2 - (-F) ^ 2) = 0 := by simp
    rw [hsqrt, mul_zero]
  have hg_zero_right : g b = 0 := by
    dsimp [g, b]
    have hsqrt : Real.sqrt (F ^ 2 - F ^ 2) = 0 := by simp
    rw [hsqrt, mul_zero]
  have hP_left : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) 0 a := by
    have h := (hg_cont.integral_hasStrictDerivAt a a).hasDerivAt
    simpa [g, hg_zero_left] using h
  have hP_right : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) 0 b := by
    have h := (hg_cont.integral_hasStrictDerivAt a b).hasDerivAt
    simpa [g, hg_zero_right] using h
  by_cases hxs_lt : x s < F
  · have h_event_u : ∀ᶠ r in 𝓝 s, u r = x r := by
      have hxs_upper : x s < b := by dsimp [x, b]; simpa using hxs_lt
      have h_event_upper : ∀ᶠ r in 𝓝 s, x r < b := by
        have hmem : {r : ℝ | x r < b} ∈ 𝓝 s :=
          hx_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hxs_upper)
        exact Filter.eventually_iff.mpr hmem
      filter_upwards [h_event_upper] with r hr
      dsimp [u, x, b]
      rw [min_eq_right hr.le]
    have hP_deriv : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) (g (x s)) (x s) :=
      (hg_cont.integral_hasStrictDerivAt a (x s)).hasDerivAt
    have hcomp : HasDerivAt ((fun y : ℝ => ∫ z in a..y, g z) ∘ x)
        (g (x s) * (t + dh)) s := by
      simpa [Function.comp_def] using hP_deriv.comp s hx
    have h_event : (fun r : ℝ => ∫ z in (-F)..(min F (r * t + h r)),
          (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)) =ᶠ[𝓝 s]
        ((fun y : ℝ => ∫ z in a..y, g z) ∘ x) := by
      filter_upwards [h_event_u] with r hr
      have hr' : min F (r * t + h r) = r * t + h r := by
        simpa [u, x] using hr
      simp [a, g, x, hr']
    have hmain : HasDerivAt
        (fun r : ℝ => ∫ z in (-F)..(min F (r * t + h r)),
          (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))
        (g (x s) * (t + dh)) s :=
      HasDerivAt.congr_of_eventuallyEq hcomp h_event
    simpa [x, g] using hmain
  · have hxs_ge : F ≤ x s := le_of_not_gt hxs_lt
    have hqs : u s = b := by
      dsimp [u, x, b]
      rw [min_eq_left hxs_ge]
    have hqO : (fun r : ℝ => u r - b) =O[𝓝 s] (fun r : ℝ => r - s) := by
      simpa [hqs] using huO
    have hderiv0 : HasDerivAt (fun r : ℝ => ∫ z in a..(u r), g z) 0 s := by
      simpa using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
        (P := fun y : ℝ => ∫ z in a..y, g z) (q := u) (s := s) (b := b)
        hP_right hu_cont hqs hqO
    have hmain : HasDerivAt
        (fun r : ℝ => ∫ z in (-F)..(min F (r * t + h r)),
          (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)) 0 s := by
      simpa [u, a, b, g] using hderiv0
    have hg_zero : g (x s) = 0 := by
      dsimp [g]
      have hnonpos : F ^ 2 - (x s) ^ 2 ≤ 0 := by
        have hx_nonneg : 0 ≤ x s := le_trans hF hxs_ge
        have hsq : F ^ 2 ≤ (x s) ^ 2 := (sq_le_sq₀ hF hx_nonneg).2 hxs_ge
        nlinarith
      have hsqrt : Real.sqrt (F ^ 2 - (x s) ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos hnonpos
      rw [hsqrt, mul_zero]
    have hderiv_eq_zero : (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
        Real.sqrt (F ^ 2 - (s * t + h s) ^ 2) * (t + dh) = 0 := by
      have hxval : s * t + h s = x s := rfl
      rw [hxval]
      change g (x s) * (t + dh) = 0
      rw [hg_zero, zero_mul]
    simpa [x, g, hderiv_eq_zero] using hmain

private lemma odd_inner_integral_eq_clamp {n : ℕ} {F L : ℝ} (hn : 1 ≤ n) (hF : 0 ≤ F) :
    (∫ z in (-F)..(min F L),
        (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)) =
      ∫ z in (-F)..(max (-F) (min F L)),
        (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2) := by
  let W : ℝ → ℝ := fun z => (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)
  have hF_neg : -F ≤ F := by linarith
  by_cases hL : L ≤ -F
  · have hLF : L ≤ F := le_trans hL hF_neg
    have hmin : min F L = L := by rw [min_eq_right hLF]
    have hmax : max (-F) (min F L) = -F := by
      rw [hmin]
      exact max_eq_left hL
    have hWzero : ∫ z in L..(-F), W z = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with z hz
      have hzIoc : z ∈ Ioc L (-F) := by
        simpa [Set.uIoc_of_le hL] using hz
      have hz_le : z ≤ -F := hzIoc.2
      have hnegz_geF : F ≤ -z := by linarith
      have hz_nonneg_neg : 0 ≤ -z := by linarith
      have hsq : F ^ 2 ≤ z ^ 2 := by
        have hsq' : F ^ 2 ≤ (-z) ^ 2 := (sq_le_sq₀ hF hz_nonneg_neg).2 hnegz_geF
        simpa [neg_sq] using hsq'
      have hnonpos : F ^ 2 - z ^ 2 ≤ 0 := by nlinarith
      have hsqrt : Real.sqrt (F ^ 2 - z ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos hnonpos
      dsimp [W]
      rw [hsqrt, mul_zero]
    have hWcont : Continuous W := by dsimp [W]; continuity
    have h_int : IntervalIntegrable W volume (-F) L := hWcont.intervalIntegrable _ _
    have h_int2 : IntervalIntegrable W volume L (-F) := hWcont.intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals_cancel h_int h_int2
    have hlast : (∫ z in (-F)..(-F), W z) = 0 := by simp
    have hsum : (∫ z in (-F)..L, W z) + (∫ z in L..(-F), W z) = 0 := by
      simpa [hlast] using hadd
    rw [hWzero, add_zero] at hsum
    have hmax' : max (-F) L = -F := by simpa [hmin] using hmax
    simpa [hmin, hmax'] using hsum
  · have hlt : -F < L := lt_of_not_ge hL
    by_cases hLF : L ≤ F
    · have hmin : min F L = L := by rw [min_eq_right hLF]
      have hmax : max (-F) (min F L) = L := by
        rw [hmin]
        exact max_eq_right hlt.le
      have hmax' : max (-F) L = L := by simpa [hmin] using hmax
      simpa [hmin, hmax']
    · have hFL : F ≤ L := le_of_not_ge hLF
      have hmin : min F L = F := by rw [min_eq_left hFL]
      have hmax : max (-F) (min F L) = F := by
        rw [hmin]
        exact max_eq_right hF_neg
      have hmax' : max (-F) F = F := by simpa [hmin] using hmax
      simpa [hmin, hmax']

private lemma norm_odd_cap_slice_integral_le {n : ℕ} {f h : ℝ → ℝ} {M a b : ℝ}
    (hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hab : a ≤ b) (hM_nonneg : 0 ≤ M) (hn : 1 ≤ n) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι a b →
      ‖(∫ z in (-f t)..(min (f t) (r * t + h r)),
          (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))‖ ≤
        (2 * M) * ((2 * M ^ 2) ^ (n - 1) * M) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Ioc a b := by
    simpa [Set.uIoc_of_le hab] using ht
  have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  let F : ℝ := f t
  let L : ℝ := r * t + h r
  let W : ℝ → ℝ := fun z => (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)
  have h_eq := odd_inner_integral_eq_clamp (n := n) (F := F) (L := L) hn hft_nonneg
  have hWcont : Continuous W := by dsimp [W]; continuity
  have h_int : IntervalIntegrable W volume (-F) (max (-F) (min F L)) := hWcont.intervalIntegrable _ _
  have h_clamp_mem : max (-F) (min F L) ∈ Set.Icc (-F) F := by
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hlen : |max (-F) (min F L) - (-F)| ≤ 2 * M := by
    have hupper : max (-F) (min F L) ≤ F := h_clamp_mem.2
    have hlower : -F ≤ max (-F) (min F L) := h_clamp_mem.1
    rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
    calc
      max (-F) (min F L) - (-F) ≤ F - (-F) := sub_le_sub hupper le_rfl
      _ = 2 * F := by ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hg_bound : ∀ z ∈ Ι (-F) (max (-F) (min F L)), ‖W z‖ ≤ (2 * M ^ 2) ^ (n - 1) * M := by
    intro z hz
    have hzIoc : z ∈ Ioc (-F) (max (-F) (min F L)) := by
      simpa [Set.uIoc_of_le h_clamp_mem.1] using hz
    have hz_lower : -F ≤ z := le_of_lt hzIoc.1
    have hz_upper : z ≤ F := le_trans hzIoc.2 h_clamp_mem.2
    have hz_abs : |z| ≤ F := abs_le.mpr ⟨hz_lower, hz_upper⟩
    have hz_abs_M : |z| ≤ M := hz_abs.trans (by simpa [abs_of_nonneg hft_nonneg] using hft_le)
    have hsq_le : |F ^ 2 - z ^ 2| ≤ 2 * M ^ 2 := by
      have h1 : |F ^ 2 - z ^ 2| ≤ F ^ 2 + z ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg F, sq_nonneg z]
      have hFsq : F ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
      have hzsq : z ^ 2 ≤ M ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg hM_nonneg] using hz_abs_M
      nlinarith
    have hpow : |(F ^ 2 - z ^ 2) ^ (n - 1)| ≤ (2 * M ^ 2) ^ (n - 1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hsq_le (n - 1)
    have hsqrt : |Real.sqrt (F ^ 2 - z ^ 2)| ≤ M := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have hle_arg : F ^ 2 - z ^ 2 ≤ M ^ 2 := by
        have hFsq : F ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
        nlinarith [sq_nonneg z]
      exact (Real.sqrt_le_left hM_nonneg).2 hle_arg
    dsimp [W]
    simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := -F) (b := max (-F) (min F L))
      (C := (2 * M ^ 2) ^ (n - 1) * M) (f := W) hg_bound
  calc
    ‖∫ z in (-F)..(min F L), W z‖
        = ‖∫ z in (-F)..(max (-F) (min F L)), W z‖ := by rw [← h_eq]
    _ ≤ ((2 * M ^ 2) ^ (n - 1) * M) * |max (-F) (min F L) - (-F)| := hnorm
    _ ≤ ((2 * M ^ 2) ^ (n - 1) * M) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = (2 * M) * ((2 * M ^ 2) ^ (n - 1) * M) := by ring

lemma odd_cap_volume_hasDerivAt_smooth {n : ℕ} {f h : ℝ → ℝ} {a b : ℝ}
    (hn : 1 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc a b))
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in a..b,
          ∫ z in (-f t)..(min (f t) (r * t + h r)),
            (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))
      (∫ t in a..b,
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) s := by
  classical
  let F : ℝ → ℝ → ℝ := fun r t =>
    ∫ z in (-f t)..(min (f t) (r * t + h r)),
      (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  let F' : ℝ → ℝ → ℝ := fun r t =>
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
  let B : ℝ := (2 * M ^ 2) ^ (n - 1) * M
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  let bound : ℝ → ℝ := fun t => B * (|t| + C)
  have hbound_nonneg : ∀ t, 0 ≤ bound t := by
    intro t; dsimp [bound]; positivity
  have hF_meas : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable (F r) (volume.restrict (Ι a b)) := by
    filter_upwards [hS_mem] with r hr
    have hL : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU : Measurable (fun t : ℝ => min (f t) (r * t + h r)) := by fun_prop
    have hg : Measurable (Function.uncurry (fun t z : ℝ => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))) := by fun_prop
    exact (aeStronglyMeasurable_intervalIntegral_param hL hU hg).restrict
  have hF_int : IntervalIntegrable (F s) volume a b := by
    rw [intervalIntegrable_iff]
    have hmeas : AEStronglyMeasurable (F s) (volume.restrict (Ι a b)) := by
      exact hF_meas.self_of_nhds
    have hbnd' := norm_odd_cap_slice_integral_le (n := n) (f := f) (h := h) (M := M) (a := a) (b := b)
      hf_le_M hf_nonneg hab (le_of_lt hMpos) hn s
    have hbnd : ∀ᵐ t ∂volume.restrict (Ι a b), ‖F s t‖ ≤ (2 * M) * B := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      exact ht
    exact IntegrableOn.of_bound (by
        rw [Set.uIoc_of_le hab]
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top) hmeas _ hbnd
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Ι a b)) := by
    have h_then_meas : Measurable (fun t : ℝ =>
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) := by
      fun_prop
    exact h_then_meas.aestronglyMeasurable.restrict
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
      have hbase_le : f t ^ 2 - (r * t + h r) ^ 2 ≤ 2 * M ^ 2 := by
        have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
        have hline_sq_nonneg : 0 ≤ (r * t + h r) ^ 2 := sq_nonneg _
        nlinarith
      have hW_le : |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)| ≤ B := by
        have hpow : |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| ≤ (2 * M ^ 2) ^ (n - 1) := by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [abs_of_nonneg hbase_nonneg] using hbase_le) (n - 1)
        have hsqrt : |Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)| ≤ M := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          have hle_arg : f t ^ 2 - (r * t + h r) ^ 2 ≤ M ^ 2 := by
            have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
            nlinarith [sq_nonneg (r * t + h r)]
          exact (Real.sqrt_le_left (le_of_lt hMpos)).2 hle_arg
        dsimp [B]
        simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
      have hlin_le : |t + deriv h r| ≤ |t| + C := by
        calc |t + deriv h r| ≤ |t| + |deriv h r| := abs_add_le t (deriv h r)
          _ ≤ |t| + C := by nlinarith [hderiv_bound r hr]
      dsimp [F', bound]
      rw [abs_mul]
      exact mul_le_mul hW_le hlin_le (abs_nonneg _) hB_nonneg
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
    exact odd_cap_slice_hasDerivAt (n := n) (F := f t) (s := r) (t := t) (dh := deriv h r)
      (h := h) hn hft_nonneg hh_deriv
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := F) (F' := F') (x₀ := s) (s := S) (μ := volume) (a := a) (b := b)
    hS_mem hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  exact hmain.2

end Work.OddCaps