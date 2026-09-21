import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even
import Submission.Commons.Geometry.Ulam.cap_volume_continuousOn_Ici_zero
import Submission.Commons.Geometry.Ulam.cap_slice_hasDerivAt
import Submission.Commons.Geometry.Ulam.moment_deriv_zero_abs_lt_one

namespace Commons.Geometry.Ulam

open MeasureTheory
open Set Filter
open scoped ContDiff Pointwise RealInnerProductSpace BigOperators Topology Interval

set_option autoImplicit false
set_option maxHeartbeats 800000



set_option autoImplicit false

/-! Helper lemmas for the even profile cap volume half theorem. -/

lemma even_profile_nonneg_Icc {f : ℝ → ℝ}
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t := by
  intro t ht
  have hmin := hf_conc.min_le_of_mem_Icc (x := (-1 : ℝ)) (y := (1 : ℝ)) (z := t)
    (by norm_num) (by norm_num) (by simpa [Set.mem_Icc] using ht)
  rw [hf_left, hf_right] at hmin
  simpa using hmin

lemma even_profile_measurable {f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ⊤ f (Set.Ioo (-1 : ℝ) 1))
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

lemma even_profile_bounded {f : ℝ → ℝ}
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0) :
    Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) := by
  classical
  let R : ℝ := |f 0|
  have hR_nonneg : 0 ≤ R := by dsimp [R]; exact abs_nonneg _
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hleft_mem : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hright_mem : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hf0_nonneg : 0 ≤ f 0 := by
    have hmin := hf_conc.min_le_of_mem_Icc (x := (-1 : ℝ)) (y := (1 : ℝ)) (z := (0 : ℝ))
      hleft_mem hright_mem h0_mem
    rw [hf_left, hf_right] at hmin
    simpa using hmin
  have h_lower : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f x := by
    intro x hx
    have hmin := hf_conc.min_le_of_mem_Icc (x := (-1 : ℝ)) (y := (1 : ℝ)) (z := x)
      hleft_mem hright_mem hx
    rw [hf_left, hf_right] at hmin
    simpa using hmin
  have h_upper : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≤ 2 * R := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · have hx_lt_one : x < 1 := by
        have hx1 : x ≤ 1 := hx.2
        by_contra hnot
        have hle : (1 : ℝ) ≤ x := le_of_not_gt hnot
        have : (1 : ℝ) ≤ 0 := le_trans hle hx0
        norm_num at this
      let lam : ℝ := 1 / (1 - x)
      have hden_pos : 0 < 1 - x := by linarith
      have hlam_pos : 0 < lam := by dsimp [lam]; positivity
      have hden_ge_one : 1 ≤ 1 - x := by linarith
      have hlam_le_one : lam ≤ 1 := by
        dsimp [lam]
        rw [div_le_one hden_pos]
        exact hden_ge_one
      have hlam_ge_half : 1 / 2 ≤ lam := by
        dsimp [lam]
        have hden_le : 1 - x ≤ 2 := by linarith [hx.1]
        field_simp [hden_pos.ne']
        nlinarith
      have hsum : lam + (1 - lam) = 1 := by ring
      have hzero_eq : lam * x + (1 - lam) = 0 := by
        dsimp [lam]
        field_simp [hden_pos.ne']
        ring
      have hconc := hf_conc.2 hx hright_mem (le_of_lt hlam_pos) (by linarith) hsum
      have hconc' : lam * f x + (1 - lam) * f 1 ≤ f 0 := by
        simpa [hzero_eq, smul_eq_mul] using hconc
      have hfx_le : lam * f x ≤ f 0 := by
        simpa [hf_right] using hconc'
      have hfx_nonneg : 0 ≤ f x := h_lower x hx
      have h_inv_nonneg : 0 ≤ 1 / lam := by positivity
      have hlam_inv_le : 1 / lam ≤ 2 := by
        rw [div_le_iff₀ hlam_pos]
        nlinarith [hlam_ge_half]
      have hfx_eq : f x = (lam * f x) * (1 / lam) := by
        field_simp [ne_of_gt hlam_pos]
      calc
        f x = (lam * f x) * (1 / lam) := hfx_eq
        _ ≤ f 0 * (1 / lam) := mul_le_mul_of_nonneg_right hfx_le h_inv_nonneg
        _ ≤ R * 2 := by
          have hf0_le_R : f 0 ≤ R := by dsimp [R]; exact le_abs_self _
          nlinarith [hf0_le_R, hlam_inv_le, hf0_nonneg, hR_nonneg]
        _ = 2 * R := by ring
    · have hx_gt : 0 < x := lt_of_not_ge hx0
      have hx_gt_neg : -1 < x := by linarith [hx_gt]
      let mu : ℝ := 1 / (x + 1)
      have hden_pos : 0 < x + 1 := by linarith
      have hmu_pos : 0 < mu := by dsimp [mu]; positivity
      have hden_ge_one : 1 ≤ x + 1 := by linarith
      have hmu_le_one : mu ≤ 1 := by
        dsimp [mu]
        rw [div_le_one hden_pos]
        exact hden_ge_one
      have hmu_ge_half : 1 / 2 ≤ mu := by
        dsimp [mu]
        have hden_le : x + 1 ≤ 2 := by linarith [hx.2]
        field_simp [hden_pos.ne']
        nlinarith
      have hsum : (1 - mu) + mu = 1 := by ring
      have hzero_eq : mu - 1 + mu * x = 0 := by
        dsimp [mu]
        field_simp [hden_pos.ne']
        ring
      have hnonneg_left : 0 ≤ 1 - mu := by linarith
      have hconc := hf_conc.2 hleft_mem hx hnonneg_left (le_of_lt hmu_pos) hsum
      have hconc' : (1 - mu) * f (-1) + mu * f x ≤ f 0 := by
        simpa [hzero_eq, smul_eq_mul] using hconc
      have hfx_le : mu * f x ≤ f 0 := by
        simpa [hf_left] using hconc'
      have hfx_nonneg : 0 ≤ f x := h_lower x hx
      have h_inv_nonneg : 0 ≤ 1 / mu := by positivity
      have hmu_inv_le : 1 / mu ≤ 2 := by
        rw [div_le_iff₀ hmu_pos]
        nlinarith [hmu_ge_half]
      have hfx_eq : f x = (mu * f x) * (1 / mu) := by
        field_simp [ne_of_gt hmu_pos]
      calc
        f x = (mu * f x) * (1 / mu) := hfx_eq
        _ ≤ f 0 * (1 / mu) := mul_le_mul_of_nonneg_right hfx_le h_inv_nonneg
        _ ≤ R * 2 := by
          have hf0_le_R : f 0 ≤ R := by dsimp [R]; exact le_abs_self _
          nlinarith [hf0_le_R, hmu_inv_le, hf0_nonneg, hR_nonneg]
        _ = 2 * R := by ring
  have h_abs_le : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ 2 * R := by
    intro x hx
    rw [abs_le]
    constructor
    · have hnonneg : 0 ≤ f x := h_lower x hx
      nlinarith [hR_nonneg]
    · exact h_upper x hx
  rw [isBounded_iff_forall_norm_le]
  refine ⟨3 * R + 1, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hx_abs := h_abs_le x hx
  norm_num [Real.norm_eq_abs]
  nlinarith [hR_nonneg]

lemma cap_volume_hasDerivAt {n : ℕ} {f h : ℝ → ℝ}
    (hn : 2 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1))
    (hh_cont : ContDiffOn ℝ ⊤ h Set.univ)
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


lemma concaveOn_affine (s h a b : ℝ) :
    ConcaveOn ℝ (Set.Icc a b) (fun t : ℝ => s * t + h) := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy p q hp hq hpq
  simp only [smul_eq_mul]
  calc
    p * (s * x + h) + q * (s * y + h) = s * (p * x + q * y) + h * (p + q) := by ring
    _ = s * (p * x + q * y) + h := by rw [hpq]; ring
    _ ≤ s * (p * x + q * y) + h := le_rfl

lemma concaveOn_sub_affine (f : ℝ → ℝ) (s h a b : ℝ)
    (hf : ConcaveOn ℝ (Set.Icc a b) f) :
    ConcaveOn ℝ (Set.Icc a b) (fun t => f t - (s * t + h)) := by
  have hlin : ConcaveOn ℝ (Set.Icc a b) (fun t : ℝ => - (s * t + h)) := by
    have hpos := concaveOn_affine (-s) (-h) a b
    exact hpos.congr (by intro x hx; ring)
  have hadd := hf.add hlin
  exact hadd.congr (by intro x hx; simp [sub_eq_add_neg])

lemma concaveOn_add_affine (f : ℝ → ℝ) (s h a b : ℝ)
    (hf : ConcaveOn ℝ (Set.Icc a b) f) :
    ConcaveOn ℝ (Set.Icc a b) (fun t => f t + (s * t + h)) := by
  have hlin : ConcaveOn ℝ (Set.Icc a b) (fun t : ℝ => s * t + h) := concaveOn_affine s h a b
  have hadd := hf.add hlin
  exact hadd.congr (by intro x hx; simp)

lemma concave_nonneg_between_of_zero {α β u v : ℝ} {g : ℝ → ℝ}
    (hαu : α ≤ u) (huv : u < v) (hvβ : v ≤ β)
    (hg : ConcaveOn ℝ (Set.Icc α β) g)
    (hgu : g u = 0) (hgv : g v = 0) :
    (∀ t ∈ Set.Icc u v, 0 ≤ g t) ∧
    (∀ t ∈ Set.Icc α u, g t ≤ 0) ∧
    (∀ t ∈ Set.Icc v β, g t ≤ 0) := by
  have hu_mem : u ∈ Set.Icc α β := ⟨hαu, le_trans huv.le hvβ⟩
  have hv_mem : v ∈ Set.Icc α β := ⟨le_trans hαu huv.le, hvβ⟩
  constructor
  · intro t ht
    have hden : 0 < v - u := sub_pos.mpr huv
    let a : ℝ := (v - t) / (v - u)
    let b : ℝ := (t - u) / (v - u)
    have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg (sub_nonneg.mpr ht.2) (le_of_lt hden)
    have hb : 0 ≤ b := by dsimp [b]; exact div_nonneg (sub_nonneg.mpr ht.1) (le_of_lt hden)
    have hab : a + b = 1 := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
    have hcombo : a * u + b * v = t := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
    have hconc := hg.2 hu_mem hv_mem ha hb hab
    simpa [smul_eq_mul, hgu, hgv, hcombo] using hconc
  constructor
  · intro t ht
    by_cases htu : t = u
    · subst t; simp [hgu]
    · have ht_lt : t < u := lt_of_le_of_ne ht.2 htu
      have hden : 0 < v - t := by linarith
      let a : ℝ := (v - u) / (v - t)
      let b : ℝ := (u - t) / (v - t)
      have ha_pos : 0 < a := by dsimp [a]; exact div_pos (sub_pos.mpr huv) hden
      have hb_pos : 0 < b := by dsimp [b]; exact div_pos (sub_pos.mpr ht_lt) hden
      have hab : a + b = 1 := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
      have hcombo : a * t + b * v = u := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
      have ht_mem : t ∈ Set.Icc α β := ⟨ht.1, le_trans ht.2 (le_trans huv.le hvβ)⟩
      have hconc := hg.2 ht_mem hv_mem (le_of_lt ha_pos) (le_of_lt hb_pos) hab
      have hle : a * g t + b * g v ≤ g u := by simpa [smul_eq_mul, hcombo] using hconc
      rw [hgv, hgu] at hle
      have hle' : a * g t ≤ 0 := by simpa using hle
      rcases (mul_nonpos_iff.mp hle') with h | h
      · exact h.2
      · linarith
  · intro t ht
    by_cases htv : t = v
    · subst t; simp [hgv]
    · have hv_lt : v < t := lt_of_le_of_ne ht.1 (Ne.symm htv)
      have hden : 0 < t - u := by linarith
      let a : ℝ := (t - v) / (t - u)
      let b : ℝ := (v - u) / (t - u)
      have ha_pos : 0 < a := by dsimp [a]; exact div_pos (sub_pos.mpr hv_lt) hden
      have hb_pos : 0 < b := by dsimp [b]; exact div_pos (sub_pos.mpr huv) hden
      have hab : a + b = 1 := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
      have hcombo : a * u + b * t = v := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
      have ht_mem : t ∈ Set.Icc α β := ⟨le_trans hαu (le_trans huv.le hv_lt.le), ht.2⟩
      have hconc := hg.2 hu_mem ht_mem (le_of_lt ha_pos) (le_of_lt hb_pos) hab
      have hle : a * g u + b * g t ≤ g v := by simpa [smul_eq_mul, hcombo] using hconc
      rw [hgu, hgv] at hle
      have hle' : b * g t ≤ 0 := by simpa using hle
      rcases (mul_nonpos_iff.mp hle') with h | h
      · exact h.2
      · linarith

lemma concave_nonneg_between_of_zero_left {α β u v : ℝ} {g : ℝ → ℝ}
    (hαu : α ≤ u) (huv : u < v) (hvβ : v ≤ β)
    (hg : ConcaveOn ℝ (Set.Icc α β) g)
    (hgu : g u = 0) (hgv_pos : 0 < g v) :
    (∀ t ∈ Set.Icc u v, 0 ≤ g t) ∧
    (∀ t ∈ Set.Icc α u, g t ≤ 0) := by
  have hu_mem : u ∈ Set.Icc α β := ⟨hαu, le_trans huv.le hvβ⟩
  have hv_mem : v ∈ Set.Icc α β := ⟨le_trans hαu huv.le, hvβ⟩
  constructor
  · intro t ht
    have hden : 0 < v - u := sub_pos.mpr huv
    let a : ℝ := (v - t) / (v - u)
    let b : ℝ := (t - u) / (v - u)
    have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg (sub_nonneg.mpr ht.2) (le_of_lt hden)
    have hb : 0 ≤ b := by dsimp [b]; exact div_nonneg (sub_nonneg.mpr ht.1) (le_of_lt hden)
    have hab : a + b = 1 := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
    have hcombo : a * u + b * v = t := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
    have hconc := hg.2 hu_mem hv_mem ha hb hab
    have hle : a * g u + b * g v ≤ g t := by simpa [smul_eq_mul, hcombo] using hconc
    have hle' : b * g v ≤ g t := by simpa [hgu] using hle
    have hb_nonneg : 0 ≤ b := hb
    have hbv_nonneg : 0 ≤ b * g v := mul_nonneg hb_nonneg (le_of_lt hgv_pos)
    simpa using hbv_nonneg.trans hle'
  · intro t ht
    by_cases htu : t = u
    · subst t; simp [hgu]
    · have ht_lt : t < u := lt_of_le_of_ne ht.2 htu
      by_contra hgt
      have hgt_pos : 0 < g t := lt_of_not_ge hgt
      have hden : 0 < v - t := by linarith
      let a : ℝ := (v - u) / (v - t)
      let b : ℝ := (u - t) / (v - t)
      have ha_pos : 0 < a := by dsimp [a]; exact div_pos (sub_pos.mpr huv) hden
      have hb_pos : 0 < b := by dsimp [b]; exact div_pos (sub_pos.mpr ht_lt) hden
      have hab : a + b = 1 := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
      have hcombo : a * t + b * v = u := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
      have ht_mem : t ∈ Set.Icc α β := ⟨ht.1, le_trans ht.2 (le_trans huv.le hvβ)⟩
      have hconc := hg.2 ht_mem hv_mem (le_of_lt ha_pos) (le_of_lt hb_pos) hab
      have hle : a * g t + b * g v ≤ g u := by simpa [smul_eq_mul, hcombo] using hconc
      rw [hgu] at hle
      have hpos : 0 < a * g t + b * g v := add_pos (mul_pos ha_pos hgt_pos) (mul_pos hb_pos hgv_pos)
      linarith

lemma concave_nonneg_between_of_zero_right {α β u v : ℝ} {g : ℝ → ℝ}
    (hαu : α ≤ u) (huv : u < v) (hvβ : v ≤ β)
    (hg : ConcaveOn ℝ (Set.Icc α β) g)
    (hgu_pos : 0 < g u) (hgv : g v = 0) :
    (∀ t ∈ Set.Icc u v, 0 ≤ g t) ∧
    (∀ t ∈ Set.Icc v β, g t ≤ 0) := by
  have hu_mem : u ∈ Set.Icc α β := ⟨hαu, le_trans huv.le hvβ⟩
  have hv_mem : v ∈ Set.Icc α β := ⟨le_trans hαu huv.le, hvβ⟩
  constructor
  · intro t ht
    have hden : 0 < v - u := sub_pos.mpr huv
    let a : ℝ := (v - t) / (v - u)
    let b : ℝ := (t - u) / (v - u)
    have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg (sub_nonneg.mpr ht.2) (le_of_lt hden)
    have hb : 0 ≤ b := by dsimp [b]; exact div_nonneg (sub_nonneg.mpr ht.1) (le_of_lt hden)
    have hab : a + b = 1 := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
    have hcombo : a * u + b * v = t := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
    have hconc := hg.2 hu_mem hv_mem ha hb hab
    have hle : a * g u + b * g v ≤ g t := by simpa [smul_eq_mul, hcombo] using hconc
    have hle' : a * g u ≤ g t := by simpa [hgv] using hle
    have ha_nonneg : 0 ≤ a := ha
    have hau_nonneg : 0 ≤ a * g u := mul_nonneg ha_nonneg (le_of_lt hgu_pos)
    simpa using hau_nonneg.trans hle'
  · intro t ht
    by_cases htv : t = v
    · subst t; simp [hgv]
    · have hv_lt : v < t := lt_of_le_of_ne ht.1 (Ne.symm htv)
      by_contra hgt
      have hgt_pos : 0 < g t := lt_of_not_ge hgt
      have hden : 0 < t - u := by linarith
      let a : ℝ := (t - v) / (t - u)
      let b : ℝ := (v - u) / (t - u)
      have ha_pos : 0 < a := by dsimp [a]; exact div_pos (sub_pos.mpr hv_lt) hden
      have hb_pos : 0 < b := by dsimp [b]; exact div_pos (sub_pos.mpr huv) hden
      have hab : a + b = 1 := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
      have hcombo : a * u + b * t = v := by dsimp [a,b]; field_simp [ne_of_gt hden]; ring
      have ht_mem : t ∈ Set.Icc α β := ⟨le_trans hαu (le_trans huv.le hv_lt.le), ht.2⟩
      have hconc := hg.2 hu_mem ht_mem (le_of_lt ha_pos) (le_of_lt hb_pos) hab
      have hle : a * g u + b * g t ≤ g v := by simpa [smul_eq_mul, hcombo] using hconc
      rw [hgv] at hle
      have hpos : 0 < a * g u + b * g t := add_pos (mul_pos ha_pos hgu_pos) (mul_pos hb_pos hgt_pos)
      linarith

lemma eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos {f L : ℝ}
    (hfsq : f ^ 2 = L ^ 2) (hf : 0 ≤ f) (hL : L ≤ 0) : f = -L := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hfsq with h | h
  · have hL0 : L = 0 := by
      have hfL : f = L := h
      have hL_nonneg : 0 ≤ L := by linarith
      linarith
    linarith
  · exact h

lemma eq_of_sq_eq_sq_of_nonneg_of_nonneg {f L : ℝ}
    (hfsq : f ^ 2 = L ^ 2) (hf : 0 ≤ f) (hL : 0 ≤ L) : f = L := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hfsq with h | h
  · exact h
  · have hL0 : L = 0 := by
      have hfL : f = -L := h
      have hL_nonpos : L ≤ 0 := by linarith
      linarith
    linarith

lemma active_nonneg_outside_of_roots_inside
    {f : ℝ → ℝ} {s h a b : ℝ} (hs : 0 < s)
    (ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1) (hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hfa_sq : f a ^ 2 = (s * a + h) ^ 2)
    (hfb_sq : f b ^ 2 = (s * b + h) ^ 2) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, (-f t < s * t + h ∧ s * t + h < f t) → a ≤ t ∧ t ≤ b) ∧
    (∀ t ∈ Set.Icc a b, 0 ≤ f t - (s * t + h) ∧ 0 ≤ f t + (s * t + h)) := by
  let L : ℝ → ℝ := fun t => s * t + h
  have hLmono : Monotone L := by
    intro u v huv
    dsimp [L]
    have hle : s * u ≤ s * v := mul_le_mul_of_nonneg_left huv (le_of_lt hs)
    linarith
  have hg_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => f t - L t) := by
    dsimp [L]
    exact concaveOn_sub_affine f s h (-1) 1 hf_conc
  have hq_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => f t + L t) := by
    dsimp [L]
    exact concaveOn_add_affine f s h (-1) 1 hf_conc
  have ha_Icc : a ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioo_subset_Icc_self ha_mem
  have hb_Icc : b ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioo_subset_Icc_self hb_mem
  have hfa_nonneg : 0 ≤ f a := hf_nonneg a ha_Icc
  have hfb_nonneg : 0 ≤ f b := hf_nonneg b hb_Icc
  have hfa_pos : 0 < f a := hf_pos a ha_mem
  have hfb_pos : 0 < f b := hf_pos b hb_mem
  have hLa : L a = s * a + h := rfl
  have hLb : L b = s * b + h := rfl
  have hab : a < b := lt_trans ha_neg hb_pos
  have hsq_a : f a ^ 2 = (L a) ^ 2 := by simpa [L] using hfa_sq
  have hsq_b : f b ^ 2 = (L b) ^ 2 := by simpa [L] using hfb_sq
  by_cases hLa_nonpos : L a ≤ 0
  · by_cases hLb_nonpos : L b ≤ 0
    · have hLa_neg : L a < 0 := lt_of_le_of_ne hLa_nonpos (by
        intro hLa0
        have hfa0 : f a = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_a hfa_nonneg hLa_nonpos
          linarith
        linarith)
      have hLb_neg : L b < 0 := lt_of_le_of_ne hLb_nonpos (by
        intro hLb0
        have hfb0 : f b = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_b hfb_nonneg hLb_nonpos
          linarith
        linarith)
      have hqa : (fun t => f t + L t) a = 0 := by
        dsimp
        have hfa := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_a hfa_nonneg (le_of_lt hLa_neg)
        linarith
      have hqb : (fun t => f t + L t) b = 0 := by
        dsimp
        have hfb := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_b hfb_nonneg (le_of_lt hLb_neg)
        linarith
      have hq := concave_nonneg_between_of_zero (α := (-1 : ℝ)) (β := 1) (u := a) (v := b)
        (hαu := ha_Icc.1) (huv := hab) (hvβ := hb_Icc.2) hq_conc hqa hqb
      constructor
      · intro t ht hact
        by_cases hta : a ≤ t
        · by_cases htb : t ≤ b
          · exact ⟨hta, htb⟩
          · have hgt : b < t := lt_of_not_ge htb
            have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2.2 t ⟨le_of_lt hgt, ht.2⟩
            have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
            linarith
        · have hlt : t < a := lt_of_not_ge hta
          have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2.1 t ⟨ht.1, le_of_lt hlt⟩
          have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
          linarith
      · intro t ht
        have hLt_nonpos : L t ≤ 0 := le_trans (hLmono ht.2) hLb_nonpos
        have ht_Icc : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_trans ha_Icc.1 ht.1, le_trans ht.2 hb_Icc.2⟩
        have hft_nonneg : 0 ≤ f t := hf_nonneg t ht_Icc
        have hg_nonneg : 0 ≤ f t - L t := by linarith
        exact ⟨by simpa [L] using hg_nonneg, hq.1 t ht⟩
    · have hLa_neg : L a < 0 := lt_of_le_of_ne hLa_nonpos (by
        intro hLa0
        have hfa0 : f a = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_a hfa_nonneg hLa_nonpos
          linarith
        linarith)
      have hLb_pos : 0 < L b := lt_of_not_ge hLb_nonpos
      have hqa : (fun t => f t + L t) a = 0 := by
        dsimp
        have hfa := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_a hfa_nonneg (le_of_lt hLa_neg)
        linarith
      have hgb : (fun t => f t - L t) b = 0 := by
        dsimp
        have hfb := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_b hfb_nonneg (le_of_lt hLb_pos)
        linarith
      have hq_b_pos : 0 < (fun t => f t + L t) b := by
        dsimp [L]
        have hfb := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_b hfb_nonneg (le_of_lt hLb_pos)
        linarith
      have hg_a_pos : 0 < (fun t => f t - L t) a := by
        dsimp [L]
        have hfa := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_a hfa_nonneg (le_of_lt hLa_neg)
        linarith
      have hq := concave_nonneg_between_of_zero_left (α := (-1 : ℝ)) (β := 1) (u := a) (v := b)
        (hαu := ha_Icc.1) (huv := hab) (hvβ := hb_Icc.2) hq_conc hqa hq_b_pos
      have hg := concave_nonneg_between_of_zero_right (α := (-1 : ℝ)) (β := 1) (u := a) (v := b)
        (hαu := ha_Icc.1) (huv := hab) (hvβ := hb_Icc.2) hg_conc hg_a_pos hgb
      constructor
      · intro t ht hact
        by_cases hta : a ≤ t
        · by_cases htb : t ≤ b
          · exact ⟨hta, htb⟩
          · have hgt : b < t := lt_of_not_ge htb
            have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2 t ⟨le_of_lt hgt, ht.2⟩
            have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
            linarith
        · have hlt : t < a := lt_of_not_ge hta
          have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2 t ⟨ht.1, le_of_lt hlt⟩
          have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
          linarith
      · intro t ht
        exact ⟨hg.1 t ht, hq.1 t ht⟩
  · have hLa_pos : 0 < L a := lt_of_not_ge hLa_nonpos
    have hLb_pos : 0 < L b := lt_of_lt_of_le hLa_pos (hLmono (le_of_lt hab))
    have hga : (fun t => f t - L t) a = 0 := by
      dsimp
      have hfa := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_a hfa_nonneg (le_of_lt hLa_pos)
      linarith
    have hgb : (fun t => f t - L t) b = 0 := by
      dsimp
      have hfb := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_b hfb_nonneg (le_of_lt hLb_pos)
      linarith
    have hg := concave_nonneg_between_of_zero (α := (-1 : ℝ)) (β := 1) (u := a) (v := b)
      (hαu := ha_Icc.1) (huv := hab) (hvβ := hb_Icc.2) hg_conc hga hgb
    constructor
    · intro t ht hact
      by_cases hta : a ≤ t
      · by_cases htb : t ≤ b
        · exact ⟨hta, htb⟩
        · have hgt : b < t := lt_of_not_ge htb
          have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2.2 t ⟨le_of_lt hgt, ht.2⟩
          have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
          linarith
      · have hlt : t < a := lt_of_not_ge hta
        have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2.1 t ⟨ht.1, le_of_lt hlt⟩
        have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
        linarith
    · intro t ht
      have hLt_nonneg : 0 ≤ L t := le_trans hLa_pos.le (hLmono ht.1)
      have ht_Icc : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_trans ha_Icc.1 ht.1, le_trans ht.2 hb_Icc.2⟩
      have hft_nonneg : 0 ≤ f t := hf_nonneg t ht_Icc
      have hq_nonneg : 0 ≤ f t + L t := by linarith
      exact ⟨hg.1 t ht, by simpa [L] using hq_nonneg⟩

lemma roots_inside_of_abs_h_lt_s
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    {s : ℝ} (hs : 0 < s) (hneg : -s < h s) (hpos : h s < s) :
    -x s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  constructor
  · -- left root -x s in Ioo
    have ha_neg : -x s < 0 := by linarith
    have ha_gt : -1 < -x s := by
      by_contra hle
      have hx_ge_one : 1 ≤ x s := by linarith
      have hL_ne : s * (-x s) + h s ≠ 0 := by
        have hL_lt : s * (-x s) + h s < 0 := by
          have hsx : s ≤ s * x s := by
            have hmul := mul_le_mul_of_nonneg_left hx_ge_one (le_of_lt hs)
            simpa using hmul
          have h1 : s * (-x s) ≤ -s := by
            have : s * (-x s) = - (s * x s) := by ring
            rw [this]
            linarith
          nlinarith [h1, hpos]
        exact ne_of_lt hL_lt
      have hfx_sq_pos : 0 < (s * (-x s) + h s) ^ 2 := sq_pos_of_ne_zero hL_ne
      have hfx_ne : f (-x s) ≠ 0 := by
        intro hf0
        have : f (-x s) ^ 2 = 0 := by simp [hf0]
        rw [hfx_sq] at this
        linarith
      have hx_support : -x s ∈ Function.support f := by
        rwa [Function.mem_support]
      have hx_Icc : -x s ∈ Set.Icc (-1 : ℝ) 1 := hf_support hx_support
      have hx_ge_neg1 : -1 ≤ -x s := hx_Icc.1
      have hx_le : -x s ≤ -1 := by linarith
      have hx_eq : -x s = -1 := le_antisymm hx_le hx_ge_neg1
      have : f (-x s) = 0 := by simp [hx_eq, hf_left]
      exact hfx_ne this
    exact ⟨ha_gt, by linarith⟩
  · -- right root y s in Ioo
    have hb_pos : 0 < y s := hypos
    have hb_lt : y s < 1 := by
      by_contra hle
      have hy_ge_one : 1 ≤ y s := by linarith
      have hL_ne : s * y s + h s ≠ 0 := by
        have hL_gt : 0 < s * y s + h s := by
          have h1 : s ≤ s * y s := by
            have : s * 1 ≤ s * y s := mul_le_mul_of_nonneg_left hy_ge_one (le_of_lt hs)
            simpa using this
          nlinarith [h1, hneg]
        exact ne_of_gt hL_gt
      have hfy_sq_pos : 0 < (s * y s + h s) ^ 2 := sq_pos_of_ne_zero hL_ne
      have hfy_ne : f (y s) ≠ 0 := by
        intro hf0
        have : f (y s) ^ 2 = 0 := by simp [hf0]
        rw [hfy_sq] at this
        linarith
      have hy_support : y s ∈ Function.support f := by
        rwa [Function.mem_support]
      have hy_Icc : y s ∈ Set.Icc (-1 : ℝ) 1 := hf_support hy_support
      have hy_le_one : y s ≤ 1 := hy_Icc.2
      have hy_eq : y s = 1 := le_antisymm hy_le_one hy_ge_one
      have : f (y s) = 0 := by simp [hy_eq, hf_right]
      exact hfy_ne this
    exact ⟨by linarith, hb_lt⟩

lemma not_eq_abs_affine_of_concave_and_abs_h_lt_s
    {f : ℝ → ℝ} {s h a b : ℝ}
    (hs : 0 < s) (hneg : -s < h) (hpos : h < s)
    (ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1) (hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (h_eq : ∀ t ∈ Set.Icc a b, f t = |s * t + h|) : False := by
  let L : ℝ → ℝ := fun t => s * t + h
  have hab : a < b := lt_trans ha_neg hb_pos
  have ha_Icc : a ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioo_subset_Icc_self ha_mem
  have hb_Icc : b ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioo_subset_Icc_self hb_mem
  have hLmono : StrictMono L := by
    intro u v huv
    dsimp [L]
    nlinarith [mul_lt_mul_of_pos_left huv hs]
  have hL_cont : Continuous L := by
    dsimp [L]
    fun_prop
  have hg_conc : ConcaveOn ℝ (Set.Icc a b) (fun t => |L t|) := by
    have hf_conc_sub : ConcaveOn ℝ (Set.Icc a b) f :=
      hf_conc.subset (by
        intro t ht
        exact ⟨le_trans ha_Icc.1 ht.1, le_trans ht.2 hb_Icc.2⟩) (convex_Icc a b)
    exact hf_conc_sub.congr (by intro t ht; simpa [L] using h_eq t ht)
  have hsign : (∀ t ∈ Set.Icc a b, 0 ≤ L t) ∨ (∀ t ∈ Set.Icc a b, L t ≤ 0) := by
    by_cases hLa_nonneg : 0 ≤ L a
    · left
      intro t ht
      exact hLa_nonneg.trans (hLmono.monotone ht.1)
    · have hLa_neg : L a < 0 := lt_of_not_ge hLa_nonneg
      by_cases hLb_nonpos : L b ≤ 0
      · right
        intro t ht
        exact (hLmono.monotone ht.2).trans hLb_nonpos
      · have hLb_pos : 0 < L b := lt_of_not_ge hLb_nonpos
        have hzero_in : (0 : ℝ) ∈ Set.Icc (L a) (L b) := ⟨le_of_lt hLa_neg, le_of_lt hLb_pos⟩
        have hzero := intermediate_value_Icc hab.le hL_cont.continuousOn hzero_in
        rcases hzero with ⟨r, hr_Icc, hrL⟩
        have hra : a < r := by
          have : L a < L r := by simpa [hrL] using hLa_neg
          exact hLmono.lt_iff_lt.mp this
        have hrb : r < b := by
          have : L r < L b := by simpa [hrL] using hLb_pos
          exact hLmono.lt_iff_lt.mp this
        have hdom_a : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
        have hdom_b : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
        have hdom_r : r ∈ Set.Icc a b := ⟨le_of_lt hra, le_of_lt hrb⟩
        have hslope := hg_conc.slope_anti_adjacent hdom_a hdom_b hra hrb
        have hg_a : |L a| = - L a := by
          exact abs_of_neg hLa_neg
        have hg_b : |L b| = L b := by
          rw [abs_of_pos hLb_pos]
        have hleft_slope : (|L r| - |L a|) / (r - a) = L a / (r - a) := by
          rw [hrL, hg_a]
          ring
        have hright_slope : (|L b| - |L r|) / (b - r) = L b / (b - r) := by
          rw [hrL, hg_b]
          ring
        rw [hleft_slope, hright_slope] at hslope
        have hleft_neg : L a / (r - a) < 0 := by
          exact div_neg_of_neg_of_pos hLa_neg (sub_pos.mpr hra)
        have hright_pos : 0 < L b / (b - r) := by
          exact div_pos hLb_pos (sub_pos.mpr hrb)
        linarith
  rcases hsign with hLnonneg | hLnonpos
  · -- L≥0, f=L on [a,b]
    have hfa : f a = L a := by
      have h := h_eq a (by exact ⟨le_rfl, hab.le⟩)
      rwa [abs_of_nonneg (hLnonneg a ⟨le_rfl, hab.le⟩)] at h
    have hfb : f b = L b := by
      have h := h_eq b (by exact ⟨hab.le, le_rfl⟩)
      rwa [abs_of_nonneg (hLnonneg b ⟨hab.le, le_rfl⟩)] at h
    have hslope := hf_conc.slope_anti_adjacent (x := (-1 : ℝ)) (y := a) (z := b)
      (by norm_num) hb_Icc (by linarith [ha_mem.1]) hab
    have hleft_slope : (f a - f (-1)) / (a - (-1)) = (s * a + h) / (a + 1) := by
      rw [hfa, hf_left]
      dsimp [L]
      ring_nf
    have hright_slope : (f b - f a) / (b - a) = s := by
      rw [hfb, hfa]
      dsimp [L]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring
    rw [hleft_slope, hright_slope] at hslope
    have hmul : s ≤ (s * a + h) / (a + 1) := hslope
    have ha1_pos : 0 < a + 1 := by linarith [ha_mem.1]
    have hle : s * (a + 1) ≤ s * a + h := (le_div_iff₀ ha1_pos).1 hmul
    nlinarith [hpos]
  · -- L≤0, f=-L on [a,b]
    have hfa : f a = - L a := by
      have h := h_eq a (by exact ⟨le_rfl, hab.le⟩)
      have hL_nonpos_a : L a ≤ 0 := hLnonpos a ⟨le_rfl, hab.le⟩
      rw [abs_of_nonpos hL_nonpos_a] at h
      exact h
    have hfb : f b = - L b := by
      have h := h_eq b (by exact ⟨hab.le, le_rfl⟩)
      have hL_nonpos_b : L b ≤ 0 := hLnonpos b ⟨hab.le, le_rfl⟩
      rw [abs_of_nonpos hL_nonpos_b] at h
      exact h
    have hslope := hf_conc.slope_anti_adjacent (x := a) (y := b) (z := (1 : ℝ))
      ha_Icc (by norm_num) hab (by linarith [hb_mem.2])
    have hleft_slope : (f b - f a) / (b - a) = -s := by
      rw [hfb, hfa]
      dsimp [L]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring
    have hright_slope : (f 1 - f b) / (1 - b) = (s * b + h) / (1 - b) := by
      rw [hf_right, hfb]
      dsimp [L]
      ring_nf
    rw [hleft_slope, hright_slope] at hslope
    have hb1_pos : 0 < 1 - b := by linarith [hb_mem.2]
    have hle : (s * b + h) / (1 - b) ≤ -s := hslope
    have hmul : s * b + h ≤ -s * (1 - b) := (div_le_iff₀ hb1_pos).1 hle
    nlinarith [hneg]

lemma concave_nonneg_eq_zero_of_interior_zero {a b c : ℝ} {g : ℝ → ℝ}
    (hac : a < c) (hcb : c < b)
    (hg : ConcaveOn ℝ (Set.Icc a b) g)
    (hga : g a = 0) (hgb : g b = 0) (hgc : g c = 0)
    (h_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ g t) :
    ∀ t ∈ Set.Icc a b, g t = 0 := by
  intro t ht
  have hab : a < b := lt_trans hac hcb
  have hdom_a : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hdom_b : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  by_cases htc : t ≤ c
  · have htb_lt : t < b := lt_of_le_of_lt htc hcb
    have htb : t ≤ b := le_of_lt htb_lt
    have hden : 0 < b - t := sub_pos.mpr htb_lt
    let lam : ℝ := (b - c) / (b - t)
    have hlam_nonneg : 0 ≤ lam := by
      dsimp [lam]
      exact div_nonneg (sub_nonneg.mpr (le_of_lt hcb)) (le_of_lt hden)
    have hlam_le_one : lam ≤ 1 := by
      dsimp [lam]
      rw [div_le_one hden]
      linarith [htc]
    have hsum : lam + (1 - lam) = 1 := by ring
    have hcombo : lam * t + (1 - lam) * b = c := by
      dsimp [lam]
      field_simp [ne_of_gt hden]
      ring
    have ht_dom : t ∈ Set.Icc a b := ⟨ht.1, htb⟩
    have hconc := hg.2 ht_dom hdom_b hlam_nonneg (by linarith) hsum
    have hle : lam * g t + (1 - lam) * g b ≤ g c := by
      simpa [smul_eq_mul, hcombo] using hconc
    rw [hgb, hgc] at hle
    have hle' : lam * g t ≤ 0 := by simpa using hle
    have hnonneg_t : 0 ≤ g t := h_nonneg t ht_dom
    have hgt_nonpos : g t ≤ 0 := by
      rcases (mul_nonpos_iff.mp hle') with hcase | hcase
      · exact hcase.2
      · have hlam_pos : 0 < lam := by
          dsimp [lam]
          exact div_pos (sub_pos.mpr hcb) hden
        linarith
    linarith
  · have hct : c < t := lt_of_not_ge htc
    have hat_lt : a < t := lt_trans hac hct
    have hden : 0 < t - a := sub_pos.mpr hat_lt
    let lam : ℝ := (t - c) / (t - a)
    have hlam_nonneg : 0 ≤ lam := by
      dsimp [lam]
      exact div_nonneg (sub_nonneg.mpr (le_of_lt hct)) (le_of_lt hden)
    have hlam_le_one : lam ≤ 1 := by
      dsimp [lam]
      rw [div_le_one hden]
      linarith [hct]
    have hsum : lam + (1 - lam) = 1 := by ring
    have hcombo : lam * a + (1 - lam) * t = c := by
      dsimp [lam]
      field_simp [ne_of_gt hden]
      ring
    have hconc := hg.2 hdom_a ht hlam_nonneg (by linarith) hsum
    have hle : lam * g a + (1 - lam) * g t ≤ g c := by
      simpa [smul_eq_mul, hcombo] using hconc
    rw [hga, hgc] at hle
    have hle' : (1 - lam) * g t ≤ 0 := by simpa using hle
    have hnonneg_t : 0 ≤ g t := h_nonneg t ht
    have hlam_lt_one : lam < 1 := by
      dsimp [lam]
      rw [div_lt_one hden]
      linarith [hct]
    have h1lam_pos : 0 < 1 - lam := by linarith
    have hgt_nonpos : g t ≤ 0 := by
      rcases (mul_nonpos_iff.mp hle') with hcase | hcase
      · exact hcase.2
      · linarith
    linarith

lemma moment_deriv_abs_lt_one_of_abs_h_lt_s {n : ℕ} (hn : 2 ≤ n)
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ⊤ f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ⊤ h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s → -s < h s → h s < s → |deriv h s| < 1 := by
  intro s hs hneg hpos
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  have hinside := roots_inside_of_abs_h_lt_s hf_support hf_left hf_right hxy hs hneg hpos
  rcases hinside with ⟨ha_mem, hb_mem⟩
  let a : ℝ := -x s
  let b : ℝ := y s
  have ha_neg : a < 0 := by dsimp [a]; linarith
  have hb_pos : 0 < b := by dsimp [b]; exact hypos
  have hab : a < b := lt_trans ha_neg hb_pos
  have hfa_sq : f a ^ 2 = (s * a + h s) ^ 2 := by simpa [a] using hfx_sq
  have hfb_sq : f b ^ 2 = (s * b + h s) ^ 2 := by simpa [b] using hfy_sq
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    even_profile_nonneg_Icc hf_conc hf_left hf_right
  have hactive := active_nonneg_outside_of_roots_inside (s := s) (h := h s) (a := a) (b := b)
    hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1)
  let C : ℝ := deriv h s
  have hn1 : 0 < n - 1 := by omega
  have hW_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ W t := by
    intro t ht
    have hnonneg := hactive.2 t ht
    have hg_nonneg : 0 ≤ f t - L t := by simpa [L] using hnonneg.1
    have hq_nonneg : 0 ≤ f t + L t := by simpa [L] using hnonneg.2
    have hA_nonneg : 0 ≤ f t ^ 2 - (L t) ^ 2 := by nlinarith [hg_nonneg, hq_nonneg]
    dsimp [W]
    positivity
  have hIcc_sub : Set.Icc a b ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ha_mem.1, ha_mem.2, hb_mem.1, hb_mem.2, ht.1, ht.2]
  have hf_cont_Icc : ContinuousOn f (Set.Icc a b) :=
    hf_cont.continuousOn.mono hIcc_sub
  have hL_cont_Icc : ContinuousOn L (Set.Icc a b) := by
    dsimp [L]
    fun_prop
  have hA_cont : ContinuousOn (fun t => f t ^ 2 - (L t) ^ 2) (Set.Icc a b) := by
    exact (hf_cont_Icc.pow 2).sub (hL_cont_Icc.pow 2)
  have hW_cont : ContinuousOn W (Set.Icc a b) := by
    dsimp [W]
    exact hA_cont.pow (n - 1)
  have hphi_conc : ConcaveOn ℝ (Set.Icc a b) (fun t => f t - |L t|) := by
    have hf_sub : ConcaveOn ℝ (Set.Icc a b) f :=
      hf_conc.subset (by
        intro t ht
        exact ⟨le_trans (Set.Ioo_subset_Icc_self ha_mem).1 ht.1, le_trans ht.2 (Set.Ioo_subset_Icc_self hb_mem).2⟩)
        (convex_Icc a b)
    have hL_abs_conc : ConcaveOn ℝ (Set.Icc a b) (fun t => - |L t|) := by
      have hL_abs_conv : ConvexOn ℝ Set.univ (fun t : ℝ => |L t|) := by
        refine ⟨convex_univ, ?_⟩
        intro u hu v hv p q hp hq hpq
        simp only [smul_eq_mul]
        have hL_combo : L (p * u + q * v) = p * L u + q * L v := by
          dsimp [L]
          ring_nf
          nlinarith [hpq]
        rw [hL_combo]
        calc
          |p * L u + q * L v| ≤ |p * L u| + |q * L v| := abs_add_le _ _
          _ = p * |L u| + q * |L v| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
      have hL_abs_conc' : ConcaveOn ℝ Set.univ (fun t : ℝ => - |L t|) := by
        exact neg_concaveOn_iff.mpr hL_abs_conv
      exact hL_abs_conc'.subset (by intro t ht; trivial) (convex_Icc a b)
    exact hf_sub.add hL_abs_conc
  have hphi_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t - |L t| := by
    intro t ht
    have hnonneg := hactive.2 t ht
    have hg_nonneg : 0 ≤ f t - L t := by simpa [L] using hnonneg.1
    have hq_nonneg : 0 ≤ f t + L t := by simpa [L] using hnonneg.2
    have : |L t| ≤ f t := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hphi_a : f a - |L a| = 0 := by
    have hfa_nonneg : 0 ≤ f a := hf_nonneg a (Set.Ioo_subset_Icc_self ha_mem)
    rcases le_total (L a) 0 with hLa_nonpos | hLa_nonneg
    · have hfa_eq : f a = - L a :=
        eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hfa_sq hfa_nonneg hLa_nonpos
      rw [abs_of_nonpos hLa_nonpos]
      linarith
    · have hfa_eq : f a = L a :=
        eq_of_sq_eq_sq_of_nonneg_of_nonneg hfa_sq hfa_nonneg hLa_nonneg
      rw [abs_of_nonneg hLa_nonneg]
      linarith
  have hphi_b : f b - |L b| = 0 := by
    have hfb_nonneg : 0 ≤ f b := hf_nonneg b (Set.Ioo_subset_Icc_self hb_mem)
    rcases le_total (L b) 0 with hLb_nonpos | hLb_nonneg
    · have hfb_eq : f b = - L b :=
        eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hfb_sq hfb_nonneg hLb_nonpos
      rw [abs_of_nonpos hLb_nonpos]
      linarith
    · have hfb_eq : f b = L b :=
        eq_of_sq_eq_sq_of_nonneg_of_nonneg hfb_sq hfb_nonneg hLb_nonneg
      rw [abs_of_nonneg hLb_nonneg]
      linarith
  have hphi0_pos : 0 < f 0 - |L 0| := by
    have h0_mem : (0 : ℝ) ∈ Set.Icc a b := ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
    by_contra hnot
    have hphi0 : f 0 - |L 0| = 0 := by
      exact le_antisymm (le_of_not_gt hnot) (hphi_nonneg 0 h0_mem)
    have hphi_zero_all := concave_nonneg_eq_zero_of_interior_zero (a := a) (b := b) (c := 0)
      ha_neg hb_pos hphi_conc hphi_a hphi_b hphi0 hphi_nonneg
    have hf_abs_all : ∀ t ∈ Set.Icc a b, f t = |L t| := by
      intro t ht
      have hz := hphi_zero_all t ht
      linarith [hphi_nonneg t ht]
    exact not_eq_abs_affine_of_concave_and_abs_h_lt_s hs hneg hpos ha_mem hb_mem ha_neg hb_pos
      hf_conc hf_left hf_right hf_abs_all
  have hW0_pos : 0 < W 0 := by
    have h0_mem : (0 : ℝ) ∈ Set.Icc a b := ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
    have hf0_pos : 0 < f 0 := hf_pos 0 (by norm_num)
    have hL0 : L 0 = h s := by simp [L]
    have hf0_gt : |L 0| < f 0 := by
      have : 0 < f 0 - |L 0| := hphi0_pos
      linarith
    have hA0_pos : 0 < f 0 ^ 2 - (L 0) ^ 2 := by
      have hf0_nonneg : 0 ≤ f 0 := le_of_lt hf0_pos
      have hL0_abs_nonneg : 0 ≤ |L 0| := abs_nonneg _
      have hsq_lt : (L 0) ^ 2 < (f 0) ^ 2 := by
        apply sq_lt_sq.mpr
        simpa [abs_of_pos hf0_pos] using hf0_gt
      linarith
    dsimp [W]
    exact pow_pos hA0_pos (n - 1)
  have hW_pos_integral : 0 < ∫ t in a..b, W t := by
    refine intervalIntegral.integral_pos hab hW_cont ?_ ?_
    · intro t ht
      exact hW_nonneg t (Set.Ioc_subset_Icc_self ht)
    · refine ⟨0, ?_, hW0_pos⟩
      exact ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
  have hJ' : (∫ t in a..b, W t * (t + C)) = 0 := by
    have hJ0 := hJ s hs
    simpa [a,b,W,L,C] using hJ0
  have hW_int : IntervalIntegrable W MeasureTheory.volume a b := by
    exact hW_cont.intervalIntegrable_of_Icc hab.le
  have hWt_cont : ContinuousOn (fun t => W t * t) (Set.Icc a b) :=
    hW_cont.mul continuousOn_id
  have hWC_cont : ContinuousOn (fun t => W t * C) (Set.Icc a b) :=
    hW_cont.mul continuousOn_const
  have hWt_int : IntervalIntegrable (fun t => W t * t) MeasureTheory.volume a b :=
    hWt_cont.intervalIntegrable_of_Icc hab.le
  have hWC_int : IntervalIntegrable (fun t => W t * C) MeasureTheory.volume a b :=
    hWC_cont.intervalIntegrable_of_Icc hab.le
  have hsum_cont : ContinuousOn (fun t => W t * t + W t * C) (Set.Icc a b) :=
    hWt_cont.add hWC_cont
  have hsum_int : IntervalIntegrable (fun t => W t * t + W t * C) MeasureTheory.volume a b :=
    hsum_cont.intervalIntegrable_of_Icc hab.le
  have h_congr : (∫ t in a..b, W t * (t + C)) = ∫ t in a..b, (W t * t + W t * C) := by
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have h_add : (∫ t in a..b, (W t * t + W t * C)) =
      (∫ t in a..b, W t * t) + (∫ t in a..b, W t * C) :=
    intervalIntegral.integral_add hWt_int hWC_int
  have h_mulC : (∫ t in a..b, W t * C) = (∫ t in a..b, W t) * C :=
    intervalIntegral.integral_mul_const C W
  have hJ_sum : (∫ t in a..b, W t * t) + (∫ t in a..b, W t) * C = 0 := by
    rw [← h_mulC, ← h_add, ← h_congr]
    exact hJ'
  let I0 : ℝ := ∫ t in a..b, W t
  let I1 : ℝ := ∫ t in a..b, W t * t
  have hI0_pos : 0 < I0 := by simpa [I0] using hW_pos_integral
  have hsum : I1 + I0 * C = 0 := by simpa [I0, I1] using hJ_sum
  have hC_eq : C = - I1 / I0 := by
    rw [eq_div_iff hI0_pos.ne']
    linarith
  have hI1_lt_b : I1 < b * I0 := by
    have hle : ∀ t ∈ Set.Ioc a b, W t * t ≤ b * W t := by
      intro t ht
      have ht_b : t ≤ b := ht.2
      have hW_nonneg_t : 0 ≤ W t := hW_nonneg t (Set.Ioc_subset_Icc_self ht)
      nlinarith [mul_le_mul_of_nonneg_right ht_b hW_nonneg_t]
    have hlt_exists : ∃ c ∈ Set.Icc a b, W c * c < b * W c := by
      refine ⟨0, ?_, ?_⟩
      · exact ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
      · have hbW_pos : 0 < b * W 0 := mul_pos hb_pos hW0_pos
        nlinarith
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun t => W t * t)
      (g := fun t => b * W t) hab hWt_cont (hW_cont.const_mul b) hle hlt_exists
    simpa [I0, I1] using h
  have hI1_gt_a : a * I0 < I1 := by
    have hle : ∀ t ∈ Set.Ioc a b, a * W t ≤ W t * t := by
      intro t ht
      have ha_t : a ≤ t := le_of_lt ht.1
      have hW_nonneg_t : 0 ≤ W t := hW_nonneg t (Set.Ioc_subset_Icc_self ht)
      nlinarith [mul_le_mul_of_nonneg_right ha_t hW_nonneg_t]
    have hlt_exists : ∃ c ∈ Set.Icc a b, a * W c < W c * c := by
      refine ⟨0, ?_, ?_⟩
      · exact ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
      · have haW_neg : a * W 0 < 0 := mul_neg_of_neg_of_pos ha_neg hW0_pos
        nlinarith
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun t => a * W t)
      (g := fun t => W t * t) hab (hW_cont.const_mul a) hWt_cont hle hlt_exists
    simpa [I0, I1] using h
  have hI0C_eq : I0 * C = -I1 := by linarith
  have hC_gt : -b < C := by
    nlinarith [hI1_lt_b, hI0C_eq, hI0_pos]
  have hC_lt : C < -a := by
    nlinarith [hI1_gt_a, hI0C_eq, hI0_pos]
  have hC_gt_m1 : -1 < C := by linarith [hC_gt, hb_mem.2]
  have hC_lt_1 : C < 1 := by linarith [hC_lt, ha_mem.1]
  exact abs_lt.mpr ⟨hC_gt_m1, hC_lt_1⟩

lemma eventually_abs_lt_self_of_deriv_abs_lt_one {h : ℝ → ℝ}
    (hh_cont : ContDiffOn ℝ ⊤ h Set.univ) (h0 : h 0 = 0)
    (hderiv : |deriv h 0| < 1) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), |h s| < s := by
  have hcontDiffAt : ContDiffAt ℝ ⊤ h 0 := by
    exact hh_cont.contDiffAt (by simp)
  have hdiff : DifferentiableAt ℝ h 0 := hcontDiffAt.differentiableAt (by simp)
  have hderivAt : HasDerivAt h (deriv h 0) 0 := hdiff.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hderivAt
  -- slope h 0 x = (h x - h 0)/(x-0) = h x / x
  have hmem_ioi : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), s ∈ Set.Ioi 0 :=
    self_mem_nhdsWithin
  have hlim : Filter.Tendsto (fun s => h s / s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv h 0)) := by
    have hmono : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ) := by
      rw [nhdsWithin_le_iff]
      have hevent : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), x ∈ (({0} : Set ℝ)ᶜ) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact ne_of_gt hx
      exact hevent
    have hderivAt_ioi : Filter.Tendsto (fun s => slope h 0 s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv h 0)) :=
      hderivAt.mono_left hmono
    refine hderivAt_ioi.congr' ?_
    filter_upwards [hmem_ioi] with s hs
    have hs_ne : s ≠ 0 := ne_of_gt hs
    show slope h 0 s = h s / s
    rw [slope]
    simp [h0]
    ring
  have hlt_event : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), |h s / s| < 1 := by
    have hd_lt : |deriv h 0| < 1 := hderiv
    have hd_event : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), |h s / s| < 1 := by
      exact (tendsto_order.1 (Filter.Tendsto.norm hlim)).2 1 hd_lt
    exact hd_event
  filter_upwards [hmem_ioi, hlt_event] with s hs hlt
  have hs_pos : 0 < s := hs
  rw [abs_div] at hlt
  have h_abs_s : |s| = s := abs_of_pos hs_pos
  rw [h_abs_s] at hlt
  have : |h s| / s < 1 := hlt
  have : |h s| < 1 * s := (div_lt_iff₀ hs_pos).1 this
  simpa using this

lemma abs_lt_self_of_eventually_and_deriv_bound {h : ℝ → ℝ}
    (hh_cont : ContDiffOn ℝ ⊤ h Set.univ)
    (h0 : h 0 = 0)
    (heventually : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), |h s| < s)
    (hderiv_bound : ∀ s : ℝ, 0 < s → |h s| < s → |deriv h s| < 1) :
    ∀ s : ℝ, 0 < s → |h s| < s := by
  by_contra hnot
  push_neg at hnot
  rcases hnot with ⟨S, hSpos, hSnot⟩
  have hS_abs : S ≤ |h S| := hSnot
  have hevent_set : {s : ℝ | |h s| < s} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := heventually
  rcases (mem_nhdsGT_iff_exists_Ioo_subset.mp hevent_set) with ⟨δ, hδ0, hδsub⟩
  have hδ_pos : 0 < δ := hδ0
  have hδS : δ ≤ S := by
    by_contra hlt
    have hS_lt_δ : S < δ := lt_of_not_ge hlt
    have hS_mem : S ∈ Set.Ioo 0 δ := ⟨hSpos, hS_lt_δ⟩
    have hltS : |h S| < S := hδsub hS_mem
    linarith
  let F : Set ℝ := Set.Icc δ S ∩ {t : ℝ | t ≤ |h t|}
  have hF_nonempty : F.Nonempty := by
    refine ⟨S, ?_⟩
    dsimp [F]
    exact ⟨⟨hδS, le_refl S⟩, hS_abs⟩
  have hh_cont_all : Continuous h := by
    exact continuousOn_univ.mp hh_cont.continuousOn
  have hclosed_second : IsClosed {t : ℝ | t ≤ |h t|} :=
    isClosed_le continuous_id (continuous_norm.comp hh_cont_all)
  have hF_closed : IsClosed F := by
    dsimp [F]
    exact isClosed_Icc.inter hclosed_second
  have hF_compact : IsCompact F := by
    dsimp [F]
    exact isCompact_Icc.inter_right hclosed_second
  obtain ⟨t0, ht0F, ht0min⟩ := hF_compact.exists_isMinOn hF_nonempty continuousOn_id
  have ht0_cc : t0 ∈ Set.Icc δ S := ht0F.1
  have ht0_ge_δ : δ ≤ t0 := ht0_cc.1
  have ht0_le_S : t0 ≤ S := ht0_cc.2
  have ht0_abs_ge : t0 ≤ |h t0| := ht0F.2
  have ht0_pos : 0 < t0 := lt_of_lt_of_le hδ_pos ht0_ge_δ
  have h_before : ∀ t : ℝ, 0 < t → t < t0 → |h t| < t := by
    intro t ht_pos ht_lt
    by_cases ht_ge_δ : t < δ
    · exact hδsub ⟨ht_pos, ht_ge_δ⟩
    · have hδ_le_t : δ ≤ t := le_of_not_gt ht_ge_δ
      have ht_le_S : t ≤ S := le_trans ht_lt.le ht0_le_S
      by_contra hnotlt
      have htF : t ∈ F := by
        dsimp [F]
        exact ⟨⟨hδ_le_t, ht_le_S⟩, le_of_not_gt hnotlt⟩
      have hmin : t0 ≤ t := by simpa using ht0min htF
      linarith
  have h_cont : ContinuousOn h (Set.Icc 0 t0) := by
    exact hh_cont.continuousOn.mono (by intro x hx; simp)
  have h_diff : DifferentiableOn ℝ h (Set.Ioo 0 t0) := by
    exact (hh_cont.differentiableOn (show (⊤ : WithTop ℕ∞) ≠ 0 by simp)).mono (by intro x hx; trivial)
  have hmvt_raw := exists_deriv_eq_slope h (a := (0 : ℝ)) (b := t0) ht0_pos h_cont h_diff
  rcases hmvt_raw with ⟨c, hc_mem, hc_eq⟩
  have hc_pos : 0 < c := hc_mem.1
  have hc_lt : c < t0 := hc_mem.2
  have hc_abs_lt : |h c| < c := h_before c hc_pos hc_lt
  have hderiv_c_lt : |deriv h c| < 1 := hderiv_bound c hc_pos hc_abs_lt
  have hc_div : deriv h c = h t0 / t0 := by
    simpa [h0] using hc_eq
  have hc_eq' : h t0 = deriv h c * t0 := by
    rw [hc_div]
    field_simp [ht0_pos.ne']
  have h_abs_eq : |h t0| = |deriv h c| * t0 := by
    rw [hc_eq']
    rw [abs_mul]
    rw [abs_of_pos ht0_pos]
  nlinarith


lemma moment_h_bounds {n : ℕ} (hn : 2 ≤ n)
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ⊤ f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ⊤ h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s → -s < h s ∧ h s < s := by
  intro s hs
  have hderiv0 : |deriv h 0| < 1 :=
    moment_deriv_zero_abs_lt_one hn hf_support hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hxy hJ
  have heventually : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), |h t| < t :=
    eventually_abs_lt_self_of_deriv_abs_lt_one hh_cont h0 hderiv0
  have hbarrier : ∀ t : ℝ, 0 < t → |h t| < t :=
    abs_lt_self_of_eventually_and_deriv_bound hh_cont h0 heventually
      (fun u hu hu_abs => moment_deriv_abs_lt_one_of_abs_h_lt_s hn hf_support hf_cont hf_conc
        hf_left hf_right hf_pos hh_cont h0 hxy hJ u hu (abs_lt.mp hu_abs).1 (abs_lt.mp hu_abs).2)
  have habs : |h s| < s := hbarrier s hs
  exact abs_lt.mp habs

end Commons.Geometry.Ulam