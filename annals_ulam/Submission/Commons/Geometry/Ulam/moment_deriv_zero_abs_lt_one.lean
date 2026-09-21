import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Commons.Geometry.Ulam.odd_floating_of_family

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace Commons.Geometry.Ulam

set_option autoImplicit false

-- helper lemmas ----------------------------------------------------------------

private lemma support_subset_iff_zero_of_not_mem {f : ℝ → ℝ} {s : Set ℝ}
    (h : Function.support f ⊆ s) {x : ℝ} (hx : x ∉ s) : f x = 0 := by
  by_contra hf
  exact hx (h (by simpa [Function.mem_support] using hf))

private lemma exists_pos_lower_on_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_pos : ∀ t ∈ Set.Icc a b, 0 < f t) :
    ∃ m > 0, ∀ t ∈ Set.Icc a b, m ≤ f t := by
  have hcomp : IsCompact (Set.Icc a b) := isCompact_Icc
  have hnonempty : (Set.Icc a b).Nonempty := ⟨a, ⟨le_rfl, hab.le⟩⟩
  obtain ⟨x, hx, hmin⟩ := hcomp.exists_isMinOn hnonempty hf_cont
  refine ⟨f x, hf_pos x hx, ?_⟩
  intro t ht
  exact hmin ht

private lemma roots_bounded_of_tendsto {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    {B : ℝ} (_hB : 0 ≤ B)
    (hle : ∀ᶠ s in 𝓝[>] (0:ℝ), |h s / s| ≤ B) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), x s ≤ max 1 B ∧ y s ≤ max 1 B := by
  filter_upwards [hle, self_mem_nhdsWithin] with s hsle hspos
  have hs : 0 < s := hspos
  rcases hxy s hs with ⟨hxpos, hypos, hfy, hfx⟩
  have hR : B ≤ max 1 B := le_max_right _ _
  constructor
  · by_cases hx1 : x s ≤ 1
    · exact le_trans hx1 (le_max_left _ _)
    · have hx_gt : 1 < x s := lt_of_not_ge hx1
      have hmem_not : -x s ∉ Set.Icc (-1 : ℝ) 1 := by
        rw [Set.mem_Icc, not_and_or]
        left
        linarith
      have hf0 : f (-x s) = 0 := support_subset_iff_zero_of_not_mem hf_support hmem_not
      have hsq : (s * (-x s) + h s) ^ 2 = 0 := by
        rw [← hfx, hf0]
        simp
      have hlin : s * (-x s) + h s = 0 := sq_eq_zero_iff.mp hsq
      have hx_eq : x s = h s / s := by
        have hs_ne : s ≠ 0 := ne_of_gt hs
        field_simp [hs_ne] at hlin ⊢
        linarith
      have hx_abs : |x s| = |h s / s| := by rw [hx_eq]
      have hx_abs' : x s = |h s / s| := by
        rw [← hx_abs]
        exact (abs_of_pos hxpos).symm
      rw [hx_abs']
      exact le_trans hsle hR
  · by_cases hy1 : y s ≤ 1
    · exact le_trans hy1 (le_max_left _ _)
    · have hy_gt : 1 < y s := lt_of_not_ge hy1
      have hmem_not : y s ∉ Set.Icc (-1 : ℝ) 1 := by
        rw [Set.mem_Icc, not_and_or]
        right
        linarith
      have hf0 : f (y s) = 0 := support_subset_iff_zero_of_not_mem hf_support hmem_not
      have hsq : (s * y s + h s) ^ 2 = 0 := by
        rw [← hfy, hf0]
        simp
      have hlin : s * y s + h s = 0 := sq_eq_zero_iff.mp hsq
      have hy_eq : y s = - h s / s := by
        have hs_ne : s ≠ 0 := ne_of_gt hs
        field_simp [hs_ne] at hlin ⊢
        linarith
      have hy_abs : |y s| = |h s / s| := by
        rw [hy_eq]
        simp [abs_div]
      have hy_abs' : y s = |h s / s| := by
        rw [← hy_abs]
        exact (abs_of_pos hypos).symm
      rw [hy_abs']
      exact le_trans hsle hR

private lemma eventually_roots_gt_one_sub {h x y f : ℝ → ℝ}
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 1 - ε < x s ∧ 1 - ε < y s := by
  let a0 : ℝ := -1 + ε / 2
  let b0 : ℝ := 1 - ε / 2
  have ha0_lt_b0 : a0 < b0 := by dsimp [a0, b0]; linarith
  have hsub : Set.Icc a0 b0 ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    rcases ht with ⟨ht1, ht2⟩
    constructor
    · dsimp [a0] at ht1
      linarith
    · dsimp [b0] at ht2
      linarith
  have hf_cont_compact : ContinuousOn f (Set.Icc a0 b0) :=
    hf_cont.continuousOn.mono hsub
  have hf_pos_compact : ∀ t ∈ Set.Icc a0 b0, 0 < f t := by
    intro t ht; exact hf_pos t (hsub ht)
  obtain ⟨m, hmpos, hmle⟩ := exists_pos_lower_on_Icc (a := a0) (b := b0) ha0_lt_b0 hf_cont_compact hf_pos_compact
  have hcont : ContinuousAt h 0 := by
    exact hh_cont.continuousOn.continuousAt (by simp)
  have htend_h : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa [h0] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have htend_s : Tendsto (fun s : ℝ => s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hhalf : 0 < m / 2 := half_pos hmpos
  have hh_event : ∀ᶠ s in 𝓝[>] (0:ℝ), |h s| < m / 2 := by
    have hlim : Tendsto (fun s => |h s|) (𝓝[>] (0:ℝ)) (𝓝 |(0:ℝ)|) := htend_h.norm
    simpa using (Metric.tendsto_nhds.1 hlim) (m / 2) hhalf
  have hs_event : ∀ᶠ s in 𝓝[>] (0:ℝ), |s| < m / 2 := by
    have hlim : Tendsto (fun s => |s|) (𝓝[>] (0:ℝ)) (𝓝 |(0:ℝ)|) := htend_s.norm
    simpa using (Metric.tendsto_nhds.1 hlim) (m / 2) hhalf
  have hpos_event : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s := self_mem_nhdsWithin
  filter_upwards [hpos_event, hh_event, hs_event] with s hspos hhle hsle
  have hs : 0 < s := hspos
  have hL_bound : ∀ t ∈ Set.Icc a0 b0, |s * t + h s| < m := by
    intro t ht
    rcases ht with ⟨ht1, ht2⟩
    have ht_abs : |t| ≤ 1 := by
      have hneg : -1 ≤ t := by
        dsimp [a0] at ht1
        linarith
      have hpos : t ≤ 1 := by
        dsimp [b0] at ht2
        linarith
      exact abs_le.mpr ⟨hneg, hpos⟩
    calc
      |s * t + h s| ≤ |s * t| + |h s| := abs_add_le _ _
      _ = |s| * |t| + |h s| := by rw [abs_mul]
      _ < m / 2 + m / 2 := by
        have h1 : |s| * |t| < m / 2 := by
          have hle_mul : |s| * |t| ≤ |s| * 1 := mul_le_mul_of_nonneg_left ht_abs (abs_nonneg s)
          have h1' : |s| * 1 < m / 2 := by simpa using hsle
          exact lt_of_le_of_lt hle_mul h1'
        linarith
      _ = m := by ring
  rcases hxy s hs with ⟨hxpos, hypos, hfy, hfx⟩
  constructor
  · by_contra hnot
    have hx_le : x s ≤ 1 - ε := le_of_not_gt hnot
    have ha_mem : -x s ∈ Set.Icc a0 b0 := by
      constructor
      · dsimp [a0]
        linarith
      · dsimp [b0]
        linarith
    have hfa_pos : 0 < f (-x s) := hf_pos_compact (-x s) ha_mem
    have hL_lt : |s * (-x s) + h s| < m := hL_bound (-x s) ha_mem
    have hf_ge : m ≤ f (-x s) := hmle (-x s) ha_mem
    have hL_lt_f : |s * (-x s) + h s| < f (-x s) := lt_of_lt_of_le hL_lt hf_ge
    have hsq := hfx
    have hfabs : f (-x s) = |s * (-x s) + h s| := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
      · have hLpos : 0 < s * (-x s) + h s := by linarith
        rw [heq, abs_of_pos hLpos]
      · have hLneg : s * (-x s) + h s < 0 := by linarith
        rw [heq, abs_of_neg hLneg]
    linarith
  · by_contra hnot
    have hy_le : y s ≤ 1 - ε := le_of_not_gt hnot
    have hb_mem : y s ∈ Set.Icc a0 b0 := by
      constructor
      · dsimp [a0]; linarith
      · dsimp [b0]; linarith
    have hfb_pos : 0 < f (y s) := hf_pos_compact (y s) hb_mem
    have hL_lt : |s * y s + h s| < m := hL_bound (y s) hb_mem
    have hf_ge : m ≤ f (y s) := hmle (y s) hb_mem
    have hL_lt_f : |s * y s + h s| < f (y s) := lt_of_lt_of_le hL_lt hf_ge
    have hsq := hfy
    have hfabs : f (y s) = |s * y s + h s| := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
      · have hLpos : 0 < s * y s + h s := by linarith
        rw [heq, abs_of_pos hLpos]
      · have hLneg : s * y s + h s < 0 := by linarith
        rw [heq, abs_of_neg hLneg]
    linarith

private lemma intervalIntegral_eq_fixed_indicator {F : ℝ → ℝ} {a b R : ℝ}
    (hR1 : -R ≤ a) (hab : a ≤ b) (hR2 : b ≤ R) :
    (∫ t in a..b, F t) = ∫ t in (-R)..R, (Set.Ioc a b).indicator F t := by
  have h_int1 : (∫ t in a..b, F t) = ∫ t in Set.Ioc a b, F t :=
    intervalIntegral.integral_of_le hab
  have hRle : -R ≤ R := le_trans hR1 (le_trans hab hR2)
  have h_int2 : (∫ t in (-R)..R, (Set.Ioc a b).indicator F t) =
      ∫ t in Set.Ioc (-R) R, (Set.Ioc a b).indicator F t :=
    intervalIntegral.integral_of_le hRle
  have h_ind : (∫ t in Set.Ioc (-R) R, (Set.Ioc a b).indicator F t) =
      ∫ t in Set.Ioc (-R) R ∩ Set.Ioc a b, F t := by
    exact MeasureTheory.setIntegral_indicator measurableSet_Ioc
  have h_inter : Set.Ioc (-R) R ∩ Set.Ioc a b = Set.Ioc a b := by
    ext t
    constructor
    · rintro ⟨ht1, ht2⟩; exact ht2
    · intro ht
      exact ⟨⟨lt_of_le_of_lt hR1 ht.1, le_trans ht.2 hR2⟩, ht⟩
  rw [h_int1, h_int2, h_ind, h_inter]

-- moment integrand -------------------------------------------------------------

private def momentF (n : ℕ) (h f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)

private def momentG (n : ℕ) (h x y f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (Set.Ioc (-x s) (y s)).indicator (fun t => momentF n h f s t) t

private def momentLimit (n : ℕ) (h f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Set.Ioo (-1 : ℝ) 1).indicator (fun t => (f t ^ 2) ^ (n - 1) * (t + deriv h 0)) t

private lemma tendsto_momentF {n : ℕ} {h f : ℝ → ℝ} {t : ℝ}
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ) (h0 : h 0 = 0) :
    Tendsto (fun s : ℝ => momentF n h f s t)
      (𝓝[>] (0:ℝ)) (𝓝 ((f t ^ 2) ^ (n - 1) * (t + deriv h 0))) := by
  unfold momentF
  have hcont_h : ContinuousAt h 0 := by
    exact hh_cont.continuousOn.continuousAt (by simp)
  have htend_h : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa [h0] using hcont_h.tendsto.mono_left nhdsWithin_le_nhds
  have htend_s : Tendsto (fun s : ℝ => s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hderiv_cont : ContinuousAt (deriv h) 0 := by
    exact (hh_cont.continuousOn_deriv_of_isOpen isOpen_univ (by simp)).continuousAt (by simp)
  have htend_deriv : Tendsto (deriv h) (𝓝[>] (0:ℝ)) (𝓝 (deriv h 0)) :=
    hderiv_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun s : ℝ => s * t + h s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s * t) (𝓝[>] (0:ℝ)) (𝓝 (0 * t)) := htend_s.mul tendsto_const_nhds
    simpa using h1.add htend_h
  have hsq : Tendsto (fun s : ℝ => f t ^ 2 - (s * t + h s) ^ 2) (𝓝[>] (0:ℝ)) (𝓝 (f t ^ 2 - 0 ^ 2)) := by
    exact tendsto_const_nhds.sub (hL.pow 2)
  have hpow : Tendsto (fun s : ℝ => (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1))
      (𝓝[>] (0:ℝ)) (𝓝 ((f t ^ 2 - 0 ^ 2) ^ (n - 1))) := hsq.pow (n - 1)
  have hlin : Tendsto (fun s : ℝ => t + deriv h s) (𝓝[>] (0:ℝ)) (𝓝 (t + deriv h 0)) :=
    tendsto_const_nhds.add htend_deriv
  have hmain := hpow.mul hlin
  simpa using hmain


private lemma f_eq_zero_of_not_mem_Ioo {f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    {t : ℝ} (ht : t ∉ Set.Ioo (-1 : ℝ) 1) : f t = 0 := by
  by_cases hle : t ≤ -1
  · by_cases heq : t = -1
    · subst t; exact hf_left
    · have hlt : t < -1 := lt_of_le_of_ne hle (by intro h; exact heq h)
      have hmem_not : t ∉ Set.Icc (-1 : ℝ) 1 := by
        rw [Set.mem_Icc, not_and_or]
        left
        linarith
      exact support_subset_iff_zero_of_not_mem hf_support hmem_not
  · have hge : 1 ≤ t := by
      have hnotlt : ¬ t < 1 := by
        intro hlt
        have ht' : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hlt⟩
        exact ht ht'
      linarith
    by_cases heq : t = 1
    · subst t; exact hf_right
    · have hgt : 1 < t := lt_of_le_of_ne hge (by intro h; exact heq h.symm)
      have hmem_not : t ∉ Set.Icc (-1 : ℝ) 1 := by
        rw [Set.mem_Icc, not_and_or]
        right
        linarith
      exact support_subset_iff_zero_of_not_mem hf_support hmem_not

private lemma eventually_momentG_eq_momentF_of_mem_Ioo {n : ℕ} {h x y f : ℝ → ℝ} {t : ℝ}
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ) (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), momentG n h x y f s t = momentF n h f s t := by
  have ht1 : -1 < t := ht.1
  have ht2 : t < 1 := ht.2
  let δ : ℝ := min ((1 + t) / 2) ((1 - t) / 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos (by linarith)) (half_pos (by linarith))
  have hδ_le_left : δ ≤ 1 + t := by
    dsimp [δ]
    have h := min_le_left ((1 + t) / 2) ((1 - t) / 2)
    linarith
  have hδ_le_right : δ ≤ 1 - t := by
    dsimp [δ]
    have h := min_le_right ((1 + t) / 2) ((1 - t) / 2)
    linarith
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    have h1 : (1 + t) / 2 < 1 := by nlinarith [ht2]
    have hmin := min_le_left ((1 + t) / 2) ((1 - t) / 2)
    exact lt_of_le_of_lt hmin h1
  have hroot_ev := eventually_roots_gt_one_sub (h := h) (x := x) (y := y) (f := f)
    hf_cont hf_pos hh_cont h0 hxy hδ_pos hδ_lt_one
  filter_upwards [hroot_ev, self_mem_nhdsWithin] with s hs hspos
  have hs_pos : 0 < s := hspos
  have hx_gt : -t < x s := by
    have hx_gt' : 1 - δ < x s := hs.1
    nlinarith [hδ_le_left, hx_gt']
  have hy_gt : t < y s := by
    have hy_gt' : 1 - δ < y s := hs.2
    nlinarith [hδ_le_right, hy_gt']
  have ha_lt_t : -x s < t := by linarith
  have ht_le_b : t ≤ y s := le_of_lt hy_gt
  have hmem : t ∈ Set.Ioc (-x s) (y s) := ⟨ha_lt_t, ht_le_b⟩
  unfold momentG
  simp [hmem]

private lemma tendsto_momentG_pointwise {n : ℕ} (hn : 2 ≤ n) {h x y f : ℝ → ℝ} {t : ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ) (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) :
    Tendsto (fun s : ℝ => momentG n h x y f s t)
      (𝓝[>] (0:ℝ)) (𝓝 (momentLimit n h f t)) := by
  by_cases ht : t ∈ Set.Ioo (-1 : ℝ) 1
  · have heq := eventually_momentG_eq_momentF_of_mem_Ioo (n := n) (h := h) (x := x) (y := y) (f := f)
      (t := t) hf_cont hf_pos hh_cont h0 hxy ht
    have hF := tendsto_momentF (n := n) (h := h) (f := f) (t := t) hh_cont h0
    have hlim_eq : momentLimit n h f t = (f t ^ 2) ^ (n - 1) * (t + deriv h 0) := by
      unfold momentLimit
      simp [ht]
    rw [hlim_eq]
    have heq' : (fun s : ℝ => momentF n h f s t) =ᶠ[𝓝[>] (0:ℝ)] (fun s => momentG n h x y f s t) := by
      filter_upwards [heq] with s hs
      exact hs.symm
    exact Filter.Tendsto.congr' heq' hF
  · have hlim0 : momentLimit n h f t = 0 := by
      unfold momentLimit
      simp [ht]
    rw [hlim0]
    have hf0 : f t = 0 := f_eq_zero_of_not_mem_Ioo hf_support hf_left hf_right ht
    have hF0 : Tendsto (fun s : ℝ => momentF n h f s t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hFlim := tendsto_momentF (n := n) (h := h) (f := f) (t := t) hh_cont h0
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      have : (f t ^ 2) ^ (n - 1) * (t + deriv h 0) = 0 := by
        simp [hf0, hzero]
      simpa [this] using hFlim
    have hbound : ∀ s : ℝ, |momentG n h x y f s t| ≤ |momentF n h f s t| := by
      intro s
      unfold momentG
      by_cases hmem : t ∈ Set.Ioc (-x s) (y s)
      · simp [hmem]
      · simp [hmem]
    have h_absF : Tendsto (fun s : ℝ => |momentF n h f s t|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using hF0.norm
    have h_absG : Tendsto (fun s : ℝ => |momentG n h x y f s t|) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      squeeze_zero (fun s => abs_nonneg _) hbound h_absF
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs, sub_zero] using h_absG


private lemma f_abs_le_global {f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0) :
    ∃ M > 0, ∀ t : ℝ, |f t| ≤ M := by
  have hbdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) :=
    concaveOn_Icc_zero_endpoints_bounded (a := -1) (b := 1) (by norm_num) hf_conc hf_left hf_right
  obtain ⟨M, hMpos, hM⟩ := hbdd.exists_pos_norm_le
  refine ⟨M, hMpos, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
  · exact hM (f t) ⟨t, ht, rfl⟩
  · have hf0 : f t = 0 := support_subset_iff_zero_of_not_mem hf_support ht
    simp [hf0, hMpos.le]

private lemma eventually_momentG_bound {n : ℕ} {h x y f : ℝ → ℝ} {R : ℝ}
    (hRpos : 0 < R)
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ) (h0 : h 0 = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ t ∈ Set.uIoc (-R) R,
      |momentG n h x y f s t| ≤ B := by
  obtain ⟨Mf, hMfpos, hMf⟩ := f_abs_le_global hf_support hf_conc hf_left hf_right
  have hcont_h : ContinuousAt h 0 := by
    exact hh_cont.continuousOn.continuousAt (by simp)
  have hderiv_cont : ContinuousAt (deriv h) 0 := by
    exact (hh_cont.continuousOn_deriv_of_isOpen isOpen_univ (by simp)).continuousAt (by simp)
  let C : ℝ := |deriv h 0| + 1
  have hCpos : 0 < C := by dsimp [C]; linarith [abs_nonneg (deriv h 0)]
  have hh_event : ∀ᶠ s in 𝓝[>] (0:ℝ), |h s| ≤ 1 := by
    have htend : Tendsto (fun s => |h s|) (𝓝[>] (0:ℝ)) (𝓝 |(0:ℝ)|) := by
      simpa [h0] using (hcont_h.tendsto.mono_left nhdsWithin_le_nhds).norm
    have hle : ∀ᶠ s in 𝓝[>] (0:ℝ), |h s| < 1 := by
      simpa using (Metric.tendsto_nhds.1 htend) 1 (by norm_num)
    filter_upwards [hle] with s hs
    exact le_of_lt hs
  have hderiv_event : ∀ᶠ s in 𝓝[>] (0:ℝ), |deriv h s| ≤ C := by
    have htend : Tendsto (fun s => |deriv h s|) (𝓝[>] (0:ℝ)) (𝓝 |deriv h 0|) :=
      (hderiv_cont.tendsto.mono_left nhdsWithin_le_nhds).norm
    have hdist : ∀ᶠ s in 𝓝[>] (0:ℝ), dist (|deriv h s|) (|deriv h 0|) < 1 := by
      simpa using (Metric.tendsto_nhds.1 htend) 1 (by norm_num)
    filter_upwards [hdist] with s hs
    have hnorm : abs (abs (deriv h s) - abs (deriv h 0)) < 1 := by
      simpa [Real.dist_eq] using hs
    have hlt : |deriv h s| < |deriv h 0| + 1 := by
      have h' := (abs_sub_lt_iff.mp hnorm).1
      linarith
    dsimp [C]
    exact le_of_lt hlt
  have hs_event : ∀ᶠ s in 𝓝[>] (0:ℝ), |s| ≤ 1 := by
    have htend : Tendsto (fun s : ℝ => |s|) (𝓝[>] (0:ℝ)) (𝓝 |(0:ℝ)|) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).norm
    have hlt : ∀ᶠ s in 𝓝[>] (0:ℝ), |s| < 1 := by
      simpa using (Metric.tendsto_nhds.1 htend) 1 (by norm_num)
    filter_upwards [hlt] with s hs
    exact le_of_lt hs
  let B : ℝ := (Mf ^ 2 + (R + 1) ^ 2) ^ (n - 1) * (R + C)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB_nonneg, ?_⟩
  filter_upwards [hh_event, hderiv_event, hs_event] with s hhs hderiv hs
  intro t ht
  have ht_mem_uIoc := ht
  have hRle : -R ≤ R := by linarith
  have htIoc : t ∈ Set.Ioc (-R) R := by
    simpa [Set.uIoc_of_le hRle] using ht
  have ht_le_R : t ≤ R := htIoc.2
  have ht_gt : -R < t := htIoc.1
  have ht_abs_R : |t| ≤ R := by
    rw [abs_le]
    constructor <;> linarith
  have hf_le : |f t| ≤ Mf := hMf t
  have hL_bound : |s * t + h s| ≤ R + 1 := by
    calc
      |s * t + h s| ≤ |s * t| + |h s| := abs_add_le _ _
      _ = |s| * |t| + |h s| := by rw [abs_mul]
      _ ≤ 1 * R + 1 := by
        exact add_le_add (mul_le_mul hs ht_abs_R (abs_nonneg t) (by norm_num)) hhs
      _ = R + 1 := by ring
  have hf_sq_le : f t ^ 2 ≤ Mf ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (f t)) hf_le 2
    simpa [abs_pow] using h
  have hL_sq_le : (s * t + h s) ^ 2 ≤ (R + 1) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (s * t + h s)) hL_bound 2
    simpa [abs_pow] using h
  have hbase_bound : |f t ^ 2 - (s * t + h s) ^ 2| ≤ Mf ^ 2 + (R + 1) ^ 2 := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [hf_sq_le, hL_sq_le, sq_nonneg (f t), sq_nonneg (s * t + h s)]
  have hbase_abs_nonneg : 0 ≤ |f t ^ 2 - (s * t + h s) ^ 2| := abs_nonneg _
  have hpow_bound : |(f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1)| ≤ (Mf ^ 2 + (R + 1) ^ 2) ^ (n - 1) := by
    rw [abs_pow]
    exact pow_le_pow_left₀ hbase_abs_nonneg hbase_bound (n - 1)
  have hlin_bound : |t + deriv h s| ≤ R + C := by
    calc
      |t + deriv h s| ≤ |t| + |deriv h s| := abs_add_le _ _
      _ ≤ R + C := add_le_add ht_abs_R hderiv
  have hF_bound : |momentF n h f s t| ≤ B := by
    unfold momentF
    rw [abs_mul]
    dsimp [B]
    exact mul_le_mul hpow_bound hlin_bound (abs_nonneg _) (by positivity)
  have hG_bound : |momentG n h x y f s t| ≤ |momentF n h f s t| := by
    unfold momentG
    by_cases hmem : t ∈ Set.Ioc (-x s) (y s)
    · simp [hmem]
    · simp [hmem]
  exact le_trans hG_bound hF_bound


private lemma momentF_measurable {n : ℕ} {h f : ℝ → ℝ} (s : ℝ)
    (hf : Measurable f) (_hh : Measurable h) (_hhd : Measurable (deriv h)) :
    Measurable (fun t : ℝ => momentF n h f s t) := by
  unfold momentF
  fun_prop

private lemma momentG_measurable {n : ℕ} {h x y f : ℝ → ℝ} (s : ℝ)
    (hf : Measurable f) (_hh : Measurable h) (_hhd : Measurable (deriv h)) :
    Measurable (fun t : ℝ => momentG n h x y f s t) := by
  unfold momentG
  exact Measurable.indicator (momentF_measurable s hf _hh _hhd) measurableSet_Ioc

private lemma momentG_aestronglyMeasurable {n : ℕ} {h x y f : ℝ → ℝ} {R : ℝ} (s : ℝ)
    (hf : Measurable f) (_hh : Measurable h) (_hhd : Measurable (deriv h)) :
    AEStronglyMeasurable (fun t : ℝ => momentG n h x y f s t) (volume.restrict (Set.uIoc (-R) R)) := by
  exact (momentG_measurable s hf _hh _hhd).aestronglyMeasurable

private lemma tendsto_momentG_integral {n : ℕ} (hn : 2 ≤ n) {h x y f : ℝ → ℝ} {R : ℝ}
    (hRpos : 0 < R) (_hRgt1 : 1 < R)
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ) (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) :
    Tendsto (fun s : ℝ => ∫ t in (-R)..R, momentG n h x y f s t)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ t in (-R)..R, momentLimit n h f t)) := by
  have hf_meas : Measurable f :=
    measurable_of_support_subset_Icc_of_contDiffOn (a := -1) (b := 1) (by norm_num)
      hf_support hf_cont hf_left hf_right
  have hcont_h : Continuous h := continuousOn_univ.mp hh_cont.continuousOn
  have hh_meas : Measurable h := hcont_h.measurable
  have hderiv_cont : Continuous (deriv h) :=
    continuousOn_univ.mp (hh_cont.continuousOn_deriv_of_isOpen isOpen_univ (by simp))
  have hderiv_meas : Measurable (deriv h) := hderiv_cont.measurable
  obtain ⟨B, hB_nonneg, hB_event⟩ := eventually_momentG_bound (n := n) (h := h) (x := x) (y := y) (f := f)
    (R := R) hRpos hf_support hf_conc hf_left hf_right hh_cont h0
  have hF_meas : ∀ᶠ s in 𝓝[>] (0:ℝ),
      AEStronglyMeasurable (fun t : ℝ => momentG n h x y f s t) (volume.restrict (Set.uIoc (-R) R)) := by
    filter_upwards [] with s
    exact momentG_aestronglyMeasurable s hf_meas hh_meas hderiv_meas
  have h_bound : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ᵐ t ∂volume, t ∈ Set.uIoc (-R) R →
      ‖momentG n h x y f s t‖ ≤ B := by
    filter_upwards [hB_event] with s hs
    filter_upwards [] with t ht
    have hle := hs t ht
    simpa [Real.norm_eq_abs] using hle
  have h_bound_int : IntervalIntegrable (fun _ : ℝ => B) volume (-R) R := by
    exact continuous_const.intervalIntegrable (-R) R
  have h_lim : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-R) R →
      Tendsto (fun s : ℝ => momentG n h x y f s t) (𝓝[>] (0:ℝ)) (𝓝 (momentLimit n h f t)) := by
    filter_upwards [] with t ht
    exact tendsto_momentG_pointwise hn hf_support hf_cont hf_left hf_right hf_pos hh_cont h0 hxy
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence (E := ℝ) (a := -R) (b := R)
    (f := fun t => momentLimit n h f t) (F := fun s t => momentG n h x y f s t) (bound := fun _ => B)
    hF_meas h_bound h_bound_int h_lim


private lemma tendsto_h_over_s {h : ℝ → ℝ}
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ) (h0 : h 0 = 0) :
    Tendsto (fun s : ℝ => h s / s) (𝓝[>] (0:ℝ)) (𝓝 (deriv h 0)) := by
  have hdiff : DifferentiableAt ℝ h 0 := by
    exact (hh_cont.contDiffAt (by simp)).differentiableAt (by simp)
  have hderivAt : HasDerivAt h (deriv h 0) 0 := hdiff.hasDerivAt
  have hlim := hderivAt.tendsto_slope_zero_right
  have hcongr : (fun s : ℝ => s⁻¹ * (h (0 + s) - h 0)) =ᶠ[𝓝[>] (0:ℝ)] (fun s => h s / s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs_ne : s ≠ 0 := ne_of_gt hs
    field_simp [hs_ne]
    simp [h0]
  exact Filter.Tendsto.congr' hcongr hlim

private lemma integral_momentLimit_eq {n : ℕ} (hn : 2 ≤ n) {h f : ℝ → ℝ} {R : ℝ}
    (hR1 : 1 < R)
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0) :
    (∫ t in (-R)..R, momentLimit n h f t) =
      ∫ t in (-1 : ℝ)..1, (f t ^ 2) ^ (n - 1) * (t + deriv h 0) := by
  let g : ℝ → ℝ := fun t => (f t ^ 2) ^ (n - 1) * (t + deriv h 0)
  have h_eq_g : momentLimit n h f = g := by
    ext t
    unfold momentLimit g
    by_cases ht : t ∈ Set.Ioo (-1 : ℝ) 1
    · simp [ht]
    · have hf0 : f t = 0 := f_eq_zero_of_not_mem_Ioo hf_support hf_left hf_right ht
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      simp [ht, hf0, hzero]
  have hsuppG : Function.support (momentLimit n h f) ⊆ Set.Ioc (-R) R := by
    intro t ht
    rw [h_eq_g] at ht
    have hf_ne : f t ≠ 0 := by
      intro hf0
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      have : g t = 0 := by simp [g, hf0, hzero]
      exact ht this
    have ht_supp : t ∈ Function.support f := by simpa [Function.mem_support] using hf_ne
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := hf_support ht_supp
    have ht_mem : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      constructor
      · exact lt_of_le_of_ne htIcc.1 (by
          intro heq
          subst t
          exact hf_ne hf_left)
      · exact htIcc.2
    exact ⟨by linarith [ht_mem.1, hR1], by linarith [ht_mem.2, hR1]⟩
  have hsuppg : Function.support g ⊆ Set.Ioc (-1 : ℝ) 1 := by
    intro t ht
    have hf_ne : f t ≠ 0 := by
      intro hf0
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      have : g t = 0 := by simp [g, hf0, hzero]
      exact ht this
    have ht_supp : t ∈ Function.support f := by simpa [Function.mem_support] using hf_ne
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := hf_support ht_supp
    constructor
    · exact lt_of_le_of_ne htIcc.1 (by
        intro heq
        subst t
        exact hf_ne hf_left)
    · exact htIcc.2
  have hG := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := momentLimit n h f) hsuppG
  have hg := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := g) hsuppg
  have h_all : (∫ t : ℝ, momentLimit n h f t) = ∫ t : ℝ, g t := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    rw [h_eq_g]
  calc
    (∫ t in (-R)..R, momentLimit n h f t) = ∫ t : ℝ, momentLimit n h f t := hG
    _ = ∫ t : ℝ, g t := h_all
    _ = ∫ t in (-1 : ℝ)..1, g t := hg.symm


private lemma intervalIntegrable_of_bounded_measurable {f : ℝ → ℝ} {a b C : ℝ}
    (hf : Measurable f)
    (hbound : ∀ᵐ t ∂volume.restrict (Set.uIoc a b), |f t| ≤ C) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  apply MeasureTheory.IntegrableOn.of_bound ?_ (hf.aestronglyMeasurable.restrict) C hbound
  rw [Real.volume_uIoc]
  exact ENNReal.ofReal_lt_top

private lemma pos_integral_of_pos_on_Ioo {W : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hW_meas : Measurable W)
    (hW_nonneg : ∀ᵐ t ∂volume, 0 ≤ W t)
    (hW_pos : ∀ t ∈ Set.Ioo a b, 0 < W t)
    (hW_bound : ∀ᵐ t ∂volume.restrict (Set.uIoc a b), |W t| ≤ C) :
    0 < ∫ t in a..b, W t := by
  have h_int : IntervalIntegrable W volume a b :=
    intervalIntegrable_of_bounded_measurable hW_meas hW_bound
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae hW_nonneg h_int]
  constructor
  · exact hab
  · have hsupp : Set.Ioo a b ⊆ Function.support W := by
      intro t ht
      exact ne_of_gt (hW_pos t ht)
    have hmeasure_pos : 0 < volume (Set.Ioo a b) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    have hmono : volume (Set.Ioo a b) ≤ volume (Function.support W ∩ Set.Ioc a b) := by
      apply measure_mono
      intro t ht
      exact ⟨hsupp ht, ⟨ht.1, le_of_lt ht.2⟩⟩
    exact lt_of_lt_of_le hmeasure_pos hmono

private lemma moment_center_abs_lt_one {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} {c : ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hzero : (∫ t in (-1 : ℝ)..1, (f t ^ 2) ^ (n - 1) * (t + c)) = 0) :
    |c| < 1 := by
  let W : ℝ → ℝ := fun t => (f t ^ 2) ^ (n - 1)
  have hf_meas : Measurable f :=
    measurable_of_support_subset_Icc_of_contDiffOn (a := -1) (b := 1) (by norm_num)
      hf_support hf_cont hf_left hf_right
  obtain ⟨M, hMpos, hM⟩ := f_abs_le_global hf_support hf_conc hf_left hf_right
  have hW_meas : Measurable W := by unfold W; fun_prop
  have hW_nonneg : ∀ t, 0 ≤ W t := by
    intro t; unfold W; positivity
  have hW_pos_Ioo : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < W t := by
    intro t ht
    unfold W
    have hf0 : 0 < f t := hf_pos t ht
    have hsq : 0 < f t ^ 2 := sq_pos_of_pos hf0
    have hn1 : 0 < n - 1 := by omega
    exact pow_pos hsq (n - 1)
  have hW_bound_ae : ∀ᵐ t ∂volume.restrict (Set.uIoc (-1 : ℝ) 1), |W t| ≤ (M ^ 2) ^ (n - 1) := by
    filter_upwards [] with t
    unfold W
    have hf_abs : |f t| ≤ M := hM t
    have hf2 : f t ^ 2 ≤ M ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (f t)) hf_abs 2
      simpa [abs_pow] using h
    have hpow : (f t ^ 2) ^ (n - 1) ≤ (M ^ 2) ^ (n - 1) := by
      exact pow_le_pow_left₀ (sq_nonneg (f t)) hf2 (n - 1)
    have hnonneg : 0 ≤ (f t ^ 2) ^ (n - 1) := pow_nonneg (sq_nonneg (f t)) (n - 1)
    rw [abs_of_nonneg hnonneg]
    exact hpow
  have hW_int : IntervalIntegrable W volume (-1 : ℝ) 1 := by
    apply intervalIntegrable_of_bounded_measurable (a := -1) (b := 1) (C := (M ^ 2) ^ (n - 1))
    · exact hW_meas
    · simpa [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hW_bound_ae
  have hI0_pos : 0 < ∫ t in (-1 : ℝ)..1, W t := by
    exact pos_integral_of_pos_on_Ioo (a := -1) (b := 1) (C := (M ^ 2) ^ (n - 1))
      (by norm_num) hW_meas (by filter_upwards [] with t; exact hW_nonneg t) hW_pos_Ioo
      (by simpa [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hW_bound_ae)
  let P : ℝ → ℝ := fun t => (t + 1) * W t
  have hP_meas : Measurable P := by unfold P W; fun_prop
  have hP_nonneg_ae : ∀ᵐ t ∂volume, 0 ≤ P t := by
    filter_upwards [] with t
    unfold P W
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
    · have ht1 : -1 ≤ t := ht.1
      have ht2 : t ≤ 1 := ht.2
      have h1 : 0 ≤ t + 1 := by linarith
      positivity
    · have hf0 : f t = 0 := support_subset_iff_zero_of_not_mem hf_support ht
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      simp [hf0, hzero]
  have hP_pos_Ioo : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < P t := by
    intro t ht
    unfold P W
    have hf0 : 0 < f t := hf_pos t ht
    have hsq : 0 < f t ^ 2 := sq_pos_of_pos hf0
    have hn1 : 0 < n - 1 := by omega
    have hWpos : 0 < (f t ^ 2) ^ (n - 1) := pow_pos hsq (n - 1)
    have htpos : 0 < t + 1 := by linarith [ht.1]
    positivity
  have hW_abs_point : ∀ t : ℝ, |W t| ≤ (M ^ 2) ^ (n - 1) := by
    intro t
    unfold W
    have hf_abs : |f t| ≤ M := hM t
    have hf2 : f t ^ 2 ≤ M ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (f t)) hf_abs 2
      simpa [abs_pow] using h
    have hpow : (f t ^ 2) ^ (n - 1) ≤ (M ^ 2) ^ (n - 1) := by
      exact pow_le_pow_left₀ (sq_nonneg (f t)) hf2 (n - 1)
    have hnonneg : 0 ≤ (f t ^ 2) ^ (n - 1) := pow_nonneg (sq_nonneg (f t)) (n - 1)
    rw [abs_of_nonneg hnonneg]
    exact hpow
  have hP_bound_ae : ∀ᵐ t ∂volume.restrict (Set.uIoc (-1 : ℝ) 1), |P t| ≤ 2 * (M ^ 2) ^ (n - 1) := by
    filter_upwards [] with t
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
    · have ht1 : -1 ≤ t := ht.1
      have ht2 : t ≤ 1 := ht.2
      have hW_nonneg_t : 0 ≤ W t := hW_nonneg t
      have hW_le : W t ≤ (M ^ 2) ^ (n - 1) := by
        simpa [abs_of_nonneg hW_nonneg_t] using hW_abs_point t
      unfold P
      rw [abs_mul]
      rw [abs_of_nonneg hW_nonneg_t]
      have hpos : 0 ≤ t + 1 := by linarith
      have hle : t + 1 ≤ 2 := by linarith
      have hprod : (t + 1) * W t ≤ 2 * (M ^ 2) ^ (n - 1) := by
        have h1 : (t + 1) * W t ≤ (t + 1) * (M ^ 2) ^ (n - 1) :=
          mul_le_mul_of_nonneg_left hW_le hpos
        have h2 : (t + 1) * (M ^ 2) ^ (n - 1) ≤ 2 * (M ^ 2) ^ (n - 1) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
        exact le_trans h1 h2
      rw [abs_of_nonneg hpos]
      exact hprod
    · have hf0 : f t = 0 := support_subset_iff_zero_of_not_mem hf_support ht
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      unfold P W
      simp [hf0, hzero]
      positivity
  have hP_int_pos : 0 < ∫ t in (-1 : ℝ)..1, P t := by
    exact pos_integral_of_pos_on_Ioo (a := -1) (b := 1) (C := 2 * (M ^ 2) ^ (n - 1))
      (by norm_num) hP_meas hP_nonneg_ae hP_pos_Ioo
      (by simpa [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hP_bound_ae)
  let Q : ℝ → ℝ := fun t => (1 - t) * W t
  have hQ_meas : Measurable Q := by unfold Q W; fun_prop
  have hQ_nonneg_ae : ∀ᵐ t ∂volume, 0 ≤ Q t := by
    filter_upwards [] with t
    unfold Q W
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
    · have ht1 : -1 ≤ t := ht.1
      have ht2 : t ≤ 1 := ht.2
      have h1 : 0 ≤ 1 - t := by linarith
      positivity
    · have hf0 : f t = 0 := support_subset_iff_zero_of_not_mem hf_support ht
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      simp [hf0, hzero]
  have hQ_pos_Ioo : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < Q t := by
    intro t ht
    unfold Q W
    have hf0 : 0 < f t := hf_pos t ht
    have hsq : 0 < f t ^ 2 := sq_pos_of_pos hf0
    have hn1 : 0 < n - 1 := by omega
    have hWpos : 0 < (f t ^ 2) ^ (n - 1) := pow_pos hsq (n - 1)
    have htpos : 0 < 1 - t := by linarith [ht.2]
    positivity
  have hQ_bound_ae : ∀ᵐ t ∂volume.restrict (Set.uIoc (-1 : ℝ) 1), |Q t| ≤ 2 * (M ^ 2) ^ (n - 1) := by
    filter_upwards [] with t
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
    · have ht1 : -1 ≤ t := ht.1
      have ht2 : t ≤ 1 := ht.2
      have hW_nonneg_t : 0 ≤ W t := hW_nonneg t
      have hW_le : W t ≤ (M ^ 2) ^ (n - 1) := by
        simpa [abs_of_nonneg hW_nonneg_t] using hW_abs_point t
      unfold Q
      rw [abs_mul]
      rw [abs_of_nonneg hW_nonneg_t]
      have hpos : 0 ≤ 1 - t := by linarith
      have hle : 1 - t ≤ 2 := by linarith
      have hprod : (1 - t) * W t ≤ 2 * (M ^ 2) ^ (n - 1) := by
        have h1 : (1 - t) * W t ≤ (1 - t) * (M ^ 2) ^ (n - 1) :=
          mul_le_mul_of_nonneg_left hW_le hpos
        have h2 : (1 - t) * (M ^ 2) ^ (n - 1) ≤ 2 * (M ^ 2) ^ (n - 1) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
        exact le_trans h1 h2
      rw [abs_of_nonneg hpos]
      exact hprod
    · have hf0 : f t = 0 := support_subset_iff_zero_of_not_mem hf_support ht
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      unfold Q W
      simp [hf0, hzero]
      positivity
  have hQ_int_pos : 0 < ∫ t in (-1 : ℝ)..1, Q t := by
    exact pos_integral_of_pos_on_Ioo (a := -1) (b := 1) (C := 2 * (M ^ 2) ^ (n - 1))
      (by norm_num) hQ_meas hQ_nonneg_ae hQ_pos_Ioo
      (by simpa [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hQ_bound_ae)
  have hWt_meas : Measurable (fun t => W t * t) := by unfold W; fun_prop
  have hWt_bound_ae : ∀ᵐ t ∂volume.restrict (Set.uIoc (-1 : ℝ) 1), |W t * t| ≤ (M ^ 2) ^ (n - 1) := by
    filter_upwards [] with t
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
    · rcases ht with ⟨ht1, ht2⟩
      have ht_abs : |t| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul]
      simpa using mul_le_mul (hW_abs_point t) ht_abs (abs_nonneg t) (by positivity)
    · have hf0 : f t = 0 := support_subset_iff_zero_of_not_mem hf_support ht
      have hn1 : n - 1 ≠ 0 := by omega
      have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
      unfold W
      simp [hf0, hzero]
      positivity
  have hWt_int : IntervalIntegrable (fun t => W t * t) volume (-1 : ℝ) 1 :=
    intervalIntegrable_of_bounded_measurable hWt_meas hWt_bound_ae
  have hP_int : IntervalIntegrable P volume (-1 : ℝ) 1 :=
    intervalIntegrable_of_bounded_measurable hP_meas
      (by simpa [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hP_bound_ae)
  have hQ_int : IntervalIntegrable Q volume (-1 : ℝ) 1 :=
    intervalIntegrable_of_bounded_measurable hQ_meas
      (by simpa [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hQ_bound_ae)
  have hP_eq : (∫ t in (-1 : ℝ)..1, P t) = (∫ t in (-1 : ℝ)..1, W t * t) + (∫ t in (-1 : ℝ)..1, W t) := by
    have hcongr : (∫ t in (-1 : ℝ)..1, P t) = ∫ t in (-1 : ℝ)..1, (W t * t + W t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      unfold P
      ring
    rw [hcongr]
    exact intervalIntegral.integral_add hWt_int hW_int
  have hQ_eq : (∫ t in (-1 : ℝ)..1, Q t) = (∫ t in (-1 : ℝ)..1, W t) - (∫ t in (-1 : ℝ)..1, W t * t) := by
    have hcongr : (∫ t in (-1 : ℝ)..1, Q t) = ∫ t in (-1 : ℝ)..1, (W t - W t * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      unfold Q
      ring
    rw [hcongr]
    exact intervalIntegral.integral_sub hW_int hWt_int
  have hI1_bounds : - (∫ t in (-1 : ℝ)..1, W t) < (∫ t in (-1 : ℝ)..1, W t * t) ∧
      (∫ t in (-1 : ℝ)..1, W t * t) < ∫ t in (-1 : ℝ)..1, W t := by
    have hP_pos' := hP_int_pos
    rw [hP_eq] at hP_pos'
    have hQ_pos' := hQ_int_pos
    rw [hQ_eq] at hQ_pos'
    constructor <;> linarith
  have hzeroW : (∫ t in (-1 : ℝ)..1, W t * (t + c)) = 0 := by
    simpa [W] using hzero
  have hzero' : (∫ t in (-1 : ℝ)..1, W t * t) + (∫ t in (-1 : ℝ)..1, W t) * c = 0 := by
    have hcongr : (∫ t in (-1 : ℝ)..1, W t * (t + c)) = ∫ t in (-1 : ℝ)..1, (W t * t + W t * c) := by
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    have hsum : (∫ t in (-1 : ℝ)..1, (W t * t + W t * c)) =
        (∫ t in (-1 : ℝ)..1, W t * t) + (∫ t in (-1 : ℝ)..1, W t * c) := by
      have hWc_int : IntervalIntegrable (fun t => W t * c) volume (-1 : ℝ) 1 := by
        simpa [mul_comm] using hW_int.const_mul c
      exact intervalIntegral.integral_add hWt_int hWc_int
    have hWc : (∫ t in (-1 : ℝ)..1, W t * c) = (∫ t in (-1 : ℝ)..1, W t) * c :=
      intervalIntegral.integral_mul_const c W
    rw [hcongr, hsum, hWc] at hzeroW
    simpa using hzeroW
  have hI0_ne : (∫ t in (-1 : ℝ)..1, W t) ≠ 0 := ne_of_gt hI0_pos
  have hc_eq : c = - (∫ t in (-1 : ℝ)..1, W t * t) / (∫ t in (-1 : ℝ)..1, W t) := by
    field_simp [hI0_ne]
    linarith
  rw [hc_eq]
  have hI0 := hI0_pos
  rcases hI1_bounds with ⟨hleft, hright⟩
  rw [abs_lt]
  constructor
  · have hdiv_gt : -1 < - (∫ t in (-1 : ℝ)..1, W t * t) / (∫ t in (-1 : ℝ)..1, W t) := by
      rw [neg_div]
      rw [neg_lt_neg_iff]
      rw [div_lt_iff₀ hI0]
      nlinarith
    exact hdiv_gt
  · have hdiv_lt : - (∫ t in (-1 : ℝ)..1, W t * t) / (∫ t in (-1 : ℝ)..1, W t) < 1 := by
      rw [neg_div]
      rw [neg_lt]
      rw [lt_div_iff₀ hI0]
      nlinarith
    exact hdiv_lt


lemma moment_deriv_zero_abs_lt_one {n : ℕ} (hn : 2 ≤ n)
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
    |deriv h 0| < 1 := by
  let B0 : ℝ := |deriv h 0| + 1
  let R : ℝ := B0 + 1
  have hB0_nonneg : 0 ≤ B0 := by dsimp [B0]; linarith [abs_nonneg (deriv h 0)]
  have hRpos : 0 < R := by dsimp [R, B0]; linarith [abs_nonneg (deriv h 0)]
  have hRgt1 : 1 < R := by dsimp [R, B0]; linarith [abs_nonneg (deriv h 0)]
  have hf_cont' : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1) :=
    ContDiffOn.of_le hf_cont le_top
  have hh_cont' : ContDiffOn ℝ ∞ h Set.univ :=
    ContDiffOn.of_le hh_cont le_top
  have htend_slope := tendsto_h_over_s hh_cont' h0
  have hle_slope : ∀ᶠ s in 𝓝[>] (0:ℝ), |h s / s| ≤ B0 := by
    have hlt : ∀ᶠ s in 𝓝[>] (0:ℝ), dist (h s / s) (deriv h 0) < 1 := by
      simpa using (Metric.tendsto_nhds.1 htend_slope) 1 (by norm_num)
    filter_upwards [hlt] with s hs
    have hnorm : |h s / s - deriv h 0| < 1 := by
      simpa [Real.dist_eq] using hs
    have hle_abs : |h s / s| ≤ |deriv h 0| + 1 := by
      have htri := abs_abs_sub_abs_le_abs_sub (h s / s) (deriv h 0)
      have htri' : abs (abs (h s / s) - abs (deriv h 0)) < 1 := lt_of_le_of_lt htri hnorm
      have h' := (abs_sub_lt_iff.mp htri').1
      linarith
    dsimp [B0]
    exact hle_abs
  have hroot_bound_ev := roots_bounded_of_tendsto (h := h) (x := x) (y := y) (f := f)
    hf_support hxy hB0_nonneg hle_slope
  have hlim := tendsto_momentG_integral (n := n) hn (h := h) (x := x) (y := y) (f := f)
    (R := R) hRpos hRgt1 hf_support hf_cont' hf_conc hf_left hf_right hf_pos hh_cont' h0 hxy
  have heq_zero : (fun s : ℝ => ∫ t in (-R)..R, momentG n h x y f s t) =ᶠ[𝓝[>] (0:ℝ)] 0 := by
    filter_upwards [hroot_bound_ev, self_mem_nhdsWithin] with s hs hspos
    have hs_pos : 0 < s := hspos
    have hxR : x s ≤ R := by
      have hxmax := hs.1
      have hB0_ge_one : 1 ≤ B0 := by dsimp [B0]; linarith [abs_nonneg (deriv h 0)]
      have hmax_le : max 1 B0 ≤ R := by
        rw [max_eq_right hB0_ge_one]
        dsimp [R]
        linarith
      exact le_trans hxmax hmax_le
    have hyR : y s ≤ R := by
      have hymax := hs.2
      have hB0_ge_one : 1 ≤ B0 := by dsimp [B0]; linarith [abs_nonneg (deriv h 0)]
      have hmax_le : max 1 B0 ≤ R := by
        rw [max_eq_right hB0_ge_one]
        dsimp [R]
        linarith
      exact le_trans hymax hmax_le
    rcases hxy s hs_pos with ⟨hxpos, hypos, hfy, hfx⟩
    have hab : -x s ≤ y s := by linarith
    have hR1 : -R ≤ -x s := by linarith
    have hR2 : y s ≤ R := hyR
    have hJ' : (∫ t in (-x s)..(y s), momentF n h f s t) = 0 := by
      simpa [momentF] using hJ s hs_pos
    have heq := intervalIntegral_eq_fixed_indicator (F := fun t => momentF n h f s t)
      (a := -x s) (b := y s) (R := R) hR1 hab hR2
    have hGzero : (∫ t in (-R)..R, momentG n h x y f s t) = 0 := by
      unfold momentG
      rw [← heq]
      exact hJ'
    exact hGzero
  have hzero_tend : Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 (∫ t in (-R)..R, momentLimit n h f t)) :=
    Filter.Tendsto.congr' heq_zero hlim
  have hL0 : (∫ t in (-R)..R, momentLimit n h f t) = 0 := by
    exact tendsto_nhds_unique hzero_tend tendsto_const_nhds
  have hcenter : (∫ t in (-1 : ℝ)..1, (f t ^ 2) ^ (n - 1) * (t + deriv h 0)) = 0 := by
    rw [← integral_momentLimit_eq (n := n) hn (h := h) (f := f) (R := R) hRgt1 hf_support hf_left hf_right]
    exact hL0
  exact moment_center_abs_lt_one hn hf_support hf_cont' hf_conc hf_left hf_right hf_pos hcenter

end Commons.Geometry.Ulam
