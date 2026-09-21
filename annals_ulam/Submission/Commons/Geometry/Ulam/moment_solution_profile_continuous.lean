import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Geometry.Ulam

open scoped ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false
set_option linter.unusedVariables false

private lemma concave_ratio_antitone_right
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (hf0 : 0 ≤ f 0) :
    AntitoneOn (fun t : ℝ => f t / t) (Set.Ioo 0 1) := by
  intro u hu v hv huv
  dsimp
  have hu0 : 0 < u := hu.1
  have hv0 : 0 < v := hv.1
  have h0mem : (0 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
  have hvmem : v ∈ Set.Icc (-1) 1 := by
    exact ⟨by linarith [hv0], by linarith [hv.2]⟩
  have hlambda_nonneg : 0 ≤ 1 - u / v := by
    have : u / v ≤ 1 := (div_le_one hv0).2 huv
    linarith
  have hlambda2 : (1 - u / v) + u / v = 1 := by ring
  have hconc := hf.2 h0mem hvmem
    (show 0 ≤ 1 - u / v from hlambda_nonneg)
    (show 0 ≤ u / v from div_nonneg (le_of_lt hu0) (le_of_lt hv0))
    (show (1 - u / v) + u / v = 1 from hlambda2)
  have hconc' : (1 - u / v) * f 0 + (u / v) * f v ≤ f u := by
    have harg' : (u / v) * v = u := by
      field_simp [hv0.ne']
    simpa [harg'] using hconc
  have hmul : (u / v) * f v ≤ f u := by
    have hterm : 0 ≤ (1 - u / v) * f 0 := mul_nonneg hlambda_nonneg hf0
    linarith
  have hgoal : f v / v ≤ f u / u := by
    have hmul' : (u / v) * f v ≤ f u := hmul
    field_simp [hu0.ne', hv0.ne'] at hmul' ⊢
    nlinarith
  exact hgoal

private lemma concave_ratio_antitone_left
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (hf0 : 0 ≤ f 0) :
    AntitoneOn (fun t : ℝ => f (-t) / t) (Set.Ioo 0 1) := by
  have hg : ConcaveOn ℝ (Set.Icc (-1) 1) (fun t : ℝ => f (-t)) := by
    refine ⟨hf.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : -x ∈ Set.Icc (-1) 1 := by
      rcases hx with ⟨hx1, hx2⟩
      constructor <;> linarith
    have hy' : -y ∈ Set.Icc (-1) 1 := by
      rcases hy with ⟨hy1, hy2⟩
      constructor <;> linarith
    have h := hf.2 hx' hy' ha hb hab
    have harg : a • (-x) + b • (-y) = -(a • x + b • y) := by
      simp [smul_eq_mul]
      ring
    rw [harg] at h
    simpa [smul_eq_mul] using h
  exact concave_ratio_antitone_right hg (by simpa using hf0)

private lemma small_moment_data
    {τ : ℝ} {h x y f : ℝ → ℝ}
    (_hτ : 0 < τ) (_hτsmall : 2 * τ < 1)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hf_supp : Function.support f ⊆ Set.Icc (-1) 1)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hxy : ∀ s : ℝ, 0 < s →
      0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) :
    ∀ s : ℝ, 0 < s → s < 1 - 2 * τ →
      0 < y s ∧ y s < 1 ∧ f (y s) = s * y s ∧
      0 < x s ∧ x s < 1 ∧ f (-x s) = s * x s := by
  intro s hs hs_small
  have hs_not : s ∉ Set.Icc (1 - 2 * τ) (1 - τ) := by
    intro hsmem
    have : 1 - 2 * τ ≤ s := hsmem.1
    linarith
  have hh0 : h s = 0 := by
    rw [Function.support_subset_iff'] at hh_supp
    exact hh_supp s hs_not
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  have hy_ne : f (y s) ≠ 0 := by
    intro hfy0
    have hright_sq : (s * y s + h s) ^ 2 = 0 := by simpa [hfy0] using hfy_sq.symm
    have hright : s * y s + h s = 0 := sq_eq_zero_iff.mp hright_sq
    have : s * y s = 0 := by simpa [hh0] using hright
    have : s = 0 ∨ y s = 0 := mul_eq_zero.mp this
    rcases this with h | h
    · linarith
    · linarith
  have hy_support : y s ∈ Function.support f := by
    rwa [Function.mem_support]
  have hy_mem_Icc : y s ∈ Set.Icc (-1) 1 := hf_supp hy_support
  have hy_le_one : y s ≤ 1 := hy_mem_Icc.2
  have hy_lt_one : y s < 1 := lt_of_le_of_ne hy_le_one (by
    intro hyeq
    have : f (y s) = 0 := by simp [hyeq, hf_right]
    exact hy_ne this)
  have hy_mem_Ioo : y s ∈ Set.Ioo (-1) 1 := ⟨by linarith [hypos], hy_lt_one⟩
  have hfy_pos : 0 < f (y s) := hf_pos (y s) hy_mem_Ioo
  have hfy_eq_or : f (y s) = s * y s + h s ∨ f (y s) = -(s * y s + h s) := by
    have h := sq_eq_sq_iff_eq_or_eq_neg.mp hfy_sq
    simpa [hh0] using h
  have hright_pos : 0 < s * y s + h s := by simpa [hh0] using mul_pos hs hypos
  have hfy_eq : f (y s) = s * y s + h s := by
    rcases hfy_eq_or with h | h
    · exact h
    · have : f (y s) = - (s * y s) := by simpa [hh0] using h
      linarith
  have hfy_eq' : f (y s) = s * y s := by simpa [hh0] using hfy_eq

  have hx_ne : f (-x s) ≠ 0 := by
    intro hfx0
    have hleft_sq : (s * (-x s) + h s) ^ 2 = 0 := by simpa [hfx0] using hfx_sq.symm
    have hleft : s * (-x s) + h s = 0 := sq_eq_zero_iff.mp hleft_sq
    have : s * (-x s) = 0 := by simpa [hh0] using hleft
    have : s = 0 ∨ -x s = 0 := mul_eq_zero.mp this
    rcases this with h | h
    · linarith
    · have : x s = 0 := by linarith
      linarith
  have hx_support : -x s ∈ Function.support f := by
    rwa [Function.mem_support]
  have hx_mem_Icc : -x s ∈ Set.Icc (-1) 1 := hf_supp hx_support
  have hx_le_one : -x s ≤ 1 := hx_mem_Icc.2
  have hx_ne_neg1 : -x s ≠ -1 := by
    intro h
    have : f (-x s) = 0 := by simp [h, hf_left]
    exact hx_ne this
  have hx_gt_neg1 : -1 < -x s := lt_of_le_of_ne hx_mem_Icc.1 hx_ne_neg1.symm
  have hx_ne_one : -x s ≠ 1 := by
    intro h
    have : f (-x s) = 0 := by simp [h, hf_right]
    exact hx_ne this
  have hx_lt_one_strict : -x s < 1 := lt_of_le_of_ne hx_le_one hx_ne_one
  have hx_lt_one : x s < 1 := by linarith
  have hx_mem_Ioo : -x s ∈ Set.Ioo (-1) 1 := ⟨hx_gt_neg1, hx_lt_one_strict⟩
  have hfx_pos : 0 < f (-x s) := hf_pos (-x s) hx_mem_Ioo
  have hfx_eq_or : f (-x s) = s * (-x s) + h s ∨ f (-x s) = -(s * (-x s) + h s) := by
    have h := sq_eq_sq_iff_eq_or_eq_neg.mp hfx_sq
    simpa [hh0] using h
  have hfx_eq : f (-x s) = s * x s := by
    rcases hfx_eq_or with h | h
    · have : f (-x s) = - (s * x s) := by
        simpa [hh0, mul_neg, neg_mul] using h
      have hsx_pos : 0 < s * x s := mul_pos hs hxpos
      linarith
    · simpa [hh0, mul_neg, neg_mul] using h
  exact ⟨hypos, hy_lt_one, hfy_eq', hxpos, hx_lt_one, hfx_eq⟩

private lemma continuousWithinAt_right_of_moment
    {τ : ℝ} {h x y f : ℝ → ℝ}
    (_hτ : 0 < τ) (hτsmall : 2 * τ < 1)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hf_supp : Function.support f ⊆ Set.Icc (-1) 1)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hxy : ∀ s : ℝ, 0 < s →
      0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) :
    ContinuousWithinAt f (Set.Iic 1) 1 := by
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  have hf0_nonneg : 0 ≤ f 0 := le_of_lt (hf_pos 0 (by norm_num))
  let s0 : ℝ := min (ε / 2) ((1 - 2 * τ) / 2)
  have hs0pos : 0 < s0 := by
    dsimp [s0]
    exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hτsmall))
  have hs0_lt : s0 < 1 - 2 * τ := by
    dsimp [s0]
    have hpos : 0 < 1 - 2 * τ := sub_pos.mpr hτsmall
    have : (1 - 2 * τ) / 2 < 1 - 2 * τ := by nlinarith
    linarith [min_le_right (ε / 2) ((1 - 2 * τ) / 2)]
  have hs0_lt_ε : s0 < ε := by
    dsimp [s0]
    have : ε / 2 < ε := by nlinarith
    linarith [min_le_left (ε / 2) ((1 - 2 * τ) / 2)]
  have hsmall := small_moment_data _hτ hτsmall hh_supp hf_supp hf_left hf_right hf_pos hxy s0 hs0pos hs0_lt
  rcases hsmall with ⟨hypos, hy_lt_one, hfy_eq, hxpos, hx_lt_one, hfx_eq⟩
  let δ : ℝ := (1 - y s0) / 2
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hIoc_mem : Set.Ioc (1 - δ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iic 1) := by
    apply Ioc_mem_nhdsLE
    dsimp [δ]
    linarith
  refine Filter.mem_of_superset hIoc_mem ?_
  intro t ht
  have ht_le_one : t ≤ 1 := ht.2
  have ht_gt : 1 - δ < t := ht.1
  by_cases ht1 : t = 1
  · subst t
    simp [hf_right, hε]
  · have ht_lt_one : t < 1 := lt_of_le_of_ne ht_le_one ht1
    have ht_pos : 0 < t := by
      dsimp [δ] at ht_gt
      nlinarith
    have ht_mem_Ioo : t ∈ Set.Ioo (-1) 1 := by
      constructor <;> linarith
    have hft_pos : 0 < f t := hf_pos t ht_mem_Ioo
    have hft_nonneg : 0 ≤ f t := le_of_lt hft_pos
    have hy_mem_Ioo : y s0 ∈ Set.Ioo 0 1 := ⟨hypos, hy_lt_one⟩
    have ht_mem_Ioo_01 : t ∈ Set.Ioo 0 1 := ⟨ht_pos, ht_lt_one⟩
    have hy_le_t : y s0 ≤ t := by
      dsimp [δ] at ht_gt
      nlinarith
    have hratio := concave_ratio_antitone_right hf_conc hf0_nonneg
    have hrat : f t / t ≤ f (y s0) / y s0 := hratio hy_mem_Ioo ht_mem_Ioo_01 hy_le_t
    have hy_ratio : f (y s0) / y s0 = s0 := by
      rw [hfy_eq]
      field_simp [hypos.ne']
    have hrat' : f t / t ≤ s0 := by
      simpa [hy_ratio] using hrat
    have hft_le : f t ≤ s0 * t := (div_le_iff₀ ht_pos).1 hrat'
    have hft_lt_ε : f t < ε := by
      have hs0_nonneg : 0 ≤ s0 := le_of_lt hs0pos
      have hle : s0 * t ≤ s0 := by
        have := mul_le_mul_of_nonneg_left ht_le_one hs0_nonneg
        simpa using this
      linarith
    have hdist : dist (f t) (f 1) = f t := by
      simp [hf_right, abs_of_nonneg hft_nonneg]
    change dist (f t) (f 1) < ε
    rw [hdist]
    exact hft_lt_ε

private lemma continuousWithinAt_left_of_moment
    {τ : ℝ} {h x y f : ℝ → ℝ}
    (_hτ : 0 < τ) (hτsmall : 2 * τ < 1)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hf_supp : Function.support f ⊆ Set.Icc (-1) 1)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hxy : ∀ s : ℝ, 0 < s →
      0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) :
    ContinuousWithinAt f (Set.Ici (-1)) (-1) := by
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  have hf0_nonneg : 0 ≤ f 0 := le_of_lt (hf_pos 0 (by norm_num))
  let s0 : ℝ := min (ε / 2) ((1 - 2 * τ) / 2)
  have hs0pos : 0 < s0 := by
    dsimp [s0]
    exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hτsmall))
  have hs0_lt : s0 < 1 - 2 * τ := by
    dsimp [s0]
    have hpos : 0 < 1 - 2 * τ := sub_pos.mpr hτsmall
    have : (1 - 2 * τ) / 2 < 1 - 2 * τ := by nlinarith
    linarith [min_le_right (ε / 2) ((1 - 2 * τ) / 2)]
  have hs0_lt_ε : s0 < ε := by
    dsimp [s0]
    have : ε / 2 < ε := by nlinarith
    linarith [min_le_left (ε / 2) ((1 - 2 * τ) / 2)]
  have hsmall := small_moment_data _hτ hτsmall hh_supp hf_supp hf_left hf_right hf_pos hxy s0 hs0pos hs0_lt
  rcases hsmall with ⟨hypos, hy_lt_one, hfy_eq, hxpos, hx_lt_one, hfx_eq⟩
  let δ : ℝ := (1 - x s0) / 2
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hIcc_mem : Set.Icc (-1 : ℝ) (-1 + δ) ∈ nhdsWithin (-1 : ℝ) (Set.Ici (-1)) := by
    apply Icc_mem_nhdsGE
    dsimp [δ]
    linarith
  refine Filter.mem_of_superset hIcc_mem ?_
  intro t ht
  have ht_ge_neg1 : -1 ≤ t := ht.1
  have ht_le : t ≤ -1 + δ := ht.2
  by_cases ht_neg1 : t = -1
  · subst t
    simp [hf_left, hε]
  · have hne : -1 ≠ t := by
      intro h
      exact ht_neg1 h.symm
    have ht_gt_neg1 : -1 < t := lt_of_le_of_ne ht_ge_neg1 hne
    have ht_neg : t < 0 := by
      dsimp [δ] at ht_le
      nlinarith
    have ht_lt_one : t < 1 := by linarith
    have ht_mem_Ioo : t ∈ Set.Ioo (-1) 1 := ⟨ht_gt_neg1, ht_lt_one⟩
    have hft_pos : 0 < f t := hf_pos t ht_mem_Ioo
    have hft_nonneg : 0 ≤ f t := le_of_lt hft_pos
    let u : ℝ := -t
    have hu_pos : 0 < u := by dsimp [u]; linarith
    have hu_lt_one : u < 1 := by dsimp [u]; linarith
    have hx_mem_Ioo : x s0 ∈ Set.Ioo 0 1 := ⟨hxpos, hx_lt_one⟩
    have hu_mem_Ioo : u ∈ Set.Ioo 0 1 := ⟨hu_pos, hu_lt_one⟩
    have hx_le_u : x s0 ≤ u := by
      dsimp [δ] at ht_le
      dsimp [u]
      nlinarith
    have hratio := concave_ratio_antitone_left hf_conc hf0_nonneg
    have hrat : f (-u) / u ≤ f (-x s0) / x s0 := hratio hx_mem_Ioo hu_mem_Ioo hx_le_u
    have hx_ratio : f (-x s0) / x s0 = s0 := by
      rw [hfx_eq]
      field_simp [hxpos.ne']
    have hrat' : f (-u) / u ≤ s0 := by
      simpa [hx_ratio] using hrat
    have hft_le : f t ≤ s0 * u := by
      have h := (div_le_iff₀ hu_pos).1 hrat'
      simpa [u] using h
    have hft_lt_ε : f t < ε := by
      have hs0_nonneg : 0 ≤ s0 := le_of_lt hs0pos
      have hle : s0 * u ≤ s0 := by
        have := mul_le_mul_of_nonneg_left hu_lt_one.le hs0_nonneg
        simpa using this
      linarith
    have hdist : dist (f t) (f (-1)) = f t := by
      simp [hf_left, abs_of_nonneg hft_nonneg]
    change dist (f t) (f (-1)) < ε
    rw [hdist]
    exact hft_lt_ε

lemma moment_solution_profile_continuous
    {τ : ℝ} {h x y f : ℝ → ℝ}
    (hτ : 0 < τ) (hτsmall : 2 * τ < 1)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hf_supp : Function.support f ⊆ Set.Icc (-1) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hxy : ∀ s : ℝ, 0 < s →
      0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) :
    ContinuousOn f (Set.Icc (-1) 1) := by
  have _ := hf_cont
  refine hf_conc.continuousOn_Icc (by norm_num : (-1 : ℝ) < 1) ?_ ?_
  · exact continuousWithinAt_left_of_moment hτ hτsmall hh_supp hf_supp hf_conc hf_left hf_right hf_pos hxy
  · exact continuousWithinAt_right_of_moment hτ hτsmall hh_supp hf_supp hf_conc hf_left hf_right hf_pos hxy

end Commons.Geometry.Ulam