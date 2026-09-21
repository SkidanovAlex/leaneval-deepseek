import Mathlib
import Submission.Commons.Geometry.Ulam.moment_h_bounds_smooth

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped ContDiff Pointwise BigOperators

set_option autoImplicit false

private lemma cap_volume_deriv_integral_eq_zero_of_roots_inside_smooth {n : ℕ} (hn : 2 ≤ n)
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1)
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)
        else 0) = 0 := by
  intro s hs
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  rcases hxy_inside s hs with ⟨ha_mem, hb_mem⟩
  let a : ℝ := -x s
  let b : ℝ := y s
  have ha_neg : a < 0 := by dsimp [a]; linarith
  have hb_pos : 0 < b := by dsimp [b]; exact hypos
  have hfa_sq : f a ^ 2 = (s * a + h s) ^ 2 := by simpa [a] using hfx_sq
  have hfb_sq : f b ^ 2 = (s * b + h s) ^ 2 := by simpa [b] using hfy_sq
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    even_profile_nonneg_Icc hf_conc hf_left hf_right
  have hactive := active_nonneg_outside_of_roots_inside (s := s) (h := h s) (a := a) (b := b)
    hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1)
  let C : ℝ := deriv h s
  let F : ℝ → ℝ := fun t => if -f t < L t ∧ L t < f t then W t * (t + C) else 0
  let G : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then W t * (t + C) else 0
  have hn1 : 0 < n - 1 := by omega
  have hW_a : W a = 0 := by
    dsimp [W, L]
    have hbase : f a ^ 2 - (s * a + h s) ^ 2 = 0 := by rw [hfa_sq]; ring
    rw [hbase]
    simp [hn1.ne']
  have hW_b : W b = 0 := by
    dsimp [W, L]
    have hbase : f b ^ 2 - (s * b + h s) ^ 2 = 0 := by rw [hfb_sq]; ring
    rw [hbase]
    simp [hn1.ne']
  have hFG : Set.EqOn F G (Set.Icc (-1 : ℝ) 1) := by
    intro t ht
    by_cases htab : a ≤ t ∧ t ≤ b
    · have hnonneg := hactive.2 t htab
      have hg_nonneg : 0 ≤ f t - L t := by simpa [L] using hnonneg.1
      have hq_nonneg : 0 ≤ f t + L t := by simpa [L] using hnonneg.2
      have hW_zero_of_not : ¬ (-f t < L t ∧ L t < f t) → W t = 0 := by
        intro hnot
        have hg_pos_or : ¬ 0 < f t - L t ∨ ¬ 0 < f t + L t := by
          by_contra hboth
          have hboth' : 0 < f t - L t ∧ 0 < f t + L t := by
            simpa [not_or, not_lt] using hboth
          apply hnot
          constructor <;> dsimp [L] at * <;> linarith
        rcases hg_pos_or with hg_not | hq_not
        · have hg0 : f t - L t = 0 := le_antisymm (le_of_not_gt hg_not) hg_nonneg
          have hbase : f t ^ 2 - (L t) ^ 2 = 0 := by
            have hprod : (f t - L t) * (f t + L t) = 0 := by rw [hg0]; ring
            nlinarith [hprod]
          dsimp [W]
          rw [hbase]
          simp [hn1.ne']
        · have hq0 : f t + L t = 0 := le_antisymm (le_of_not_gt hq_not) hq_nonneg
          have hbase : f t ^ 2 - (L t) ^ 2 = 0 := by
            have hprod : (f t - L t) * (f t + L t) = 0 := by rw [hq0]; ring
            nlinarith [hprod]
          dsimp [W]
          rw [hbase]
          simp [hn1.ne']
      dsimp [F, G]
      rw [if_pos htab]
      by_cases hact : -f t < L t ∧ L t < f t
      · rw [if_pos hact]
      · rw [if_neg hact, hW_zero_of_not hact]
        simp
    · have hact_false : ¬ (-f t < L t ∧ L t < f t) := by
        intro hact
        exact htab (hactive.1 t ht hact)
      dsimp [F, G]
      rw [if_neg htab, if_neg hact_false]
  have hF_eq_G : (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hFG
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
          simp [G, hW_a]
        exact (ht hG0).elim
      have hta_lt : a < t := lt_of_le_of_ne htab.1 (Ne.symm hta_ne)
      exact ⟨hta_lt, htab.2⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := -1) (b := 1) hsuppG_m1
  have hIab := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_ab
  have hab : a < b := lt_trans ha_neg hb_pos
  have hG_ab_eq : (∫ t in a..b, G t) = ∫ t in a..b, W t * (t + C) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htab : a ≤ t ∧ t ≤ b := by
      rw [Set.uIcc_of_le hab.le] at ht
      exact ht
    dsimp [G]
    rw [if_pos htab]
  have hJ' : (∫ t in a..b, W t * (t + C)) = 0 := by
    have hJ0 := hJ s hs
    simpa [a,b,W,L,C] using hJ0
  have hmain : (∫ t in (-1 : ℝ)..1, F t) = 0 := by
    calc
      (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := hF_eq_G
      _ = ∫ t, G t := hI1
      _ = ∫ t in a..b, G t := hIab.symm
      _ = ∫ t in a..b, W t * (t + C) := hG_ab_eq
      _ = 0 := hJ'
  simpa [F, L] using hmain


lemma cap_volume_deriv_integral_eq_zero_smooth {n : ℕ} (hn : 2 ≤ n)
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
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)
        else 0) = 0 := by
  intro s hs
  have hb := moment_h_bounds_smooth hn hf_support hf_cont hf_conc hf_left hf_right hf_pos
    hh_cont h0 hxy hJ s hs
  have hinside := roots_inside_of_abs_h_lt_s hf_support hf_left hf_right hxy hs hb.1 hb.2
  exact cap_volume_deriv_integral_eq_zero_of_roots_inside_smooth hn hf_support hf_conc hf_left
    hf_right hf_pos hxy (fun u hu => by
      have hbu := moment_h_bounds_smooth hn hf_support hf_cont hf_conc hf_left hf_right hf_pos
        hh_cont h0 hxy hJ u hu
      exact roots_inside_of_abs_h_lt_s hf_support hf_left hf_right hxy hu hbu.1 hbu.2) hJ s hs

end Commons.Geometry.Ulam
