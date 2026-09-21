import Mathlib
import Submission.Commons.Geometry.Ulam.cap_pow_integral_hasDerivAt_smooth
import Submission.Commons.Geometry.Ulam.cap_volume_deriv_integral_eq_zero_smooth
import Submission.Commons.Geometry.Ulam.moment_h_bounds_smooth
import Submission.Commons.Geometry.Ulam.moment_h_bounds
import Submission.Commons.Geometry.Ulam.even_profile_cap_volume_half
import Submission.Commons.Geometry.Ulam.cap_centroid_moment_hasDerivAt_smooth

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

private lemma integral_eq_integral_of_support_subset_two {G : ℝ → ℝ} {a b c d : ℝ}
    (hG1 : Function.support G ⊆ Set.Ioc c d) (hG2 : Function.support G ⊆ Set.Ioc a b) :
    (∫ t in c..d, G t) = ∫ t in a..b, G t := by
  have h1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := c) (b := d) hG1
  have h2 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hG2
  exact h1.trans h2.symm

private lemma pow_clamp_integral_eq_interval_of_active {n : ℕ} {f : ℝ → ℝ} {s h a b : ℝ}
    (hn : 2 ≤ n) (hs : 0 < s)
    (ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1) (hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hfa_sq : f a ^ 2 = (s * a + h) ^ 2)
    (hfb_sq : f b ^ 2 = (s * b + h) ^ 2) :
    (∫ t in (-1 : ℝ)..1, (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2) ^ n) =
      ∫ t in a..b, (f t ^ 2 - (s * t + h) ^ 2) ^ n := by
  let L : ℝ → ℝ := fun t => s * t + h
  let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (L t))
  let F : ℝ → ℝ := fun t => (f t ^ 2 - (U t) ^ 2) ^ n
  let G : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then (f t ^ 2 - (L t) ^ 2) ^ n else 0
  have hactive := active_nonneg_outside_of_roots_inside (f := f) (s := s) (h := h) (a := a) (b := b)
    hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hFG : Set.EqOn F G (Set.Icc (-1 : ℝ) 1) := by
    intro t ht
    dsimp [F, G, U, L]
    by_cases htab : a ≤ t ∧ t ≤ b
    · have hnonneg := hactive.2 t htab
      have hL_lower : -f t ≤ s * t + h := by linarith
      have hL_upper : s * t + h ≤ f t := by linarith
      have hU : max (-f t) (min (f t) (s * t + h)) = s * t + h := by
        rw [min_eq_right hL_upper, max_eq_right hL_lower]
      rw [if_pos htab, hU]
    · have hact_false : ¬ (-f t < s * t + h ∧ s * t + h < f t) := by
        intro hact
        exact htab (hactive.1 t ht hact)
      have hU_zero : f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2 = 0 := by
        have hle_or : s * t + h ≤ -f t ∨ f t ≤ s * t + h := by
          by_contra hboth
          have hnot := not_or.mp hboth
          have hlt_lower : -f t < s * t + h := lt_of_not_ge hnot.1
          have hlt_upper : s * t + h < f t := lt_of_not_ge hnot.2
          exact hact_false ⟨hlt_lower, hlt_upper⟩
        rcases hle_or with hL_low | hL_high
        · have hmin : min (f t) (s * t + h) = s * t + h := by
            rw [min_eq_right (le_trans hL_low (by linarith [hf_nonneg t ht]))]
          have hU : max (-f t) (min (f t) (s * t + h)) = -f t := by
            rw [hmin]
            exact max_eq_left hL_low
          rw [hU]
          ring
        · have hmin : min (f t) (s * t + h) = f t := by
            rw [min_eq_left hL_high]
          have hU : max (-f t) (min (f t) (s * t + h)) = f t := by
            rw [hmin]
            exact max_eq_right (by linarith [hf_nonneg t ht])
          rw [hU]
          ring
      have hF0 : (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2) ^ n = 0 := by
        rw [hU_zero]
        simp [zero_pow (by omega : n ≠ 0)]
      rw [if_neg htab, hF0]
  have hF_eq_G : (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hFG
  have hab : a < b := lt_trans ha_neg hb_pos
  have hG_a : G a = 0 := by
    have htab : a ≤ a ∧ a ≤ b := ⟨le_rfl, hab.le⟩
    have hbase : f a ^ 2 - (s * a + h) ^ 2 = 0 := by rw [hfa_sq]; ring
    dsimp [G, L]
    rw [if_pos htab, hbase]
    simp [zero_pow (by omega : n ≠ 0)]
  have hG_b : G b = 0 := by
    have htab : a ≤ b ∧ b ≤ b := ⟨hab.le, le_rfl⟩
    have hbase : f b ^ 2 - (s * b + h) ^ 2 = 0 := by rw [hfb_sq]; ring
    dsimp [G, L]
    rw [if_pos htab, hbase]
    simp [zero_pow (by omega : n ≠ 0)]
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
          exact hG_a
        exact (ht hG0).elim
      have hta_lt : a < t := lt_of_le_of_ne htab.1 (Ne.symm hta_ne)
      exact ⟨hta_lt, htab.2⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := -1) (b := 1) hsuppG_m1
  have hIab := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_ab
  have hG_ab_eq : (∫ t in a..b, G t) = ∫ t in a..b, (f t ^ 2 - (s * t + h) ^ 2) ^ n := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htab : a ≤ t ∧ t ≤ b := by
      simpa [Set.uIcc_of_le hab.le] using ht
    dsimp [G, L]
    rw [if_pos htab]
  calc
    (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := hF_eq_G
    _ = ∫ t, G t := hI1
    _ = ∫ t in a..b, G t := hIab.symm
    _ = ∫ t in a..b, (f t ^ 2 - (s * t + h) ^ 2) ^ n := hG_ab_eq

private lemma deriv_clamp_integral_eq_interval_of_active {n : ℕ} {f : ℝ → ℝ} {s h a b C : ℝ}
    (hn : 2 ≤ n) (hs : 0 < s)
    (ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1) (hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hfa_sq : f a ^ 2 = (s * a + h) ^ 2)
    (hfb_sq : f b ^ 2 = (s * b + h) ^ 2) :
    (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h ∧ s * t + h < f t then
          -(2 * (n : ℝ)) * (s * t + h) *
            (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1) * (t + C)
        else 0) =
      ∫ t in a..b,
        -(2 * (n : ℝ)) * (s * t + h) *
          (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1) * (t + C) := by
  let L : ℝ → ℝ := fun t => s * t + h
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1)
  let F : ℝ → ℝ := fun t => if -f t < L t ∧ L t < f t then -(2 * (n : ℝ)) * L t * W t * (t + C) else 0
  let G : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then -(2 * (n : ℝ)) * L t * W t * (t + C) else 0
  have hactive := active_nonneg_outside_of_roots_inside (f := f) (s := s) (h := h) (a := a) (b := b)
    hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hab : a < b := lt_trans ha_neg hb_pos
  have hW_a : W a = 0 := by
    dsimp [W, L]
    have hbase : f a ^ 2 - (s * a + h) ^ 2 = 0 := by rw [hfa_sq]; ring
    rw [hbase]
    simp [zero_pow (by omega : n - 1 ≠ 0)]
  have hW_b : W b = 0 := by
    dsimp [W, L]
    have hbase : f b ^ 2 - (s * b + h) ^ 2 = 0 := by rw [hfb_sq]; ring
    rw [hbase]
    simp [zero_pow (by omega : n - 1 ≠ 0)]
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
          simp [zero_pow (by omega : n - 1 ≠ 0)]
        · have hq0 : f t + L t = 0 := le_antisymm (le_of_not_gt hq_not) hq_nonneg
          have hbase : f t ^ 2 - (L t) ^ 2 = 0 := by
            have hprod : (f t - L t) * (f t + L t) = 0 := by rw [hq0]; ring
            nlinarith [hprod]
          dsimp [W]
          rw [hbase]
          simp [zero_pow (by omega : n - 1 ≠ 0)]
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
  have hG_a : G a = 0 := by
    have htab : a ≤ a ∧ a ≤ b := ⟨le_rfl, hab.le⟩
    dsimp [G, L]
    rw [if_pos htab, hW_a]
    ring
  have hG_b : G b = 0 := by
    have htab : a ≤ b ∧ b ≤ b := ⟨hab.le, le_rfl⟩
    dsimp [G, L]
    rw [if_pos htab, hW_b]
    ring
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
          exact hG_a
        exact (ht hG0).elim
      have hta_lt : a < t := lt_of_le_of_ne htab.1 (Ne.symm hta_ne)
      exact ⟨hta_lt, htab.2⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := -1) (b := 1) hsuppG_m1
  have hIab := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_ab
  have hG_ab_eq : (∫ t in a..b, G t) = ∫ t in a..b, -(2 * (n : ℝ)) * L t * W t * (t + C) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htab : a ≤ t ∧ t ≤ b := by
      simpa [Set.uIcc_of_le hab.le] using ht
    dsimp [G]
    rw [if_pos htab]
  calc
    (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := hF_eq_G
    _ = ∫ t, G t := hI1
    _ = ∫ t in a..b, G t := hIab.symm
    _ = ∫ t in a..b, -(2 * (n : ℝ)) * L t * W t * (t + C) := hG_ab_eq

private lemma centroid_target_integral_eq_interval_of_active {n : ℕ} {f : ℝ → ℝ} {s h a b C : ℝ}
    (hn : 2 ≤ n) (hs : 0 < s)
    (ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1) (hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hfa_sq : f a ^ 2 = (s * a + h) ^ 2)
    (hfb_sq : f b ^ 2 = (s * b + h) ^ 2) :
    (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h ∧ s * t + h < f t then
          (t + s * (s * t + h)) * (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1) *
            (t + C) -
          (f t ^ 2 - (s * t + h) ^ 2) ^ n / (2 * (n : ℝ))
        else 0) =
      ∫ t in a..b,
        (t + s * (s * t + h)) * (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1) *
          (t + C) -
        (f t ^ 2 - (s * t + h) ^ 2) ^ n / (2 * (n : ℝ)) := by
  let L : ℝ → ℝ := fun t => s * t + h
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1)
  let E : ℝ → ℝ := fun t => (t + s * L t) * W t * (t + C) - (f t ^ 2 - (L t) ^ 2) ^ n / (2 * (n : ℝ))
  let F : ℝ → ℝ := fun t => if -f t < L t ∧ L t < f t then E t else 0
  let G : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then E t else 0
  have hactive := active_nonneg_outside_of_roots_inside (f := f) (s := s) (h := h) (a := a) (b := b)
    hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hab : a < b := lt_trans ha_neg hb_pos
  have hn1 : n - 1 ≠ 0 := by omega
  have hW_a : W a = 0 := by
    dsimp [W, L]
    have hbase : f a ^ 2 - (s * a + h) ^ 2 = 0 := by rw [hfa_sq]; ring
    rw [hbase]
    simp [zero_pow hn1]
  have hW_b : W b = 0 := by
    dsimp [W, L]
    have hbase : f b ^ 2 - (s * b + h) ^ 2 = 0 := by rw [hfb_sq]; ring
    rw [hbase]
    simp [zero_pow hn1]
  have hq_a : (f a ^ 2 - (s * a + h) ^ 2) ^ n = 0 := by
    have hbase : f a ^ 2 - (s * a + h) ^ 2 = 0 := by rw [hfa_sq]; ring
    rw [hbase]
    simp [zero_pow (by omega : n ≠ 0)]
  have hq_b : (f b ^ 2 - (s * b + h) ^ 2) ^ n = 0 := by
    have hbase : f b ^ 2 - (s * b + h) ^ 2 = 0 := by rw [hfb_sq]; ring
    rw [hbase]
    simp [zero_pow (by omega : n ≠ 0)]
  have hE_a : E a = 0 := by
    dsimp [E, L]
    rw [hW_a, hq_a]
    ring
  have hE_b : E b = 0 := by
    dsimp [E, L]
    rw [hW_b, hq_b]
    ring
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
          simp [zero_pow hn1]
        · have hq0 : f t + L t = 0 := le_antisymm (le_of_not_gt hq_not) hq_nonneg
          have hbase : f t ^ 2 - (L t) ^ 2 = 0 := by
            have hprod : (f t - L t) * (f t + L t) = 0 := by rw [hq0]; ring
            nlinarith [hprod]
          dsimp [W]
          rw [hbase]
          simp [zero_pow hn1]
      have hq_zero_of_not : ¬ (-f t < L t ∧ L t < f t) → (f t ^ 2 - (L t) ^ 2) ^ n = 0 := by
        intro hnot
        have hW0 : (f t ^ 2 - (L t) ^ 2) ^ (n - 1) = 0 := hW_zero_of_not hnot
        have hbase : f t ^ 2 - (L t) ^ 2 = 0 := by
          exact (pow_eq_zero_iff hn1).mp hW0
        rw [hbase]
        simp [zero_pow (by omega : n ≠ 0)]
      dsimp [F, G]
      rw [if_pos htab]
      by_cases hact : -f t < L t ∧ L t < f t
      · rw [if_pos hact]
      · rw [if_neg hact]
        dsimp [E]
        rw [hW_zero_of_not hact, hq_zero_of_not hact]
        ring
    · have hact_false : ¬ (-f t < L t ∧ L t < f t) := by
        intro hact
        exact htab (hactive.1 t ht hact)
      dsimp [F, G]
      rw [if_neg htab, if_neg hact_false]
  have hF_eq_G : (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hFG
  have hG_a : G a = 0 := by
    have htab : a ≤ a ∧ a ≤ b := ⟨le_rfl, hab.le⟩
    dsimp [G]
    rw [if_pos htab]
    exact hE_a
  have hG_b : G b = 0 := by
    have htab : a ≤ b ∧ b ≤ b := ⟨hab.le, le_rfl⟩
    dsimp [G]
    rw [if_pos htab]
    exact hE_b
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
          exact hG_a
        exact (ht hG0).elim
      have hta_lt : a < t := lt_of_le_of_ne htab.1 (Ne.symm hta_ne)
      exact ⟨hta_lt, htab.2⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := -1) (b := 1) hsuppG_m1
  have hIab := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_ab
  have hG_ab_eq : (∫ t in a..b, G t) = ∫ t in a..b, E t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htab : a ≤ t ∧ t ≤ b := by
      simpa [Set.uIcc_of_le hab.le] using ht
    dsimp [G]
    rw [if_pos htab]
  calc
    (∫ t in (-1 : ℝ)..1, F t) = ∫ t in (-1 : ℝ)..1, G t := hF_eq_G
    _ = ∫ t, G t := hI1
    _ = ∫ t in a..b, G t := hIab.symm
    _ = ∫ t in a..b, E t := hG_ab_eq


private lemma ball_moment_integral_eq_const_div_sqrt {n : ℕ} (s : ℝ) :
    (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        ((1 - t ^ 2) - (s * t) ^ 2) ^ n) =
      (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n) / Real.sqrt (1 + s ^ 2) := by
  let c : ℝ := Real.sqrt (1 + s ^ 2)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg s])
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have h_integrand : ∀ t, ((1 - t ^ 2) - (s * t) ^ 2) ^ n = (1 - (c * t) ^ 2) ^ n := by
    intro t
    have hc_sq : c ^ 2 = 1 + s ^ 2 := by
      dsimp [c]
      rw [Real.sq_sqrt (by nlinarith [sq_nonneg s])]
    have hbase : (1 - t ^ 2 - (s * t) ^ 2) = 1 - (c * t) ^ 2 := by
      calc
        (1 - t ^ 2 - (s * t) ^ 2) = 1 - (1 + s ^ 2) * t ^ 2 := by ring
        _ = 1 - c ^ 2 * t ^ 2 := by rw [← hc_sq]
        _ = 1 - (c * t) ^ 2 := by ring
    exact congrArg (fun z : ℝ => z ^ n) hbase
  calc
    (∫ t in (-(1 / c))..(1 / c), ((1 - t ^ 2) - (s * t) ^ 2) ^ n)
        = ∫ t in (-(1 / c))..(1 / c), (1 - (c * t) ^ 2) ^ n := by
            apply intervalIntegral.integral_congr
            intro t ht
            exact h_integrand t
    _ = c⁻¹ • ∫ u in c * (-(1 / c))..c * (1 / c), (1 - u ^ 2) ^ n := by
            exact intervalIntegral.integral_comp_mul_left (f := fun u : ℝ => (1 - u ^ 2) ^ n) (c := c) (a := -(1 / c)) (b := 1 / c) hc_ne
    _ = c⁻¹ • ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n := by
            have h1 : c * (-(1 / c)) = -1 := by field_simp [hc_ne]
            have h2 : c * (1 / c) = 1 := by field_simp [hc_ne]
            have h1' : c * (-c⁻¹) = -1 := by field_simp [hc_ne]
            have h2' : c * c⁻¹ = 1 := by field_simp [hc_ne]
            simp [h1', h2']
    _ = c⁻¹ * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n := by
            rw [smul_eq_mul]
    _ = (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n) / c := by
            ring

private lemma ball_moment_integral_hasDerivAt_local {n : ℕ} (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in (-(1 / Real.sqrt (1 + r ^ 2)))..(1 / Real.sqrt (1 + r ^ 2)),
          ((1 - t ^ 2) - (r * t) ^ 2) ^ n)
      (-(s / (1 + s ^ 2)) *
        ∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n) s := by
  let J : ℝ := ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n
  let c : ℝ → ℝ := fun r => Real.sqrt (1 + r ^ 2)
  have hfun : (fun r : ℝ => ∫ t in (-(1 / c r))..(1 / c r), ((1 - t ^ 2) - (r * t) ^ 2) ^ n) = fun r => J / c r := by
    funext r
    dsimp [c, J]
    simpa [c] using ball_moment_integral_eq_const_div_sqrt (s := r)
  have hc_deriv : HasDerivAt c (s / c s) s := by
    dsimp [c]
    have hinner : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * s) s := by
      have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (0 + 2 * s) s := by
        have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 s := hasDerivAt_const s 1
        have hp : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
          simpa using (hasDerivAt_pow 2 (s : ℝ))
        exact hc.add hp
      simpa using h1
    have hsqrt : HasDerivAt (fun r : ℝ => Real.sqrt (1 + r ^ 2)) ((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) s := by
      have hpos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
      have hne : 1 + s ^ 2 ≠ 0 := ne_of_gt hpos
      have hs := hinner.sqrt hne
      simpa using hs
    have hderiv_simpl : (2 * s) / (2 * Real.sqrt (1 + s ^ 2)) = s / c s := by
      dsimp [c]
      ring
    exact hsqrt.congr_deriv hderiv_simpl
  have hc_ne : c s ≠ 0 := by
    dsimp [c]
    exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [sq_nonneg s]))
  have hdiv : HasDerivAt (fun r : ℝ => J / c r)
      (((0 : ℝ) * c s - J * (s / c s)) / (c s) ^ 2) s := by
    have hconst : HasDerivAt (fun _ : ℝ => J) 0 s := hasDerivAt_const s J
    exact hconst.div hc_deriv hc_ne
  have hdiv_simpl : ((0 : ℝ) * c s - J * (s / c s)) / (c s) ^ 2 =
      - (s / (1 + s ^ 2)) * (J / c s) := by
    dsimp [c]
    have hcsq : (Real.sqrt (1 + s ^ 2)) ^ 2 = 1 + s ^ 2 := by
      rw [Real.sq_sqrt (by nlinarith [sq_nonneg s])]
    field_simp [hc_ne]
    rw [hcsq]
    ring
  have hdiv' : HasDerivAt (fun r : ℝ => J / c r)
      (- (s / (1 + s ^ 2)) * (J / c s)) s := hdiv.congr_deriv hdiv_simpl
  rw [← hfun] at hdiv'
  have hval : J / c s = ∫ t in (-(1 / c s))..(1 / c s), ((1 - t ^ 2) - (s * t) ^ 2) ^ n := by
    dsimp [c]
    exact (ball_moment_integral_eq_const_div_sqrt (s := s)).symm
  simpa [c, hval] using hdiv'


lemma cap_centroid_moment_deriv_eq_zero_smooth {n : ℕ} (hn : 2 ≤ n)
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ (WithTop.some (⊤ : ℕ∞)) f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ (WithTop.some (⊤ : ℕ∞)) h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hI : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
        (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n))
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            (t + deriv h s) -
          (f t ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ))
        else 0) = 0 := by
  intro s hs
  have hb := moment_h_bounds_smooth hn hf_support hf_cont hf_conc hf_left hf_right hf_pos
    hh_cont h0 hxy hJ s hs
  have hinside := roots_inside_of_abs_h_lt_s hf_support hf_left hf_right hxy hs hb.1 hb.2
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  let a : ℝ := -x s
  let b : ℝ := y s
  have ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [a] using hinside.1
  have hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [b] using hinside.2
  have ha_neg : a < 0 := by dsimp [a]; linarith
  have hb_pos : 0 < b := by dsimp [b]; exact hypos
  have hfa_sq : f a ^ 2 = (s * a + h s) ^ 2 := by simpa [a] using hfx_sq
  have hfb_sq : f b ^ 2 = (s * b + h s) ^ 2 := by simpa [b] using hfy_sq
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    even_profile_nonneg_Icc hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    even_profile_measurable_smooth hf_support hf_cont hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) :=
    even_profile_bounded hf_conc hf_left hf_right
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1)
  let C : ℝ := deriv h s
  let Rfun : ℝ → ℝ := fun r : ℝ =>
    ∫ t in (-(1 / Real.sqrt (1 + r ^ 2)))..(1 / Real.sqrt (1 + r ^ 2)),
      ((1 - t ^ 2) - (r * t) ^ 2) ^ n
  let Qfun : ℝ → ℝ := fun r : ℝ =>
    ∫ t in (-1 : ℝ)..1, (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2) ^ n
  have hQ_eq_interval : Qfun s = ∫ t in a..b, (f t ^ 2 - (L t) ^ 2) ^ n := by
    dsimp [Qfun, L, a, b]
    exact pow_clamp_integral_eq_interval_of_active (n := n) (f := f) (s := s) (h := h s)
      (a := a) (b := b) hn hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hQ_deriv := cap_pow_integral_hasDerivAt_smooth (n := n) (f := f) (h := h) (a := -1) (b := 1)
    hn (by norm_num) hf_nonneg hf_meas hf_bdd hh_cont s
  have hD_eq_interval : (∫ t in (-1 : ℝ)..1,
        if -f t < L t ∧ L t < f t then
          -(2 * (n : ℝ)) * L t * (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * (t + C)
        else 0) =
      ∫ t in a..b, -(2 * (n : ℝ)) * L t * (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * (t + C) := by
    dsimp [L, C, a, b]
    exact deriv_clamp_integral_eq_interval_of_active (n := n) (f := f) (s := s) (h := h s)
      (a := a) (b := b) (C := deriv h s) hn hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hR_deriv := ball_moment_integral_hasDerivAt_local (n := n) s
  have hfun_eq_on : ∀ᶠ r in 𝓝 s, Qfun r = Rfun r := by
    have hpos_ev : ∀ᶠ r in 𝓝 s, 0 < r := by
      exact (isOpen_Ioi.mem_nhds hs)
    filter_upwards [hpos_ev] with r hr
    dsimp [Qfun, Rfun]
    have hb_r := moment_h_bounds_smooth hn hf_support hf_cont hf_conc hf_left hf_right hf_pos
      hh_cont h0 hxy hJ r hr
    have hinside_r := roots_inside_of_abs_h_lt_s hf_support hf_left hf_right hxy hr hb_r.1 hb_r.2
    rcases hxy r hr with ⟨hxr, hyr, hfy_r, hfx_r⟩
    let ar : ℝ := -x r
    let br : ℝ := y r
    have har_mem : ar ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [ar] using hinside_r.1
    have hbr_mem : br ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [br] using hinside_r.2
    have har_neg : ar < 0 := by dsimp [ar]; linarith
    have hbr_pos : 0 < br := by dsimp [br]; exact hyr
    have hfar_sq : f ar ^ 2 = (r * ar + h r) ^ 2 := by simpa [ar] using hfx_r
    have hfbr_sq : f br ^ 2 = (r * br + h r) ^ 2 := by simpa [br] using hfy_r
    have hpow_eq := pow_clamp_integral_eq_interval_of_active (n := n) (f := f) (s := r) (h := h r)
      (a := ar) (b := br) hn hr har_mem hbr_mem har_neg hbr_pos hf_conc hf_nonneg hf_pos hfar_sq hfbr_sq
    have hI_r := hI r hr
    calc
      (∫ t in (-1 : ℝ)..1, (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2) ^ n)
          = ∫ t in ar..br, (f t ^ 2 - (r * t + h r) ^ 2) ^ n := hpow_eq
      _ = (∫ t in (-(1 / Real.sqrt (1 + r ^ 2)))..(1 / Real.sqrt (1 + r ^ 2)),
            ((1 - t ^ 2) - (r * t) ^ 2) ^ n) := hI_r
  have hfun_eq_on' : Qfun =ᶠ[𝓝 s] Rfun := by
    exact hfun_eq_on
  have hQ_deriv' : HasDerivAt Qfun (-(s / (1 + s ^ 2)) * Rfun s) s := by
    exact hR_deriv.congr_of_eventuallyEq hfun_eq_on'
  have hder_eq : (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          -(2 * (n : ℝ)) * (s * t + h s) *
            (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)
        else 0) =
      -(s / (1 + s ^ 2)) * Rfun s := by
    have huniq := hQ_deriv.unique hQ_deriv'
    simpa [Qfun, L, C] using huniq
  have hD_interval : (∫ t in a..b, -(2 * (n : ℝ)) * L t * (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * (t + C)) =
      -(s / (1 + s ^ 2)) * Rfun s := by
    calc
      (∫ t in a..b, -(2 * (n : ℝ)) * L t * (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * (t + C))
          = (∫ t in (-1 : ℝ)..1,
              if -f t < L t ∧ L t < f t then
                -(2 * (n : ℝ)) * L t * (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * (t + C)
              else 0) := by
                dsimp [L, C, a, b]
                exact (deriv_clamp_integral_eq_interval_of_active (n := n) (f := f) (s := s) (h := h s)
                  (a := a) (b := b) (C := deriv h s) hn hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq).symm
      _ = -(s / (1 + s ^ 2)) * Rfun s := by
                simpa [L, C] using hder_eq
  have hJ_ab : (∫ t in a..b, W t * (t + C)) = 0 := by
    simpa [W, L, C, a, b] using hJ s hs
  have hT_interval := centroid_target_integral_eq_interval_of_active (n := n) (f := f) (s := s) (h := h s)
    (a := a) (b := b) (C := deriv h s) hn hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hf_cont_ab : ContinuousOn f (Set.Icc a b) := by
    exact hf_cont.continuousOn.mono (by
      intro t ht
      exact ⟨lt_of_lt_of_le ha_mem.1 ht.1, lt_of_le_of_lt ht.2 hb_mem.2⟩)
  have h_cont_ab : ContinuousOn h (Set.Icc a b) := by
    exact hh_cont.continuousOn.mono (by intro t ht; simp)
  have hW_cont : ContinuousOn W (Set.Icc a b) := by
    dsimp [W, L]
    fun_prop
  have hg1_cont : ContinuousOn (fun t : ℝ => t * W t * (t + C)) (Set.Icc a b) := by
    dsimp [W, L]
    fun_prop
  have hg2_cont : ContinuousOn (fun t : ℝ => s * (L t * W t * (t + C))) (Set.Icc a b) := by
    dsimp [W, L]
    fun_prop
  have hg3_cont : ContinuousOn (fun t : ℝ => (f t ^ 2 - (L t) ^ 2) ^ n / (2 * (n : ℝ))) (Set.Icc a b) := by
    dsimp [W, L]
    fun_prop
  have hab_le : a ≤ b := le_of_lt (lt_trans ha_neg hb_pos)
  have hg1_int : IntervalIntegrable (fun t : ℝ => t * W t * (t + C)) volume a b :=
    hg1_cont.intervalIntegrable_of_Icc hab_le
  have hg2_int : IntervalIntegrable (fun t : ℝ => s * (L t * W t * (t + C))) volume a b :=
    hg2_cont.intervalIntegrable_of_Icc hab_le
  have hg3_int : IntervalIntegrable (fun t : ℝ => (f t ^ 2 - (L t) ^ 2) ^ n / (2 * (n : ℝ))) volume a b :=
    hg3_cont.intervalIntegrable_of_Icc hab_le
  have hWmul_cont : ContinuousOn (fun t : ℝ => W t * (t + C)) (Set.Icc a b) := by
    dsimp [W, L]
    fun_prop
  have hLmul_cont : ContinuousOn (fun t : ℝ => L t * W t * (t + C)) (Set.Icc a b) := by
    dsimp [W, L]
    fun_prop
  have hW_int : IntervalIntegrable (fun t : ℝ => W t * (t + C)) volume a b :=
    hWmul_cont.intervalIntegrable_of_Icc hab_le
  have hL_int : IntervalIntegrable (fun t : ℝ => L t * W t * (t + C)) volume a b :=
    hLmul_cont.intervalIntegrable_of_Icc hab_le
  let ItLs : ℝ := ∫ t in a..b, t * W t * (t + C)
  let ILs : ℝ := ∫ t in a..b, W t * (t + C)
  have hILs : ILs = 0 := by
    simpa [ILs] using hJ_ab
  let ILLs : ℝ := ∫ t in a..b, L t * W t * (t + C)
  let IQ : ℝ := ∫ t in a..b, (f t ^ 2 - (L t) ^ 2) ^ n
  have hE_decomp : (∫ t in a..b,
        (t + s * L t) * W t * (t + C) - (f t ^ 2 - (L t) ^ 2) ^ n / (2 * (n : ℝ))) =
      ItLs + s * ILLs - IQ / (2 * (n : ℝ)) := by
    calc
      (∫ t in a..b, (t + s * L t) * W t * (t + C) - (f t ^ 2 - (L t) ^ 2) ^ n / (2 * (n : ℝ)))
          = ∫ t in a..b, (t * W t * (t + C) + s * (L t * W t * (t + C)) -
              (f t ^ 2 - (L t) ^ 2) ^ n / (2 * (n : ℝ))) := by
              apply intervalIntegral.integral_congr
              intro t ht
              ring
      _ = (∫ t in a..b, (t * W t * (t + C) + s * (L t * W t * (t + C)))) -
            ∫ t in a..b, ((f t ^ 2 - (L t) ^ 2) ^ n / (2 * (n : ℝ))) := by
              rw [intervalIntegral.integral_sub]
              · exact hg1_int.add hg2_int
              · exact hg3_int
      _ = ItLs + s * ILLs - IQ / (2 * (n : ℝ)) := by
              rw [intervalIntegral.integral_add hg1_int hg2_int]
              simp [ItLs, ILLs, IQ, intervalIntegral.integral_const_mul]
  have hILLs_decomp : ILLs = s * ItLs + h s * ILs := by
    calc
      ILLs = ∫ t in a..b, (s * (t * W t * (t + C)) + h s * (W t * (t + C))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp [ILLs, L]
        ring
      _ = (∫ t in a..b, s * (t * W t * (t + C))) + ∫ t in a..b, h s * (W t * (t + C)) := by
        rw [intervalIntegral.integral_add]
        · exact hg1_int.const_mul s
        · exact hW_int.const_mul (h s)
      _ = s * ItLs + h s * ILs := by
        simp [ItLs, ILs, intervalIntegral.integral_const_mul]
  have hQ_interval_R : IQ = Rfun s := by
    dsimp [IQ, L]
    exact hI s hs
  have hLLs_from_D : s * ILLs =
      (s / (2 * (n : ℝ))) * (s / (1 + s ^ 2)) * Rfun s := by
    have hconst := intervalIntegral.integral_const_mul (μ := volume) (r := -(2 * (n : ℝ))) (f := fun t : ℝ => L t * W t * (t + C)) (a := a) (b := b)
    have hD_interval_cast : (∫ t in a..b, -(2 * (n : ℝ)) * (L t * W t * (t + C))) =
        ∫ t in a..b, -(2 * (n : ℝ)) * L t * (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * (t + C) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [W]
      ring
    have hD_interval_cast' : (∫ t in a..b, -(2 * (n : ℝ)) * (L t * W t * (t + C))) =
        -(s / (1 + s ^ 2)) * Rfun s := by
      rw [hD_interval_cast, hD_interval]
    rw [hconst] at hD_interval_cast'
    change -(2 * (n : ℝ)) * ILLs = -(s / (1 + s ^ 2)) * Rfun s at hD_interval_cast'
    have hden : (2 * (n : ℝ)) ≠ 0 := by positivity
    have hs_ne : s ≠ 0 := ne_of_gt hs
    field_simp [hden, hs_ne] at hD_interval_cast' ⊢
    nlinarith
  have hItLs : ItLs = ILLs / s := by
    have hs_ne : s ≠ 0 := ne_of_gt hs
    have hdecomp := hILLs_decomp
    rw [hILs] at hdecomp
    simp at hdecomp
    field_simp [hs_ne] at hdecomp ⊢
    exact hdecomp.symm
  have hden : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hc : 1 + s ^ 2 ≠ 0 := by nlinarith [sq_nonneg s]
  have hILLs_val : ILLs = (s * Rfun s) / (2 * (n : ℝ) * (1 + s ^ 2)) := by
    have h := hLLs_from_D
    field_simp [hs_ne, hden, hc] at h ⊢
    nlinarith
  have hItLs_val : ItLs = Rfun s / (2 * (n : ℝ) * (1 + s ^ 2)) := by
    rw [hItLs, hILLs_val]
    field_simp [hs_ne, hden, hc]
  have hT_eq : (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            (t + deriv h s) -
          (f t ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ))
        else 0) = 0 := by
    calc
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            (t + deriv h s) -
          (f t ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ))
        else 0)
          = ItLs + s * ILLs - IQ / (2 * (n : ℝ)) := by
              rw [hT_interval, hE_decomp]
      _ = Rfun s / (2 * (n : ℝ) * (1 + s ^ 2)) +
            s * ((s * Rfun s) / (2 * (n : ℝ) * (1 + s ^ 2))) - Rfun s / (2 * (n : ℝ)) := by
              rw [hItLs_val, hILLs_val, hQ_interval_R]
      _ = 0 := by
              field_simp [hs_ne, hden, hc]
              ring
  exact hT_eq


private lemma cap_centroid_moment_at_zero {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t) :
    (∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..0, t * (f t ^ 2 - z ^ 2) ^ (n - 1)) =
      (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(f t), t * (f t ^ 2 - z ^ 2) ^ (n - 1) := by
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  have hinner : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      (∫ z in (-f t)..0, t * W t z) =
        (1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z := by
    intro t ht
    have hft_nonneg : 0 ≤ f t := hf_nonneg t ht
    have hg_cont : Continuous (fun z : ℝ => W t z) := by
      dsimp [W]
      continuity
    have hg_even : ∀ z : ℝ, W t (-z) = W t z := by
      intro z
      dsimp [W]
      ring
    have hhalf := (intervalIntegral_half_even hft_nonneg hg_cont hg_even).2
    calc
      (∫ z in (-f t)..0, t * W t z) = t * ∫ z in (-f t)..0, W t z := by
        rw [intervalIntegral.integral_const_mul]
      _ = t * ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), W t z) := by
        rw [hhalf]
        ring
      _ = (1 / 2 : ℝ) * (t * ∫ z in (-f t)..(f t), W t z) := by ring
      _ = (1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z := by
        rw [intervalIntegral.integral_const_mul]
  have hcongr : (∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..0, t * W t z) =
      ∫ t in (-1 : ℝ)..1, ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    exact hinner t htIcc
  calc
    (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, t * W t z)
        = ∫ t in (-1 : ℝ)..1, ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z) := hcongr
    _ = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), t * W t z := by
        rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), t * (f t ^ 2 - z ^ 2) ^ (n - 1) := by
        simp [W]


lemma even_profile_cap_centroid_moment_eq_smooth {n : ℕ} (hn : 2 ≤ n)
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ (WithTop.some (⊤ : ℕ∞)) f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ (WithTop.some (⊤ : ℕ∞)) h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hI : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
        (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n))
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h s))),
            (t + s * z) * (f t ^ 2 - z ^ 2) ^ (n - 1)) =
        (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(f t), t * (f t ^ 2 - z ^ 2) ^ (n - 1) := by
  classical
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  let A : ℝ → ℝ := fun r =>
    ∫ t in (-1 : ℝ)..1,
      ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))), (t + r * z) * W t z
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    even_profile_nonneg_Icc hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    even_profile_measurable_smooth hf_support hf_cont hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) :=
    even_profile_bounded hf_conc hf_left hf_right
  have hcont : ContinuousOn A (Set.Ici 0) := by
    intro r hr
    exact (cap_centroid_moment_hasDerivAt_smooth (n := n) (f := f) (h := h)
      hn hf_nonneg hf_meas hf_bdd hh_cont r).continuousAt.continuousWithinAt
  have hderiv : ∀ r > 0, HasDerivAt A 0 r := by
    intro r hr
    have hd := cap_centroid_moment_hasDerivAt_smooth (n := n) (f := f) (h := h)
      hn hf_nonneg hf_meas hf_bdd hh_cont r
    have hz := cap_centroid_moment_deriv_eq_zero_smooth hn hf_support hf_cont hf_conc hf_left hf_right
      hf_pos hh_cont h0 hxy hI hJ r hr
    simpa [A, W] using hd.congr_deriv hz
  have hconst : ∀ r > 0, A r = A 0 := const_on_Ioi_of_deriv_zero hderiv hcont
  have hA0 : A 0 = ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, t * W t z := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have hf_nonneg_t : 0 ≤ f t := hf_nonneg t htIcc
    have hup : max (-f t) (min (f t) (0 * t + h 0)) = 0 := by
      rw [h0]
      simp [hf_nonneg_t]
    change (∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + h 0))),
        (t + 0 * z) * W t z) = ∫ z in (-f t)..0, t * W t z
    rw [hup]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  have hhalf := cap_centroid_moment_at_zero (n := n) hn (f := f) hf_nonneg
  intro s hs
  calc
    (∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h s))),
          (t + s * z) * (f t ^ 2 - z ^ 2) ^ (n - 1))
        = A s := by simp [A, W]
    _ = A 0 := hconst s hs
    _ = ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..0, t * W t z := hA0
    _ = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(f t), t * W t z := hhalf
    _ = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        ∫ z in (-f t)..(f t), t * (f t ^ 2 - z ^ 2) ^ (n - 1) := by simp [W]

end Commons.Geometry.Ulam
