import Mathlib
import Submission.Commons.Geometry.Ulam.moment_h_bounds
import Submission.Work.Geometry.Ulam.active_nonneg_outside_of_roots_inside_general

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma odd_pow_clamp_integral_eq_interval_of_active_general
    {n : ℕ} {f : ℝ → ℝ} {s h a b A B : ℝ}
    (hn : 1 ≤ n) (hs : 0 < s) (hAB : A < B)
    (ha_mem : a ∈ Set.Ioo A B) (hb_mem : b ∈ Set.Ioo A B)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc A B) f)
    (hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo A B, 0 < f t)
    (hfa_sq : f a ^ 2 = (s * a + h) ^ 2)
    (hfb_sq : f b ^ 2 = (s * b + h) ^ 2) :
    (∫ t in A..B,
        (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2) ^ n *
          Real.sqrt (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2)) =
      ∫ t in a..b, (f t ^ 2 - (s * t + h) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h) ^ 2) := by
  let L : ℝ → ℝ := fun t => s * t + h
  let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (L t))
  let F : ℝ → ℝ := fun t => (f t ^ 2 - (U t) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (U t) ^ 2)
  let G : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then (f t ^ 2 - (L t) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (L t) ^ 2) else 0
  have hactive := active_nonneg_outside_of_roots_inside_general (f := f) (s := s) (h := h)
    (u := a) (v := b) (α := A) (β := B) hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hFG : Set.EqOn F G (Set.Icc A B) := by
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
      have hF0 : (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2) ^ n *
          Real.sqrt (f t ^ 2 - (max (-f t) (min (f t) (s * t + h))) ^ 2) = 0 := by
        rw [hU_zero]
        simp
      rw [if_neg htab, hF0]
  have hF_eq_G : (∫ t in A..B, F t) = ∫ t in A..B, G t := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le hAB.le] using hFG
  have hab : a < b := lt_trans ha_neg hb_pos
  have hG_a : G a = 0 := by
    have htab : a ≤ a ∧ a ≤ b := ⟨le_rfl, hab.le⟩
    have hbase : f a ^ 2 - (s * a + h) ^ 2 = 0 := by rw [hfa_sq]; ring
    dsimp [G, L]
    rw [if_pos htab, hbase]
    simp
  have hG_b : G b = 0 := by
    have htab : a ≤ b ∧ b ≤ b := ⟨hab.le, le_rfl⟩
    have hbase : f b ^ 2 - (s * b + h) ^ 2 = 0 := by rw [hfb_sq]; ring
    dsimp [G, L]
    rw [if_pos htab, hbase]
    simp
  have hsuppG_AB : Function.support G ⊆ Set.Ioc A B := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : a ≤ t ∧ t ≤ b
    · have ht_gt : A < t := lt_of_lt_of_le ha_mem.1 htab.1
      have ht_le : t ≤ B := le_trans htab.2 (le_of_lt hb_mem.2)
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
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := A) (b := B) hsuppG_AB
  have hIab := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_ab
  calc
    (∫ t in A..B, F t) = ∫ t in A..B, G t := hF_eq_G
    _ = ∫ t, G t := hI1
    _ = ∫ t in a..b, G t := hIab.symm
    _ = ∫ t in a..b, (f t ^ 2 - (s * t + h) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htab : a ≤ t ∧ t ≤ b := by
        rwa [Set.uIcc_of_le hab.le] at ht
      dsimp [G]
      rw [if_pos htab]

end Commons.Geometry.Ulam
