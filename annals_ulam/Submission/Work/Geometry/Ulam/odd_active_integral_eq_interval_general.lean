import Mathlib
import Submission.Commons.Geometry.Ulam.moment_h_bounds
import Submission.Work.Geometry.Ulam.active_nonneg_outside_of_roots_inside_general

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma odd_active_integral_eq_interval_general
    {f : ℝ → ℝ} {s h a b A B : ℝ} {D : ℝ → ℝ} (hAB : A < B)
    (hs : 0 < s)
    (ha_mem : a ∈ Set.Ioo A B) (hb_mem : b ∈ Set.Ioo A B)
    (ha_neg : a < 0) (hb_pos : 0 < b)
    (hf_conc : ConcaveOn ℝ (Set.Icc A B) f)
    (hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo A B, 0 < f t)
    (hfa_sq : f a ^ 2 = (s * a + h) ^ 2)
    (hfb_sq : f b ^ 2 = (s * b + h) ^ 2)
    (hD_zero_out : ∀ t ∈ Set.Icc A B, ¬ (-f t < s * t + h ∧ s * t + h < f t) → D t = 0)
    (hD_a : D a = 0) (hD_b : D b = 0) :
    (∫ t in A..B, if -f t < s * t + h ∧ s * t + h < f t then D t else 0) =
      ∫ t in a..b, D t := by
  have hactive := active_nonneg_outside_of_roots_inside_general (f := f) (s := s) (h := h)
    (u := a) (v := b) (α := A) (β := B) hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  let L : ℝ → ℝ := fun t => s * t + h
  let F : ℝ → ℝ := fun t => if -f t < L t ∧ L t < f t then D t else 0
  let G : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then D t else 0
  have hFG : Set.EqOn F G (Set.Icc A B) := by
    intro t ht
    by_cases htab : a ≤ t ∧ t ≤ b
    · dsimp [F, G, L]
      rw [if_pos htab]
      by_cases hact : -f t < s * t + h ∧ s * t + h < f t
      · rw [if_pos hact]
      · rw [if_neg hact, hD_zero_out t ht hact]
    · dsimp [F, G, L]
      have hact_false : ¬ (-f t < s * t + h ∧ s * t + h < f t) := by
        intro hact
        exact htab (hactive.1 t ht hact)
      rw [if_neg htab, if_neg hact_false]
  have hF_eq_G : (∫ t in A..B, F t) = ∫ t in A..B, G t := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le hAB.le] using hFG
  have hab : a < b := lt_trans ha_neg hb_pos
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
          simp [G, hD_a]
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
    _ = ∫ t in a..b, D t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htab : a ≤ t ∧ t ≤ b := by
        rwa [Set.uIcc_of_le hab.le] at ht
      dsimp [G]
      rw [if_pos htab]

end Commons.Geometry.Ulam
