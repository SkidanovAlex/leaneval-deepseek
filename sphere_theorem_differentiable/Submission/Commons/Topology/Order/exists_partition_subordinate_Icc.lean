import Mathlib.Algebra.CharP.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.Order

open Set Metric

theorem exists_partition_subordinate_Icc {ι : Type*} [Fintype ι] {U : ι → Set ℝ}
    (hU : ∀ i, IsOpen (U i)) {a b : ℝ} (hab : a ≤ b)
    (hcov : Set.Icc a b ⊆ ⋃ i, U i) :
    ∃ N : ℕ, ∃ c : ℕ → ℝ, c 0 = a ∧ c N = b ∧ (∀ k < N, c k < c (k + 1)) ∧
      (∀ k < N, ∃ i, Set.Icc (c k) (c (k + 1)) ⊆ U i) := by
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · rw [hab_eq]
    exact ⟨0, fun _ => b, rfl, rfl, by simp, by simp⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hU hcov
  have hba : 0 < b - a := sub_pos.mpr hab_lt
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hNpos : 0 < N := by
    have : (0:ℝ) < (N:ℝ) := lt_trans (div_pos hba hδpos) hN
    exact_mod_cast this
  have hNposR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNposR
  have hfrac : 0 < (b - a) / (N:ℝ) := div_pos hba hNposR
  have hfrac_lt : (b - a) / (N:ℝ) < δ := by
    rw [div_lt_iff₀ hNposR]
    rw [div_lt_iff₀ hδpos] at hN
    linarith
  let c : ℕ → ℝ := fun k => a + (k:ℝ) * ((b - a) / (N:ℝ))
  have hc0 : c 0 = a := by simp [c]
  have hcN : c N = b := by
    simp only [c]
    rw [mul_div_cancel₀ _ hNne]
    ring
  have hmono : ∀ k < N, c k < c (k + 1) := by
    intro k hk
    have hk' : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by push_cast; ring
    simp only [c]
    rw [hk']
    nlinarith [hfrac]
  have hsub : ∀ k < N, ∃ i, Set.Icc (c k) (c (k + 1)) ⊆ U i := by
    intro k hk
    have hck : c k ∈ Set.Icc a b := by
      simp only [c]
      constructor
      · nlinarith [mul_nonneg (Nat.cast_nonneg k) (le_of_lt hfrac)]
      · have hk_le : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.le_of_lt hk
        have hmul := mul_le_mul_of_nonneg_right hk_le (le_of_lt hfrac)
        rw [mul_div_cancel₀ _ hNne] at hmul
        linarith
    obtain ⟨i, hi⟩ := hδ (c k) hck
    refine ⟨i, fun y hy => hi ?_⟩
    rw [mem_ball, Real.dist_eq]
    have hstepk : c (k + 1) = c k + (b - a) / (N:ℝ) := by
      simp only [c]; push_cast; ring
    have hyge : 0 ≤ y - c k := by linarith [hy.1]
    have hyle : y - c k ≤ (b - a) / (N:ℝ) := by
      have h := hy.2; rw [hstepk] at h; linarith
    rw [abs_of_nonneg hyge]
    linarith [hyle, hfrac_lt]
  exact ⟨N, c, hc0, hcN, hmono, hsub⟩

end Commons.Topology.Order