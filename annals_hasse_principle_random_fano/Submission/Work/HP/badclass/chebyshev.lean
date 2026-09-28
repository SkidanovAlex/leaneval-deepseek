import Mathlib

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP.badclass

/-- Second-moment (Chebyshev) bound on the number of `a` with `M a = 0`. -/
theorem chebyshev {α : Type*} [Fintype α] (M : α → ℕ) :
    ((Finset.univ.filter (fun a => M a = 0)).card : ℝ) * (∑ a, (M a : ℝ)) ^ 2
      ≤ (Fintype.card α : ℝ) *
          ((Fintype.card α : ℝ) * (∑ a, (M a : ℝ) ^ 2) - (∑ a, (M a : ℝ)) ^ 2) := by
  classical
  set s : Finset α := Finset.univ.filter (fun a => M a ≠ 0) with hs
  set z : ℕ := (Finset.univ.filter (fun a => M a = 0)).card with hz
  set S : ℝ := ∑ a, (M a : ℝ) with hS
  set T : ℝ := ∑ a, (M a : ℝ) ^ 2 with hT
  set q : ℝ := (Fintype.card α : ℝ) with hq
  have hzt : (Finset.univ.filter (fun a => ¬ (M a ≠ 0))).card = z := by
    rw [hz]
    congr 1
    ext a
    simp
  have hcard : s.card + z = Fintype.card α := by
    rw [hs, ← hzt, Finset.card_filter_add_card_filter_not]
    simp
  have hScard : S = ∑ a ∈ s, (M a : ℝ) := by
    rw [hS, hs]
    exact (Finset.sum_subset (Finset.filter_subset _ _) (fun a _ ha => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
      rw [ha]; simp)).symm
  have hTle : (∑ a ∈ s, ((M a : ℝ)) ^ 2) ≤ T := by
    rw [hT, hs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => by positivity)
  have hcs : (∑ a ∈ s, (M a : ℝ)) ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, (M a : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsz : (s.card : ℝ) = q - (z : ℝ) := by
    have h : ((s.card : ℝ) + (z : ℝ)) = q := by
      rw [hq]; exact_mod_cast hcard
    linarith
  have hzq : (z : ℝ) ≤ q := by
    have h0 : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
    linarith
  have hsq : S ^ 2 ≤ (q - (z : ℝ)) * T := by
    rw [hScard, ← hsz]
    exact hcs.trans (mul_le_mul_of_nonneg_left hTle (by positivity))
  have hT0 : 0 ≤ T := by positivity
  have h1 : ((z : ℝ) + q) * S ^ 2 ≤ ((z : ℝ) + q) * ((q - (z : ℝ)) * T) :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  have h2 : ((z : ℝ) + q) * ((q - (z : ℝ)) * T) = (q ^ 2 - (z : ℝ) ^ 2) * T := by ring
  have h3 : (q ^ 2 - (z : ℝ) ^ 2) * T ≤ q ^ 2 * T := by nlinarith [sq_nonneg ((z : ℝ)), hT0]
  have h4 : ((z : ℝ) + q) * S ^ 2 ≤ q ^ 2 * T :=
    le_trans h1 (le_trans (le_of_eq h2) h3)
  nlinarith [h4]

end Work.HP.badclass
