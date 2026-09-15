import ChallengeDeps

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

lemma equiv_apply (x : ℝᵈ) (i : Fin d) : (EuclideanSpace.equiv (Fin d) ℝ) x i = x i := by
  rfl

lemma mem_cube_iff (a b : ℝ) (x : ℝᵈ) :
    x ∈ (cube a b : Set ℝᵈ) ↔ ∀ i : Fin d, x i ∈ Set.Icc a b := by
  simp only [cube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Icc, equiv_apply]

lemma mem_cube (a b : ℝ) (x : ℝᵈ) :
    x ∈ (cube a b : Set ℝᵈ) ↔ ∀ i : Fin d, a ≤ x i ∧ x i ≤ b := by
  simp only [cube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Icc, equiv_apply]

lemma cube_subset {a b a' b' : ℝ} (h1 : a' ≤ a) (h2 : b ≤ b') :
    (cube a b : Set ℝᵈ) ⊆ cube a' b' := by
  intro x hx
  rw [mem_cube] at hx ⊢
  intro i
  exact ⟨le_trans h1 (hx i).1, le_trans (hx i).2 h2⟩

/-- If `0 < h ≤ 1`, then the unit cube sits inside the big `h`-cube. -/
lemma cube_unit_subset_cube_inv {h : ℝ} (hh1 : 0 < h) (hh2 : h ≤ 1) :
    (cube (-1) 1 : Set ℝᵈ) ⊆ cube (-h⁻¹) h⁻¹ := by
  refine cube_subset ?_ ?_
  · have hge : (1 : ℝ) ≤ h⁻¹ := (one_le_inv₀ hh1).2 hh2
    linarith
  · exact (one_le_inv₀ hh1).2 hh2

/-- If `x ∈ cube (-c) c` with `c ≥ 0`, then `‖x‖ ≤ √d · c`. -/
lemma norm_le_of_mem_cube_center {c : ℝ} (hc : 0 ≤ c) {x : ℝᵈ}
    (hx : x ∈ (cube (-c) c : Set ℝᵈ)) :
    ‖x‖ ≤ Real.sqrt (d : ℝ) * c := by
  rw [mem_cube] at hx
  have habs : ∀ i : Fin d, |x i| ≤ c := by
    intro i
    exact abs_le.mpr ⟨(hx i).1, (hx i).2⟩
  have h1 : ‖x‖ ^ 2 ≤ (Real.sqrt (d : ℝ) * c) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i : Fin d, (x i) ^ 2) ≤ ∑ i : Fin d, c ^ 2 := by
        exact Finset.sum_le_sum (fun i _ => by
          exact sq_le_sq.mpr (by simpa [abs_of_nonneg hc] using habs i))
      _ = (d : ℝ) * c ^ 2 := by simp
      _ = (Real.sqrt (d : ℝ) * c) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by exact_mod_cast Nat.zero_le d)]
  have h2 : |‖x‖| ≤ |Real.sqrt (d : ℝ) * c| := sq_le_sq.mp h1
  simpa [abs_of_nonneg (norm_nonneg x),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg (d : ℝ)) hc)] using h2

/-- `cube (-c) c` with `c ≥ 0` is contained in the closed ball of radius `√d · c`. -/
lemma cube_center_subset_closedBall {c : ℝ} (hc : 0 ≤ c) :
    (cube (-c) c : Set ℝᵈ) ⊆ closedBall 0 (Real.sqrt (d : ℝ) * c) := by
  intro x hx
  rw [Metric.mem_closedBall]
  simpa [dist_eq_norm] using norm_le_of_mem_cube_center hc hx

/-- The cube `[-4,4]^d` is contained in the ball of radius `4√d`. -/
lemma cube_four_subset_closedBall :
    (cube (-4) 4 : Set ℝᵈ) ⊆ closedBall 0 (4 * Real.sqrt (d : ℝ)) := by
  intro x hx
  have h := norm_le_of_mem_cube_center (by norm_num : (0 : ℝ) ≤ 4) hx
  rw [Metric.mem_closedBall]
  calc
    dist x 0 ≤ Real.sqrt (d : ℝ) * 4 := by simpa [dist_eq_norm, mul_comm] using h
    _ = 4 * Real.sqrt (d : ℝ) := by ring

/-- The big cube `[-h⁻¹, h⁻¹]^d` lies in a ball of radius `h⁻¹ √d` (for `h > 0`). -/
lemma cube_inv_subset_closedBall {h : ℝ} (hh : 0 < h) :
    (cube (-h⁻¹) h⁻¹ : Set ℝᵈ) ⊆ closedBall 0 (h⁻¹ * Real.sqrt (d : ℝ)) := by
  intro x hx
  have hn : ‖x‖ ≤ Real.sqrt (d : ℝ) * h⁻¹ :=
    norm_le_of_mem_cube_center (inv_nonneg.mpr (le_of_lt hh)) hx
  rw [Metric.mem_closedBall]
  calc
    dist x 0 ≤ Real.sqrt (d : ℝ) * h⁻¹ := by simpa [dist_eq_norm] using hn
    _ = h⁻¹ * Real.sqrt (d : ℝ) := by ring

end Submission.FUP
