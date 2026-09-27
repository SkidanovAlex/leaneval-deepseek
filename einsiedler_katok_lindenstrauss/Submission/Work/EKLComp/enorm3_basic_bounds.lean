import Mathlib
import Submission.Work.EKLComp.EucDefs

namespace Work.EKLComp

/-- Elementary bounds comparing the hand-rolled Euclidean norm `enorm3 v = sqrt (∑ i, v i * v i)`
with the coordinates of `v` and with the default (sup) norm `‖v‖` on `Fin 3 → ℝ`
(`Pi.norm_def`). -/
theorem enorm3_basic_bounds (v : Fin 3 → ℝ) :
    (0 ≤ Work.EKLComp.enorm3 v) ∧
    (∀ i, |v i| ≤ Work.EKLComp.enorm3 v) ∧
    ‖v‖ ≤ Work.EKLComp.enorm3 v ∧
    Work.EKLComp.enorm3 v ≤ Real.sqrt 3 * ‖v‖ ∧
    (Work.EKLComp.enorm3 v = 0 ↔ v = 0) := by
  have hnn : ∀ i, 0 ≤ v i * v i := fun i => mul_self_nonneg (v i)
  have hsum_nonneg : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => hnn i)
  have hsqrt_nonneg : 0 ≤ enorm3 v := Real.sqrt_nonneg _
  -- coordinate bound
  have hcoord : ∀ i, |v i| ≤ enorm3 v := by
    intro i
    have hle : v i * v i ≤ ∑ j, v j * v j :=
      Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have h1 : |v i| = Real.sqrt (v i * v i) := by
      rw [show v i * v i = v i ^ 2 from (sq (v i)).symm, Real.sqrt_sq_eq_abs]
    change |v i| ≤ Real.sqrt (∑ j, v j * v j)
    rw [h1]
    exact Real.sqrt_le_sqrt hle
  refine ⟨hsqrt_nonneg, hcoord, ?_, ?_, ?_⟩
  · -- sup norm dominates every coordinate
    rw [pi_norm_le_iff_of_nonneg hsqrt_nonneg]
    intro i
    simpa [Real.norm_eq_abs] using hcoord i
  · -- Euclidean norm bounded by sqrt 3 times the sup norm
    have hbound : ∑ i, v i * v i ≤ 3 * ‖v‖ ^ 2 := by
      have h : ∀ i ∈ (Finset.univ : Finset (Fin 3)), v i * v i ≤ ‖v‖ ^ 2 := by
        intro i _
        have h1 : ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
        have h2 : v i * v i = ‖v i‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs, sq]
        calc v i * v i = ‖v i‖ ^ 2 := h2
          _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc ∑ i, v i * v i ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := Finset.sum_le_sum h
        _ = 3 * ‖v‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_fin]
            norm_num
    have h := Real.sqrt_le_sqrt hbound
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) (‖v‖ ^ 2),
      Real.sqrt_sq (norm_nonneg v)] at h
    simpa only [enorm3, dot3] using h
  · -- vanishing
    constructor
    · intro hv
      have hle : ∑ i, v i * v i ≤ 0 :=
        (Real.sqrt_eq_zero').1 (by simpa only [enorm3, dot3] using hv)
      have hz : ∑ i, v i * v i = 0 := le_antisymm hle hsum_nonneg
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hz i (Finset.mem_univ i)
      exact (mul_self_eq_zero).1 hi
    · intro hv
      rw [enorm3, dot3, hv]
      simp

end Work.EKLComp
