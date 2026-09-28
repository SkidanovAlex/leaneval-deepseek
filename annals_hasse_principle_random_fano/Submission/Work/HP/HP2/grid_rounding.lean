import Mathlib
import Submission.Work.HP.HP2.GridDefs
import Submission.Work.HP.tau_basic

namespace Work.HP.HP2

/-! ## Auxiliary facts for `grid_rounding` -/

/-- The fractional part of `t`, scaled by a positive `W`, lies in `[0, W)`. -/
lemma mul_fract_mem_Ico {W : ℝ} (hW : 0 < W) (t : ℝ) :
    W * Int.fract t ∈ Set.Ico 0 W := by
  constructor
  · exact mul_nonneg (le_of_lt hW) (Int.fract_nonneg t)
  · calc W * Int.fract t < W * 1 := mul_lt_mul_of_pos_left (Int.fract_lt_one t) hW
      _ = W := by ring

/-- A point of the fundamental box `∏ᵢ [0, W)` has Euclidean norm at most `√m · W`. -/
lemma rNorm_le_sqrt_mul_of_mem_fundBox {m : ℕ} {W : ℝ} (hW : 0 ≤ W) {y : Fin m → ℝ}
    (hy : y ∈ fundBox m W) : rNorm y ≤ Real.sqrt m * W := by
  rw [fundBox, Set.mem_pi] at hy
  have hsum : ∑ i, (y i) ^ 2 ≤ (m : ℝ) * W ^ 2 := by
    calc ∑ i : Fin m, (y i) ^ 2 ≤ ∑ _ : Fin m, W ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact pow_le_pow_left₀ (hy i (Set.mem_univ i)).1
            (le_of_lt (hy i (Set.mem_univ i)).2) 2
      _ = (m : ℝ) * W ^ 2 := by simp
  rw [rNorm]
  calc Real.sqrt (∑ i, (y i) ^ 2) ≤ Real.sqrt ((m : ℝ) * W ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt m * W := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq_eq_abs, abs_of_nonneg hW]

/-- Coordinatewise, the rounding error `x - gridPt m W b x` is `W` times the fractional
part of `(x i - b i)/W`. -/
lemma sub_gridPt_eq (m : ℕ) {W : ℕ} (hW : 0 < W) (b : Fin m → ℤ) (x : Fin m → ℝ)
    (i : Fin m) : x i - gridPt m W b x i = (W : ℝ) * Int.fract ((x i - (b i : ℝ)) / (W : ℝ)) := by
  have hWne : (W : ℝ) ≠ 0 := by positivity
  simp only [gridPt, gridVal, gridIdx]
  have ht : (W : ℝ) * ((x i - (b i : ℝ)) / (W : ℝ)) = x i - (b i : ℝ) := by field_simp
  rw [show Int.fract ((x i - (b i : ℝ)) / (W : ℝ))
        = (x i - (b i : ℝ)) / (W : ℝ) - ⌊(x i - (b i : ℝ)) / (W : ℝ)⌋ from rfl, mul_sub, ht]
  ring

/-- Rounding a point `x ∈ ℝ^m` down to the point of the coset `b + W ℤ^m` at or below it
(`gridIdx` is the coordinatewise floor of `(x - b)/W`, `gridPt = gridVal ∘ gridIdx`). -/
theorem grid_rounding (m : ℕ) {W : ℕ} (hW : 0 < W) (b : Fin m → ℤ) :
    (∀ x : Fin m → ℝ, x - gridPt m W b x ∈ fundBox m (W : ℝ)) ∧
    (∀ x : Fin m → ℝ, rNorm (x - gridPt m W b x) ≤ Real.sqrt m * (W : ℝ)) ∧
    (∀ y : Fin m → ℝ, y ∈ fundBox m (W : ℝ) → rNorm y ≤ Real.sqrt m * (W : ℝ)) := by
  have hWℝ : (0 : ℝ) < W := by exact_mod_cast hW
  have hmem : ∀ x : Fin m → ℝ, x - gridPt m W b x ∈ fundBox m (W : ℝ) := by
    intro x
    rw [fundBox, Set.mem_pi]
    intro i _
    rw [Pi.sub_apply, sub_gridPt_eq m hW b x i]
    exact mul_fract_mem_Ico hWℝ _
  exact ⟨hmem, fun x => rNorm_le_sqrt_mul_of_mem_fundBox (le_of_lt hWℝ) (hmem x),
    fun y hy => rNorm_le_sqrt_mul_of_mem_fundBox (le_of_lt hWℝ) hy⟩

end Work.HP.HP2
