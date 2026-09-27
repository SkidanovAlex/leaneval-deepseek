import Mathlib
import Submission.Work.Whitney.BumpModel.structMap_immersion_infty
import Submission.Work.Whitney.BumpModel.uhat_fderiv_infty
import Submission.Work.Whitney.TransverseAux

namespace Work.Whitney.BumpModel

open scoped Manifold ContDiff
open Set Filter Topology

open Work.Whitney

/-- Coordinate description of the sheet map `sheetE0 n`. -/
theorem sheetE0_apply' (n : ℕ) [NeZero n] (v : Fin n → ℝ) (i : Fin n) :
    sheetE0 n v i = if i = 0 then -(1/2) * v i else (1/2) * v i := by
  simp only [sheetE0, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply]
  split_ifs <;> ring

/-- Coordinate description of the sheet map `sheetNegE0 n`. -/
theorem sheetNegE0_apply' (n : ℕ) [NeZero n] (v : Fin n → ℝ) (i : Fin n) :
    sheetNegE0 n v i = if i = 0 then (1/2) * v i else -(1/2) * v i := by
  simp only [sheetNegE0, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply]
  split_ifs <;> ring

/-- `û = χ/(1 + ∑ xᵢ²)` takes the value `1/2` at `e₀` when `χ = 1` on the ball of radius `2`. -/
theorem uhat_at_e0 (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hχ1 : ∀ x, ‖x‖ ≤ 2 → χ x = 1) : uhat n χ (e0 n) = 1 / 2 := by
  have h1 : χ (e0 n) = 1 := hχ1 (e0 n) (by rw [Work.Whitney.norm_e0]; norm_num)
  simp only [uhat, h1, bumpU_e0 n]

/-- `û = χ/(1 + ∑ xᵢ²)` takes the value `1/2` at `-e₀` when `χ = 1` on the ball of radius `2`. -/
theorem uhat_at_neg_e0 (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hχ1 : ∀ x, ‖x‖ ≤ 2 → χ x = 1) : uhat n χ (-(e0 n)) = 1 / 2 := by
  have h1 : χ (-(e0 n)) = 1 :=
    hχ1 (-(e0 n)) (by rw [norm_neg, Work.Whitney.norm_e0]; norm_num)
  simp only [uhat, h1, bumpU_neg_e0 n]

/-- The derivative of the cut-off structure map at the two preimages `±e₀` of its double point is
the linear inclusion on the first block and the "sheet" map on the second block; at `e₀` the second
block is `sheetE0 n`, at `-e₀` it is `sheetNegE0 n` (these are exactly the two sheets of Whitney's
local model, so the `coprod` of these two derivatives is the endomorphism `C n` whose determinant is
nonzero).  The hypothesis `hχ1` (`χ = 1` on the ball of radius `2`) is what makes the cut-off
inactive at `±e₀`, so that `û = χ/(1 + ∑ xᵢ²)` has value `1/2` there with the same derivative as
`1/(1 + ∑ xᵢ²)`. -/
theorem fderiv_structMap_at_pm_e0 (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ1 : ∀ x, ‖x‖ ≤ 2 → χ x = 1) :
    (∀ v : Fin n → ℝ, fderiv ℝ (structMap n χ) (e0 n) v = (v, sheetE0 n v)) ∧
      (∀ v : Fin n → ℝ, fderiv ℝ (structMap n χ) (-(e0 n)) v = (v, sheetNegE0 n v)) := by
  constructor
  · intro v
    rw [structMap_fderiv_smooth n hχ (e0 n) v,
      (uhat_fderiv_infty n (χ := χ) hχ hχ1 v).1, uhat_at_e0 n hχ1]
    refine Prod.ext ?_ ?_
    · funext i
      by_cases hi : i = 0
      · subst hi
        simp only [e0, Pi.single_eq_same, mul_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [e0, Pi.single_eq_of_ne hi, Pi.single_eq_same, mul_zero, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
        ring
    · funext i
      by_cases hi : i = 0
      · subst hi
        simp only [sheetE0, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
          ↓reduceIte, e0, Pi.single_eq_same, mul_one, Pi.add_apply, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [sheetE0, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
          hi, ↓reduceIte, e0, Pi.single_eq_of_ne hi, Pi.single_eq_same, mul_zero, Pi.add_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
  · intro v
    rw [structMap_fderiv_smooth n hχ (-(e0 n)) v,
      (uhat_fderiv_infty n (χ := χ) hχ hχ1 v).2, uhat_at_neg_e0 n hχ1]
    refine Prod.ext ?_ ?_
    · funext i
      by_cases hi : i = 0
      · subst hi
        simp only [e0, Pi.single_eq_same, Pi.neg_apply, neg_mul, one_mul, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [e0, Pi.single_eq_of_ne hi, Pi.single_eq_same, mul_zero, Pi.neg_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · funext i
      by_cases hi : i = 0
      · subst hi
        simp only [sheetNegE0, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
          ↓reduceIte, e0, Pi.single_eq_same, mul_one, Pi.add_apply, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
        ring
      · simp only [sheetNegE0, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
          hi, ↓reduceIte, e0, Pi.single_eq_of_ne hi, Pi.single_eq_same, mul_zero, Pi.add_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
        ring

end Work.Whitney.BumpModel
