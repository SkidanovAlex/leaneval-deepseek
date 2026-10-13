import Mathlib
import Submission.Work.WilE10.SubPfRexp.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.WilE10.SubPfRexp

open WilkiesDesign WilkiesDesign.E

/-- Triangle inequality on the cube: `|ell_j z|` is at most the sum of the absolute values of
the coefficients of the affine form `ell_j`. -/
private theorem abs_ell_le_coeff {k r : ℕ} (c : EAChain k r) (j : Fin r) {z : Fin k → ℝ}
    (hz : z ∈ cubeC k) :
    |c.ell j z| ≤ (∑ i, |c.a j i|) + |c.b j| := by
  have h1 : |c.ell j z| ≤ (∑ i, |c.a j i * z i|) + |c.b j| := by
    rw [EAChain.ell]
    calc |(∑ i, c.a j i * z i) + c.b j| ≤ |∑ i, c.a j i * z i| + |c.b j| := abs_add_le _ _
      _ ≤ (∑ i, |c.a j i * z i|) + |c.b j| := by
          have h := Finset.abs_sum_le_sum_abs (fun i : Fin k => c.a j i * z i) Finset.univ
          linarith
  have h2 : (∑ i, |c.a j i * z i|) ≤ ∑ i, |c.a j i| := by
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    calc |c.a j i| * |z i| ≤ |c.a j i| * 1 := mul_le_mul_of_nonneg_left (hz i) (abs_nonneg _)
      _ = |c.a j i| := mul_one _
  linarith

/-- The coefficient sum of `ell_j` is bounded by the natural number `Lbound c j`. -/
private theorem coeff_sum_le_Lbound {k r : ℕ} (c : EAChain k r) (j : Fin r) :
    (∑ i, |c.a j i|) + |c.b j| ≤ (Lbound c j : ℝ) := by
  rw [Lbound]
  exact Nat.le_ceil _

/-- **Cube bound for the chain functions.** On the cube `[-1,1]^k`, the value `c.ell j z` of the
`j`-th affine form is bounded in absolute value by `Lbound c j`, its normalisation
`c.ell j z / Lbound c j` lies in `[-1,1]`, and multiplying that normalisation back by
`Lbound c j` returns `c.ell j z`. -/
theorem cube_bound {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (j : Fin r) {z : Fin k → ℝ}
    (hz : z ∈ WilkiesDesign.E.cubeC k) :
    |c.ell j z| ≤ (Work.WilE10.SubPfRexp.Lbound c j : ℝ) ∧
    |c.ell j z / (Work.WilE10.SubPfRexp.Lbound c j : ℝ)| ≤ 1 ∧
    (Work.WilE10.SubPfRexp.Lbound c j : ℝ) * (c.ell j z / (Work.WilE10.SubPfRexp.Lbound c j : ℝ))
      = c.ell j z := by
  have hle : |c.ell j z| ≤ (Lbound c j : ℝ) :=
    le_trans (abs_ell_le_coeff c j hz) (coeff_sum_le_Lbound c j)
  have hLnn : (0 : ℝ) ≤ (Lbound c j : ℝ) := Nat.cast_nonneg _
  refine ⟨hle, ?_, ?_⟩
  · by_cases hL : (Lbound c j : ℝ) = 0
    · -- `Lbound c j = 0` forces `c.ell j z = 0`, and `0 / 0 = 0` in `ℝ`.
      have hx : c.ell j z = 0 := abs_eq_zero.mp (le_antisymm (hL ▸ hle) (abs_nonneg _))
      rw [hL, hx, zero_div, abs_zero]
      norm_num
    · have hpos : 0 < (Lbound c j : ℝ) := lt_of_le_of_ne hLnn (Ne.symm hL)
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hle
  · by_cases hL : (Lbound c j : ℝ) = 0
    · have hx : c.ell j z = 0 := abs_eq_zero.mp (le_antisymm (hL ▸ hle) (abs_nonneg _))
      rw [hL, hx, zero_div, mul_zero]
    · exact mul_div_cancel₀ (c.ell j z) hL

end Work.WilE10.SubPfRexp
