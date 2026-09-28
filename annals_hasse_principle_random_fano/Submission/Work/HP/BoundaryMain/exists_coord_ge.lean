import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic

namespace Work.HP.BoundaryMain

open Work.HP

/-- If the Euclidean norm of `y : Fin (n+1) → ℝ` is at least `1/2`, then some coordinate of `y`
has absolute value at least `1 / (2 √(n+1))`.  Indeed, if `M = max_i |y_i|` then every coordinate
is bounded by `M`, hence `‖y‖² ≤ (n+1) M²`, i.e. `M ≥ ‖y‖/√(n+1) ≥ 1/(2√(n+1))`. -/
theorem exists_coord_ge (n : ℕ) (y : Fin (n + 1) → ℝ) (hy : (1 : ℝ) / 2 ≤ Work.HP.rNorm y) :
    ∃ j : Fin (n + 1), 1 / (2 * Real.sqrt ((n : ℝ) + 1)) ≤ |y j| := by
  classical
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image Finset.univ (fun i => |y i|) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  have hcoord : ∀ i, |y i| ≤ |y j| := fun i => hj i (Finset.mem_univ i)
  -- Sum-of-squares bound.
  have hsum : Work.HP.rNorm y ^ 2 ≤ ((n : ℝ) + 1) * (|y j|) ^ 2 := by
    rw [rNorm_sq]
    calc ∑ i, (y i) ^ 2 = ∑ i, (|y i|) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by rw [sq_abs])
      _ ≤ ∑ _i : Fin (n + 1), (|y j|) ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2)
      _ = ((n : ℝ) + 1) * (|y j|) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hkey : Work.HP.rNorm y ≤ Real.sqrt ((n : ℝ) + 1) * |y j| := by
    have h := Real.sqrt_le_sqrt hsum
    rwa [Real.sqrt_sq (rNorm_nonneg y), Real.sqrt_mul (x := (n : ℝ) + 1) (by positivity) ((|y j|) ^ 2),
      Real.sqrt_sq (abs_nonneg _)] at h
  have h1 : (1 / 2) / Real.sqrt ((n : ℝ) + 1) ≤ Work.HP.rNorm y / Real.sqrt ((n : ℝ) + 1) :=
    div_le_div_of_nonneg_right hy (le_of_lt hs)
  have h2 : Work.HP.rNorm y / Real.sqrt ((n : ℝ) + 1) ≤ |y j| := by
    rw [div_le_iff₀ hs, mul_comm]
    exact hkey
  have h3 : (1 : ℝ) / (2 * Real.sqrt ((n : ℝ) + 1)) = (1 / 2) / Real.sqrt ((n : ℝ) + 1) := by
    rw [div_div]
  rw [h3]
  exact h1.trans h2

end Work.HP.BoundaryMain
