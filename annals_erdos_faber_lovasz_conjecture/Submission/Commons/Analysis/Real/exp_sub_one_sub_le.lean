import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The elementary bound `exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3))` on `[0, 3)`

For `0 ≤ u < 3` we prove

`Real.exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3))`.

The proof is a three-step monotonicity (Taylor-Lagrange) argument.  Put

* `ψ u = 1 + (u - 1) e ^ u`,   with `ψ 0 = 0` and `ψ' u = u e ^ u ≥ 0` for `u ≥ 0`;
* `χ u = 2 + u - (2 - u) e ^ u`, with `χ 0 = 0` and `χ' = ψ ≥ 0` for `u ≥ 0`;
* `G u = u ^ 2 - 2 (1 - u / 3) (e ^ u - 1 - u)`, with `G 0 = 0` and
  `G' = (2 / 3) χ ≥ 0` for `u ≥ 0`.

Hence `ψ, χ, G ≥ 0` on `[0, ∞)`.  `G ≥ 0` says exactly
`2 (1 - u / 3) (e ^ u - 1 - u) ≤ u ^ 2`, and dividing by the positive quantity
`2 (1 - u / 3)` (positive because `u < 3`) gives the claim.
-/

namespace Commons.Analysis.Real

/-- Derivative computation for `ψ u = 1 + (u - 1) e ^ u`. -/
private lemma deriv_psi (x : ℝ) :
    deriv (fun u : ℝ => 1 + (u - 1) * Real.exp u) x = x * Real.exp x := by
  rw [show (fun u : ℝ => 1 + (u - 1) * Real.exp u)
      = ((fun _ : ℝ => (1 : ℝ)) + ((id - fun _ : ℝ => (1 : ℝ)) * Real.exp)) from rfl]
  rw [deriv_add, deriv_mul, deriv_const, deriv_sub, deriv_id, deriv_const, Real.deriv_exp]
  · simp only [Pi.sub_apply, id_eq]
    ring
  all_goals fun_prop

/-- `ψ u = 1 + (u - 1) e ^ u` is nonnegative on `[0, ∞)`. -/
private lemma psi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ 1 + (u - 1) * Real.exp u := by
  have hmono : MonotoneOn (fun u : ℝ => 1 + (u - 1) * Real.exp u) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      rw [interior_Ici] at hx
      rw [deriv_psi]
      exact mul_nonneg (le_of_lt hx) (le_of_lt (Real.exp_pos x))
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  simpa using h

/-- Derivative computation for `χ u = 2 + u - (2 - u) e ^ u`; note `χ' = ψ`. -/
private lemma deriv_chi (x : ℝ) :
    deriv (fun u : ℝ => 2 + u - (2 - u) * Real.exp u) x = 1 + (x - 1) * Real.exp x := by
  rw [show (fun u : ℝ => 2 + u - (2 - u) * Real.exp u)
      = (((fun _ : ℝ => (2 : ℝ)) + id) - (((fun _ : ℝ => (2 : ℝ)) - id) * Real.exp))
      from rfl]
  rw [deriv_sub, deriv_add, deriv_mul, deriv_const, deriv_id, deriv_sub, deriv_const, deriv_id,
      Real.deriv_exp]
  · simp only [Pi.sub_apply, id_eq]
    ring
  all_goals fun_prop

/-- `χ u = 2 + u - (2 - u) e ^ u` is nonnegative on `[0, ∞)`. -/
private lemma chi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ 2 + u - (2 - u) * Real.exp u := by
  have hmono : MonotoneOn (fun u : ℝ => 2 + u - (2 - u) * Real.exp u) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      rw [interior_Ici] at hx
      rw [deriv_chi]
      exact psi_nonneg (le_of_lt hx)
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  simpa using h

/-- Derivative computation for `G u = u ^ 2 - 2 (1 - u / 3) (e ^ u - 1 - u)`. -/
private lemma deriv_g (x : ℝ) :
    deriv (fun u : ℝ => u ^ 2 - 2 * (1 - u / 3) * (Real.exp u - 1 - u)) x
      = (2 / 3) * (2 + x - (2 - x) * Real.exp x) := by
  rw [show (fun u : ℝ => u ^ 2 - 2 * (1 - u / 3) * (Real.exp u - 1 - u))
      = ((fun u : ℝ => u ^ 2)
          - ((fun u : ℝ => 2 * (1 - u / 3)) * ((Real.exp - fun _ : ℝ => (1 : ℝ)) - id)))
      from rfl]
  rw [deriv_sub, deriv_mul]
  · rw [show deriv (fun u : ℝ => u ^ 2) x = 2 * x by simp]
    rw [show deriv (fun u : ℝ => 2 * (1 - u / 3)) x = -(2 / 3) by
      simp
      ring]
    rw [show deriv ((Real.exp - fun _ : ℝ => (1 : ℝ)) - id) x = Real.exp x - 1 by simp]
    simp only [Pi.sub_apply, id_eq]
    ring
  all_goals fun_prop

/-- `G u = u ^ 2 - 2 (1 - u / 3) (e ^ u - 1 - u)` is nonnegative on `[0, ∞)`. -/
private lemma g_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u ^ 2 - 2 * (1 - u / 3) * (Real.exp u - 1 - u) := by
  have hmono :
      MonotoneOn (fun u : ℝ => u ^ 2 - 2 * (1 - u / 3) * (Real.exp u - 1 - u)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      rw [interior_Ici] at hx
      rw [deriv_g]
      exact mul_nonneg (by norm_num) (chi_nonneg (le_of_lt hx))
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  simpa using h

theorem exp_sub_one_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 3) :
    Real.exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3)) := by
  have hpos : 0 < 2 * (1 - u / 3) := by linarith
  have hG := g_nonneg hu0
  rw [le_div_iff₀ hpos]
  nlinarith [hG]

end Commons.Analysis.Real
