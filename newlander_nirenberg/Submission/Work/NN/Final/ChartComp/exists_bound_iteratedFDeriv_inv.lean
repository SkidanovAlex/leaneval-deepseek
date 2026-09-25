import Mathlib

namespace Work.NN.Final.ChartComp

/-- The `m`-th iterated derivative of `r ↦ r⁻¹` at `r > 0`, obtained from
`iteratedDerivWithin_one_div` on the open set `univ`. -/
lemma iteratedDeriv_inv_eq (m : ℕ) (r : ℝ) :
    iteratedDeriv m (fun r : ℝ => r⁻¹) r
      = (-1) ^ m * (Nat.factorial m : ℝ) * r ^ (-1 - (m : ℤ)) := by
  rw [show (fun r : ℝ => r⁻¹) = (fun y : ℝ => 1 / y) by funext y; rw [one_div]]
  have h := (iteratedDerivWithin_one_div (𝕜 := ℝ) m isOpen_univ) (Set.mem_univ r)
  simpa only [iteratedDerivWithin_univ] using h

/-- Exact value of the norm of the `m`-th iterated Fréchet derivative of `r ↦ r⁻¹` at `r > 0`. -/
lemma norm_iteratedFDeriv_inv_eq (m : ℕ) (r : ℝ) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ m (fun r : ℝ => r⁻¹) r‖
      = (Nat.factorial m : ℝ) * (1 / r) ^ (m + 1) := by
  have hval := iteratedDeriv_inv_eq m r
  have hexp : r ^ (-1 - (m : ℤ)) = (1 / r) ^ (m + 1) := by
    rw [show (-1 : ℤ) - (m : ℤ) = -((m + 1 : ℕ) : ℤ) by push_cast; ring]
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hval, hexp]
  rw [norm_mul, norm_mul]
  rw [show ‖(-1 : ℝ) ^ m‖ = 1 by simp]
  rw [Real.norm_of_nonneg (Nat.cast_nonneg (Nat.factorial m))]
  rw [Real.norm_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < (1 / r) ^ (m + 1)))]
  ring

theorem exists_bound_iteratedFDeriv_inv :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (r : ℝ),
      0 < r → ‖iteratedFDeriv ℝ m (fun r : ℝ => r⁻¹) r‖ ≤ C m * (1 / r) ^ (m + 1) := by
  refine ⟨fun m => (Nat.factorial m : ℝ), fun m => Nat.cast_pos.mpr (Nat.factorial_pos m), ?_⟩
  intro m _hm r hr
  rw [norm_iteratedFDeriv_inv_eq m r hr]

end Work.NN.Final.ChartComp
