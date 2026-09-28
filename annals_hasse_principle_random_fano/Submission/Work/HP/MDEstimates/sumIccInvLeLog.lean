import Mathlib

namespace Work.HP.MDEstimates

/-- The sum of the reciprocals of the integers in `(L, n]` is at most
`log (n / L)`, via comparison with the integral of `x ↦ x⁻¹`. -/
theorem sumIccInvLeLog (L n : ℕ) (hL : 1 ≤ L) (hLn : L ≤ n) :
    (∑ l ∈ Finset.Icc (L + 1) n, 1 / (l : ℝ)) ≤ Real.log ((n : ℝ) / L) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have key : ∑ i ∈ Finset.Ico L n, (((i + 1 : ℕ)) : ℝ)⁻¹ ≤ ∫ x in (L : ℝ)..(n : ℝ), x⁻¹ :=
    AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x⁻¹) (a := L) (b := n) hLn
      (inv_antitoneOn_Icc_right hLpos)
  rw [Finset.sum_Ico_add' (fun j : ℕ => ((j : ℝ))⁻¹) L n 1] at key
  rw [Finset.Ico_add_one_right_eq_Icc] at key
  rw [integral_inv_of_pos hLpos hnpos] at key
  simpa [one_div] using key

end Work.HP.MDEstimates
