import Mathlib

namespace Work.LinnikAreas.Density4

theorem sum_Icc_inv_le_one (m : ℕ) (hm : 1 ≤ m) :
    ∑ e ∈ Finset.Icc m (2 * m - 1), (1 : ℝ) / (e : ℝ) ≤ 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcard : (Finset.Icc m (2 * m - 1)).card = m := by
    rw [Nat.card_Icc]
    omega
  have hle : ∀ e ∈ Finset.Icc m (2 * m - 1),
      (1 : ℝ) / (e : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by
    intro e he
    have he1 : m ≤ e := (Finset.mem_Icc.mp he).1
    have h : (m : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
    exact one_div_le_one_div_of_le hmpos h
  calc ∑ e ∈ Finset.Icc m (2 * m - 1), (1 : ℝ) / (e : ℝ)
      ≤ ∑ _e ∈ Finset.Icc m (2 * m - 1), (1 : ℝ) / (m : ℝ) := Finset.sum_le_sum hle
    _ = (Finset.Icc m (2 * m - 1)).card • ((1 : ℝ) / (m : ℝ)) := Finset.sum_const _
    _ = (m : ℝ) * ((1 : ℝ) / (m : ℝ)) := by rw [nsmul_eq_mul, hcard]
    _ = 1 := by
        field_simp

end Work.LinnikAreas.Density4
