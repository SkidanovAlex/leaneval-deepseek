import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.Interval

theorem exists_grid_Icc_gap_lt {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∃ (n : ℕ) (s : ℕ → ℝ), s 0 = a ∧ s n = b ∧ Monotone s ∧
      (∀ i < n, s i < s (i + 1)) ∧ (∀ i < n, s (i + 1) - s i < ε) := by
  rcases lt_or_eq_of_le hab with h | h
  · obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / ε)
    have hba : 0 < b - a := sub_pos.mpr h
    have h1 : 0 < (b - a) / ε := div_pos hba hε
    have hnpos : 0 < n := by
      have h2 : (0:ℝ) < n := lt_trans h1 hn
      exact_mod_cast h2
    set c : ℝ := (b - a) / (n:ℝ) with hcdef
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hc : 0 < c := by rw [hcdef]; exact div_pos hba hnR
    have hbasel : b - a < (n:ℝ) * ε := (div_lt_iff₀ hε).mp hn
    have hcε : c < ε := by
      rw [hcdef, div_lt_iff₀ hnR]
      linarith [mul_comm (n:ℝ) ε]
    refine ⟨n, fun i => a + (i:ℝ) * c, by simp, ?_, ?_, ?_, ?_⟩
    · have hnc : (n:ℝ) * c = b - a := by rw [hcdef]; field_simp
      show a + (n:ℝ) * c = b
      linarith
    · intro i j hij
      have hij' : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
      have := mul_le_mul_of_nonneg_right hij' (le_of_lt hc)
      linarith
    · intro i _
      have hi : (i:ℝ) < ((i+1:ℕ):ℝ) := by push_cast; linarith
      have := mul_lt_mul_of_pos_right hi hc
      push_cast at this ⊢
      linarith
    · intro i _
      have hval : (a + (((i+1:ℕ):ℝ)) * c) - (a + (i:ℝ) * c) = c := by
        push_cast; ring
      rw [hval]; exact hcε
  · subst h
    exact ⟨0, fun _ => a, rfl, rfl, monotone_const,
      by intro i hi; omega, by intro i hi; omega⟩

end Commons.Topology.Interval