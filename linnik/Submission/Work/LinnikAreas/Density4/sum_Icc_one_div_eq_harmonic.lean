import Mathlib

namespace Work.LinnikAreas.Density4

theorem sum_Icc_one_div_eq_harmonic (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ)) = (harmonic M : ℝ) := by
  induction M with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num [harmonic_succ]
    · rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
      push_cast
      ring

end Work.LinnikAreas.Density4
