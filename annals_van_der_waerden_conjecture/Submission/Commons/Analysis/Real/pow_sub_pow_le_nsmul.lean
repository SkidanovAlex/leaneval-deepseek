import Mathlib

namespace Commons.Analysis.Real

theorem pow_sub_pow_le_nsmul (a b : ℝ) (n : ℕ) (hb : 0 ≤ b) (hba : b ≤ a) (hn : 1 ≤ n) :
    a ^ n - b ^ n ≤ (n : ℝ) * (a - b) * a ^ (n - 1) := by
  have ha : 0 ≤ a := le_trans hb hba
  have hgeom : a ^ n - b ^ n = (a - b) * ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i) :=
    ((Commute.all a b).mul_geom_sum₂ n).symm
  rw [hgeom]
  have hS : ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i) ≤ (n : ℝ) * a ^ (n - 1) := by
    have hterm : ∀ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i) ≤ a ^ (n - 1) := by
      intro i hi
      have hi_n : i < n := Finset.mem_range.mp hi
      have hile : i ≤ n - 1 := by omega
      have hbpow : b ^ (n - 1 - i) ≤ a ^ (n - 1 - i) :=
        pow_le_pow_left₀ hb hba (n - 1 - i)
      calc a ^ i * b ^ (n - 1 - i)
          ≤ a ^ i * a ^ (n - 1 - i) :=
            mul_le_mul_of_nonneg_left hbpow (pow_nonneg ha i)
        _ = a ^ (i + (n - 1 - i)) := (pow_add a i (n - 1 - i)).symm
        _ = a ^ (n - 1) := by rw [show i + (n - 1 - i) = n - 1 by omega]
    calc ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)
        ≤ ∑ _i ∈ Finset.range n, a ^ (n - 1) := Finset.sum_le_sum hterm
      _ = (n : ℝ) * a ^ (n - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (a - b) * ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)
      ≤ (a - b) * ((n : ℝ) * a ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr hba)
    _ = (n : ℝ) * (a - b) * a ^ (n - 1) := by ring

end Commons.Analysis.Real
