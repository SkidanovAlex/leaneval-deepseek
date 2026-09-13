import Mathlib
import Submission.Commons.Combinatorics.QBinomial.alt_sum_eq_one
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow

namespace Commons.Combinatorics.QBinomial

/-- Crude bound: the number of `k`-dimensional subspaces of `𝔽₂ⁿ` is at most `2 ^ (n * k)`
(for `k ≤ n`). -/
lemma gb_le_two_pow_mul (n k : ℕ) (hk : k ≤ n) : gb n k ≤ 2 ^ (n * k) := by
  have h := Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow
    (K := ZMod 2) (V := Fin n → ZMod 2) k
  have h1 : Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
      Module.finrank (ZMod 2) W = k} ≤ 2 ^ (k * (n - k) + k) := by
    simpa using h
  have hgb : gb n k = Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
      Module.finrank (ZMod 2) W = k} := rfl
  rw [hgb]
  refine le_trans h1 ?_
  apply Nat.pow_le_pow_right (by norm_num)
  have hid : k * (n - k) + k * k = k * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hk]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; simp
  · have hkk : k ≤ k * k := Nat.le_mul_of_pos_left k hkpos
    calc k * (n - k) + k ≤ k * (n - k) + k * k := Nat.add_le_add_left hkk _
      _ = k * n := hid
      _ = n * k := Nat.mul_comm k n

theorem gb_mul_gb_mul_pow_le (i j k : ℕ) (hk : k ≤ i) (hk' : k ≤ j) :
    Commons.Combinatorics.QBinomial.gb i k * Commons.Combinatorics.QBinomial.gb j k * 2 ^ (k * k)
      ≤ 2 ^ ((i + j + k) * k) := by
  have hi : gb i k ≤ 2 ^ (i * k) := gb_le_two_pow_mul i k hk
  have hj : gb j k ≤ 2 ^ (j * k) := gb_le_two_pow_mul j k hk'
  calc gb i k * gb j k * 2 ^ (k * k)
      ≤ 2 ^ (i * k) * 2 ^ (j * k) * 2 ^ (k * k) := by gcongr
    _ = 2 ^ (i * k + j * k) * 2 ^ (k * k) := by rw [← pow_add]
    _ = 2 ^ (i * k + j * k + k * k) := by rw [← pow_add]
    _ = 2 ^ ((i + j + k) * k) := by congr 1; ring

end Commons.Combinatorics.QBinomial
