import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.SepDefs

namespace Work.FIArea4.Vflip.Vfd

/-- Telescoping sum over an integer interval: for `F : ℤ → ℝ` and `m ≤ n`,
`∑_{j ∈ Icc m n} (F (j-1) - F j) = F (m-1) - F n`. -/
lemma dyadic_sum_Icc_telescope (F : ℤ → ℝ) {m n : ℤ} (hmn : m ≤ n) :
    ∑ j ∈ Finset.Icc m n, (F (j - 1) - F j) = F (m - 1) - F n := by
  induction n, hmn using Int.leInduction with
  | base => simp
  | succ k _hk ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (a := m) (b := k) (by omega : m ≤ k + 1),
      Finset.sum_insert (by simp [Finset.mem_Icc]), ih]
    simp only [add_sub_cancel_right]
    ring

/-- The dyadic partition identity: `∑_{j ∈ ℤ} η(v / 2^j) = 1` for `v > 0`, truncated to any
interval `[m, n]` of integers containing the dyadic scale of `v` (i.e. `2^m ≤ v ≤ 2^n`). -/
theorem dyadic_partition_sum (v : ℝ) (hv : 0 < v) (m n : ℤ)
    (hm : (2 : ℝ) ^ m ≤ v) (hn : v ≤ (2 : ℝ) ^ n) :
    ∑ j ∈ Finset.Icc m n, dyadEta (v / (2 : ℝ) ^ j) = 1 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hpow_pos : ∀ j : ℤ, (0 : ℝ) < (2 : ℝ) ^ j := fun j => zpow_pos h2pos j
  -- the core scaling identity `2 * (v / 2^j) = v / 2^{j-1}`
  have hrel : ∀ j : ℤ, (2 : ℝ) * (v / (2 : ℝ) ^ j) = v / (2 : ℝ) ^ (j - 1) := by
    intro j
    rw [show (j - 1 : ℤ) = j + (-1) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      zpow_neg_one]
    field_simp
  have hmn : m ≤ n := by
    have : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n := le_trans hm hn
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
  -- `η` is a difference of consecutive dyadic scale steps, so the sum telescopes
  have hterm : ∀ j : ℤ, dyadEta (v / (2 : ℝ) ^ j) =
      dyadStep (v / (2 : ℝ) ^ (j - 1)) - dyadStep (v / (2 : ℝ) ^ j) := by
    intro j
    unfold dyadEta
    rw [hrel j]
  simp only [hterm]
  rw [dyadic_sum_Icc_telescope (fun j => dyadStep (v / (2 : ℝ) ^ j)) hmn]
  -- the two boundary values: `1` at the lower end, `0` at the upper end
  have h1 : dyadStep (v / (2 : ℝ) ^ (m - 1)) = 1 := by
    apply dyadStep_one_of_le
    have hm1 : (1 : ℝ) ≤ v / (2 : ℝ) ^ m := by
      rw [le_div_iff₀ (hpow_pos m)]; simpa using hm
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * (v / (2 : ℝ) ^ m) := by linarith
      _ = v / (2 : ℝ) ^ (m - 1) := hrel m
  have h0 : dyadStep (v / (2 : ℝ) ^ n) = 0 := by
    apply dyadStep_zero_of_le
    rw [div_le_one (hpow_pos n)]
    exact hn
  rw [h1, h0]; norm_num

end Work.FIArea4.Vflip.Vfd
