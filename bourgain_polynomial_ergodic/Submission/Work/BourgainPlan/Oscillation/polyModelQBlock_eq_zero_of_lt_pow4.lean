import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_defs

/-!
# Vanishing of the model's dyadic denominator blocks below the scale `4 ^ m`

`polyModelQBlock P m N θ` collects the `q`-th major-arc terms of the model with
`Nat.log 2 q = m`, for `q ≤ ⌊N^{1/4}⌋`.  A block with index `m` can only be non-empty if some
`q ≥ 2 ^ m` is `≤ N^{1/4}`, i.e. if `N ≥ 2 ^ (4 m)`.  Since `2 ^ (4 m) ≥ 4 ^ m`, the hypothesis
`N < 4 ^ m` forces the block to be empty.

This is the "sharp-scale" vanishing used to restrict the denominator blocks of the model to the
range `4 ^ m ≤ N` (see `polyModelQBlock_eq_zero_of_lt` for the corresponding statement at the
lacunary scales `N = 2 ^ k`, `k < 4 m`).
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Work.BourgainPlan.Oscillation

theorem polyModelQBlock_eq_zero_of_lt_pow4 (P : Polynomial ℤ) {m N : ℕ} (hN : N < 4 ^ m) (θ : ℝ) :
    Work.BourgainPlan.Maximal.polyModelQBlock P m N θ = 0 := by
  -- `4 ^ m ≤ 2 ^ (4 m)` and hence `N < 2 ^ (4 m)`.
  have hle : 4^m ≤ 2^(4*m) := by
    calc (4:ℕ)^m = 2^(2*m) := by rw [show (4:ℕ) = 2^2 by norm_num, pow_mul]
      _ ≤ 2^(4*m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNlt : N < 2^(4*m) := lt_of_lt_of_le hN hle
  -- The fourth root of `2 ^ (4 m)` is exactly `2 ^ m`.
  have hid : (((2^(4*m) : ℕ)) : ℝ)^((1:ℝ)/4) = ((2^m : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    simp only [Nat.cast_ofNat]
    rw [← Real.rpow_natCast (2:ℝ) (4*m), ← Real.rpow_natCast (2:ℝ) m]
    push_cast
    rw [(Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) ((4:ℝ)*(m:ℝ)) ((1:ℝ)/4)).symm]
    rw [show (4:ℝ)*(m:ℝ)*((1:ℝ)/4) = (m:ℝ) by ring]
  -- The denominator cutoff `⌊N^{1/4}⌋` is below `2 ^ m`.
  have hfl : Nat.floor ((N:ℝ)^((1:ℝ)/4)) < 2^m := by
    rw [Nat.floor_lt (Real.rpow_nonneg (by positivity) _)]
    calc (N:ℝ)^((1:ℝ)/4) < (((2^(4*m) : ℕ) : ℝ))^((1:ℝ)/4) := by
          refine Real.rpow_lt_rpow (by positivity) ?_ (by norm_num)
          exact_mod_cast hNlt
      _ = ((2^m : ℕ) : ℝ) := hid
  -- Hence no `q` of the `m`-th block survives the cutoff.
  unfold Work.BourgainPlan.Maximal.polyModelQBlock
  have hempty : (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)))).filter
      (fun q => Nat.log 2 q = m) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hq2⟩, hlog⟩ := hq
    have hqlt : q < 2^m := lt_of_le_of_lt hq2 hfl
    have hlt := Nat.log_lt_of_lt_pow (b := 2) (by omega : q ≠ 0) hqlt
    omega
  rw [hempty, Finset.sum_empty]

end Work.BourgainPlan.Oscillation
