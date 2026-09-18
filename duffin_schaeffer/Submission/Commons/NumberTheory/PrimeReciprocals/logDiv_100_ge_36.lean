import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.PrimeCounting

open scoped BigOperators

namespace Commons.NumberTheory.PrimeReciprocals

/-- The anchoring estimate for the logarithm: for positive natural numbers `p` and `m`,
`Real.log p ≥ Real.log m + (p - m)/p`.

Indeed `log p = log m + log (p/m)` and `log (m/p) ≤ m/p - 1`, so
`log (p/m) ≥ 1 - m/p`, i.e. `log p ≥ log m + 1 - m/p = log m + (p - m)/p`. -/
lemma log_anchor (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    Real.log (m : ℝ) + ((p : ℝ) - (m : ℝ)) / (p : ℝ) ≤ Real.log (p : ℝ) := by
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h : Real.log ((m : ℝ) / (p : ℝ)) ≤ (m : ℝ) / (p : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hm' hp')
  rw [Real.log_div (ne_of_gt hm') (ne_of_gt hp')] at h
  have heq : ((p : ℝ) - (m : ℝ)) / (p : ℝ) = 1 - (m : ℝ) / (p : ℝ) := by
    field_simp
  rw [heq]; linarith

private lemma log_8 : Real.log (8:ℝ) = 3 * Real.log 2 := by
  rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow, Nat.cast_ofNat]

private lemma log_12 : Real.log (12:ℝ) = 2 * Real.log 2 + Real.log 3 := by
  rw [show (12:ℝ) = 2^2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_18 : Real.log (18:ℝ) = Real.log 2 + 2 * Real.log 3 := by
  rw [show (18:ℝ) = 2 * 3^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_20 : Real.log (20:ℝ) = 2 * Real.log 2 + Real.log 5 := by
  rw [show (20:ℝ) = 2^2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_24 : Real.log (24:ℝ) = 3 * Real.log 2 + Real.log 3 := by
  rw [show (24:ℝ) = 2^3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_30 : Real.log (30:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [show (30:ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

private lemma log_32 : Real.log (32:ℝ) = 5 * Real.log 2 := by
  rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow, Nat.cast_ofNat]

private lemma log_36 : Real.log (36:ℝ) = 2 * Real.log 2 + 2 * Real.log 3 := by
  rw [show (36:ℝ) = 2^2 * 3^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, Nat.cast_ofNat]

private lemma log_40 : Real.log (40:ℝ) = 3 * Real.log 2 + Real.log 5 := by
  rw [show (40:ℝ) = 2^3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_45 : Real.log (45:ℝ) = 2 * Real.log 3 + Real.log 5 := by
  rw [show (45:ℝ) = 3^2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_48 : Real.log (48:ℝ) = 4 * Real.log 2 + Real.log 3 := by
  rw [show (48:ℝ) = 2^4 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_54 : Real.log (54:ℝ) = Real.log 2 + 3 * Real.log 3 := by
  rw [show (54:ℝ) = 2 * 3^3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_60 : Real.log (60:ℝ) = 2 * Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [show (60:ℝ) = 2^2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Nat.cast_ofNat]

private lemma log_64 : Real.log (64:ℝ) = 6 * Real.log 2 := by
  rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow, Nat.cast_ofNat]

private lemma log_72 : Real.log (72:ℝ) = 3 * Real.log 2 + 2 * Real.log 3 := by
  rw [show (72:ℝ) = 2^3 * 3^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, Nat.cast_ofNat]
  norm_num

private lemma log_80 : Real.log (80:ℝ) = 4 * Real.log 2 + Real.log 5 := by
  rw [show (80:ℝ) = 2^4 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

private lemma log_81 : Real.log (81:ℝ) = 4 * Real.log 3 := by
  rw [show (81:ℝ) = 3^4 by norm_num, Real.log_pow, Nat.cast_ofNat]

private lemma log_90 : Real.log (90:ℝ) = Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
  rw [show (90:ℝ) = 2 * 3^2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Nat.cast_ofNat]

private lemma log_96 : Real.log (96:ℝ) = 5 * Real.log 2 + Real.log 3 := by
  rw [show (96:ℝ) = 2^5 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Nat.cast_ofNat]

/-- Lower bound for the first Mertens sum over the primes `≤ 100`: `Σ_{p ≤ 100} (log p)/p ≥ 3.36`.
(The true value is `3.36947...`, so the best possible constant here is `3.3694...`; the version
with `3.4` in place of `3.36` is *false* for `≤ 100` and only holds from `101` on.)

Route.  `Nat.primesLE 100 = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97}`
provable by `decide`.  For a prime `p` and a `7`-smooth anchor `m`,
`Real.log p ≥ Real.log m + (p - m)/p` (from `Real.log_div` and `Real.log_le_sub_one_of_pos`
applied to `m/p ≤ 1`).  With `Real.log_two_gt_d9`, `Real.log_three_gt_d9`, `Real.log_five_gt_d9`
and `log 7 ≥ 3 · log 2 - 1/7`, the anchors
`7←8, 11←12, 13←12, 17←18, 19←20, 23←24, 29←30, 31←32, 37←36, 41←40, 43←45, 47←48, 53←54,
59←60, 61←60, 67←64, 71←72, 73←72, 79←80, 83←81, 89←90, 97←96` (and `2←2, 3←3, 5←5`) give the
rational lower bound `3.36722... ≥ 3.36`. -/
theorem logDiv_100_ge_36 : (3.36 : ℝ) ≤ ∑ p ∈ Nat.primesLE 100, Real.log (p : ℝ) / (p : ℝ) := by
  have hprimes : Nat.primesLE 100 =
      ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} : Finset ℕ) := by
    decide
  rw [hprimes]
  -- lower bounds for the logarithms of the small primes
  have h2 : (0.6931471803 : ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
  have h3 : (1.0986122885 : ℝ) ≤ Real.log 3 := le_of_lt Real.log_three_gt_d9
  have h5 : (1.6094379123 : ℝ) ≤ Real.log 5 := le_of_lt Real.log_five_gt_d9
  -- anchored lower bounds for the logarithms of the primes in the range
  have h7 : 3 * Real.log 2 + ((7:ℝ) - 8) / 7 ≤ Real.log (7:ℝ) := by
    have h := log_anchor 7 8 (by norm_num) (by norm_num)
    linarith [h, log_8]
  have h11 : 2 * Real.log 2 + Real.log 3 + ((11:ℝ) - 12) / 11 ≤ Real.log (11:ℝ) := by
    have h := log_anchor 11 12 (by norm_num) (by norm_num)
    linarith [h, log_12]
  have h13 : 2 * Real.log 2 + Real.log 3 + ((13:ℝ) - 12) / 13 ≤ Real.log (13:ℝ) := by
    have h := log_anchor 13 12 (by norm_num) (by norm_num)
    linarith [h, log_12]
  have h17 : Real.log 2 + 2 * Real.log 3 + ((17:ℝ) - 18) / 17 ≤ Real.log (17:ℝ) := by
    have h := log_anchor 17 18 (by norm_num) (by norm_num)
    linarith [h, log_18]
  have h19 : 2 * Real.log 2 + Real.log 5 + ((19:ℝ) - 20) / 19 ≤ Real.log (19:ℝ) := by
    have h := log_anchor 19 20 (by norm_num) (by norm_num)
    linarith [h, log_20]
  have h23 : 3 * Real.log 2 + Real.log 3 + ((23:ℝ) - 24) / 23 ≤ Real.log (23:ℝ) := by
    have h := log_anchor 23 24 (by norm_num) (by norm_num)
    linarith [h, log_24]
  have h29 : Real.log 2 + Real.log 3 + Real.log 5 + ((29:ℝ) - 30) / 29 ≤ Real.log (29:ℝ) := by
    have h := log_anchor 29 30 (by norm_num) (by norm_num)
    linarith [h, log_30]
  have h31 : 5 * Real.log 2 + ((31:ℝ) - 32) / 31 ≤ Real.log (31:ℝ) := by
    have h := log_anchor 31 32 (by norm_num) (by norm_num)
    linarith [h, log_32]
  have h37 : 2 * Real.log 2 + 2 * Real.log 3 + ((37:ℝ) - 36) / 37 ≤ Real.log (37:ℝ) := by
    have h := log_anchor 37 36 (by norm_num) (by norm_num)
    linarith [h, log_36]
  have h41 : 3 * Real.log 2 + Real.log 5 + ((41:ℝ) - 40) / 41 ≤ Real.log (41:ℝ) := by
    have h := log_anchor 41 40 (by norm_num) (by norm_num)
    linarith [h, log_40]
  have h43 : 2 * Real.log 3 + Real.log 5 + ((43:ℝ) - 45) / 43 ≤ Real.log (43:ℝ) := by
    have h := log_anchor 43 45 (by norm_num) (by norm_num)
    linarith [h, log_45]
  have h47 : 4 * Real.log 2 + Real.log 3 + ((47:ℝ) - 48) / 47 ≤ Real.log (47:ℝ) := by
    have h := log_anchor 47 48 (by norm_num) (by norm_num)
    linarith [h, log_48]
  have h53 : Real.log 2 + 3 * Real.log 3 + ((53:ℝ) - 54) / 53 ≤ Real.log (53:ℝ) := by
    have h := log_anchor 53 54 (by norm_num) (by norm_num)
    linarith [h, log_54]
  have h59 : 2 * Real.log 2 + Real.log 3 + Real.log 5 + ((59:ℝ) - 60) / 59 ≤ Real.log (59:ℝ) := by
    have h := log_anchor 59 60 (by norm_num) (by norm_num)
    linarith [h, log_60]
  have h61 : 2 * Real.log 2 + Real.log 3 + Real.log 5 + ((61:ℝ) - 60) / 61 ≤ Real.log (61:ℝ) := by
    have h := log_anchor 61 60 (by norm_num) (by norm_num)
    linarith [h, log_60]
  have h67 : 6 * Real.log 2 + ((67:ℝ) - 64) / 67 ≤ Real.log (67:ℝ) := by
    have h := log_anchor 67 64 (by norm_num) (by norm_num)
    linarith [h, log_64]
  have h71 : 3 * Real.log 2 + 2 * Real.log 3 + ((71:ℝ) - 72) / 71 ≤ Real.log (71:ℝ) := by
    have h := log_anchor 71 72 (by norm_num) (by norm_num)
    linarith [h, log_72]
  have h73 : 3 * Real.log 2 + 2 * Real.log 3 + ((73:ℝ) - 72) / 73 ≤ Real.log (73:ℝ) := by
    have h := log_anchor 73 72 (by norm_num) (by norm_num)
    linarith [h, log_72]
  have h79 : 4 * Real.log 2 + Real.log 5 + ((79:ℝ) - 80) / 79 ≤ Real.log (79:ℝ) := by
    have h := log_anchor 79 80 (by norm_num) (by norm_num)
    linarith [h, log_80]
  have h83 : 4 * Real.log 3 + ((83:ℝ) - 81) / 83 ≤ Real.log (83:ℝ) := by
    have h := log_anchor 83 81 (by norm_num) (by norm_num)
    linarith [h, log_81]
  have h89 : Real.log 2 + 2 * Real.log 3 + Real.log 5 + ((89:ℝ) - 90) / 89 ≤ Real.log (89:ℝ) := by
    have h := log_anchor 89 90 (by norm_num) (by norm_num)
    linarith [h, log_90]
  have h97 : 5 * Real.log 2 + Real.log 3 + ((97:ℝ) - 96) / 97 ≤ Real.log (97:ℝ) := by
    have h := log_anchor 97 96 (by norm_num) (by norm_num)
    linarith [h, log_96]
  -- expand the finite sum and finish by linear arithmetic
  norm_num [Finset.sum_insert]
  linarith [h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31, h37, h41, h43, h47, h53, h59,
    h61, h67, h71, h73, h79, h83, h89, h97]

end Commons.NumberTheory.PrimeReciprocals