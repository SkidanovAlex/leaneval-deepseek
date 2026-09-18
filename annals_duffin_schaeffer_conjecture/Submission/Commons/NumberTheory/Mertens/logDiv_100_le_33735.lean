import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.PrimeCounting

open scoped BigOperators

namespace Commons.NumberTheory.Mertens

/-- Upper bound for the logarithm of a prime via a `{2,3,5}`-smooth anchor `m`:
`log p ≤ a·log 2 + b·log 3 + c·log 5 + (p - m)/m`.

Indeed `log p = log m + log (p/m)` and `log x ≤ x - 1`, so
`log (p/m) ≤ p/m - 1 = (p - m)/m`.  -/
private lemma logprime_le_upper (p m a b c : ℕ) (hm : 2^a * 3^b * 5^c = m) (hm2 : 0 < m)
    (hp : 0 < p) :
    Real.log (p : ℝ) ≤
      a * (0.6931471808 : ℝ) + b * 1.0986122888 + c * 1.6094379126 + ((p : ℝ) - m) / m := by
  have h2 : Real.log (2 : ℝ) ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  have h3 : Real.log (3 : ℝ) ≤ 1.0986122888 := le_of_lt Real.log_three_lt_d9
  have h5 : Real.log (5 : ℝ) ≤ 1.6094379126 := le_of_lt Real.log_five_lt_d9
  have hcast : (((2^a * 3^b * 5^c : ℕ)) : ℝ) = (2 : ℝ)^a * (3 : ℝ)^b * (5 : ℝ)^c := by
    push_cast; ring
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm2
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogm : Real.log (m : ℝ) ≤
      a * 0.6931471808 + b * 1.0986122888 + c * 1.6094379126 := by
    rw [← hm, hcast,
      show (2 : ℝ)^a * (3 : ℝ)^b * (5 : ℝ)^c = ((2 : ℝ)^a * (3 : ℝ)^b) * (5 : ℝ)^c from by ring,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    nlinarith [h2, h3, h5, (Nat.cast_nonneg a : (0 : ℝ) ≤ (a : ℝ)),
      (Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ)), (Nat.cast_nonneg c : (0 : ℝ) ≤ (c : ℝ))]
  have hquot : Real.log ((p : ℝ) / (m : ℝ)) ≤ (p : ℝ) / (m : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hp0) (ne_of_gt hm0)] at hquot
  have heq : ((p : ℝ) - m) / m = (p : ℝ) / (m : ℝ) - 1 := by
    rw [sub_div, div_self (ne_of_gt hm0)]
  rw [heq]
  linarith

theorem logDiv_100_le_33735 :
    (∑ p ∈ Nat.primesLE 100, Real.log (p : ℝ) / (p : ℝ)) ≤ 3.3735 := by
  have hprimes : Nat.primesLE 100 =
      ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} :
        Finset ℕ) := by
    decide
  rw [hprimes]
  have h2 : Real.log (2 : ℝ) ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  have h3 : Real.log (3 : ℝ) ≤ 1.0986122888 := le_of_lt Real.log_three_lt_d9
  have h5 : Real.log (5 : ℝ) ≤ 1.6094379126 := le_of_lt Real.log_five_lt_d9
  have h7 : Real.log (7 : ℝ) ≤ 1.9544415424 := by
    have h := logprime_le_upper 7 8 3 0 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h11 : Real.log (11 : ℝ) ≤ 2.4015733171 := by
    have h := logprime_le_upper 11 12 2 1 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h13 : Real.log (13 : ℝ) ≤ 2.5682399838 := by
    have h := logprime_le_upper 13 12 2 1 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h17 : Real.log (17 : ℝ) ≤ 2.8348162029 := by
    have h := logprime_le_upper 17 18 1 2 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h19 : Real.log (19 : ℝ) ≤ 2.9457322742 := by
    have h := logprime_le_upper 19 20 2 0 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h23 : Real.log (23 : ℝ) ≤ 3.1363871646 := by
    have h := logprime_le_upper 23 24 3 1 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h29 : Real.log (29 : ℝ) ≤ 3.3678640489 := by
    have h := logprime_le_upper 29 30 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h31 : Real.log (31 : ℝ) ≤ 3.434485904 := by
    have h := logprime_le_upper 31 32 5 0 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h37 : Real.log (37 : ℝ) ≤ 3.611296717 := by
    have h := logprime_le_upper 37 36 2 2 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h41 : Real.log (41 : ℝ) ≤ 3.713879455 := by
    have h := logprime_le_upper 41 40 3 0 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h43 : Real.log (43 : ℝ) ≤ 3.7622180458 := by
    have h := logprime_le_upper 43 45 0 2 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h47 : Real.log (47 : ℝ) ≤ 3.8503676787 := by
    have h := logprime_le_upper 47 48 4 1 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h53 : Real.log (53 : ℝ) ≤ 3.9704655287 := by
    have h := logprime_le_upper 53 54 1 3 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h59 : Real.log (59 : ℝ) ≤ 4.0776778964 := by
    have h := logprime_le_upper 59 60 2 1 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h61 : Real.log (61 : ℝ) ≤ 4.1110112297 := by
    have h := logprime_le_upper 61 60 2 1 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h67 : Real.log (67 : ℝ) ≤ 4.2057580848 := by
    have h := logprime_le_upper 67 64 6 0 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h71 : Real.log (71 : ℝ) ≤ 4.2627772312 := by
    have h := logprime_le_upper 71 72 3 2 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h73 : Real.log (73 : ℝ) ≤ 4.2905550089 := by
    have h := logprime_le_upper 73 72 3 2 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h79 : Real.log (79 : ℝ) ≤ 4.3695266358 := by
    have h := logprime_le_upper 79 80 4 0 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h83 : Real.log (83 : ℝ) ≤ 4.4191405133 := by
    have h := logprime_le_upper 83 81 0 4 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h89 : Real.log (89 : ℝ) ≤ 4.4886985599 := by
    have h := logprime_le_upper 89 90 1 2 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  have h97 : Real.log (97 : ℝ) ≤ 4.5747648595 := by
    have h := logprime_le_upper 97 96 5 1 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h; linarith
  norm_num [Finset.sum_insert]
  linarith [h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31, h37, h41, h43, h47, h53, h59,
    h61, h67, h71, h73, h79, h83, h89, h97]

end Commons.NumberTheory.Mertens
