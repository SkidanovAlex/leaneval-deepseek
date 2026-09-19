import Mathlib
import Submission.Commons.NumberTheory.Mertens.tsum_primes_eq_sum_rpowDiff

open scoped BigOperators Topology
open Filter

namespace Commons.NumberTheory.Mertens

theorem weightedDiff_telescoping {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun k : ℕ => if 2 ≤ k then
      (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) ((2 : ℝ) ^ (-ε)) := by
  let a : ℕ → ℝ := fun k => (k : ℝ) ^ (-ε)
  have ha0 (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    exact Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ)) (-ε)
  have hdec (k : ℕ) (hk : 2 ≤ k) : a (k + 1) ≤ a k := by
    have hk1 : 1 ≤ k := by omega
    have hd := rpowDiff_nonneg hε hk1
    dsimp [a]
    exact sub_nonneg.mp hd
  have ht : Tendsto a atTop (nhds 0) := by
    dsimp [a]
    exact (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  have hh := hasSum_of_differences (a := a) (ha0 := ha0) (n := 2) (hdec := hdec) (ht := ht)
  simpa [a] using hh

end Commons.NumberTheory.Mertens
