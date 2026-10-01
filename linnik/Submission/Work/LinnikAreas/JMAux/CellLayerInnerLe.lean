import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.JMAux.GeomIndicatorSum
import Submission.Work.LinnikAreas.JMAux.CellLayerTermLe

/-!
# The inner `k`-sum of the far-mass decomposition, for exponent `A ≤ 1/2`

`CellLayerInnerLe` bounds the dyadic `k`-sum
`∑_k (1/4)^k · cellLayer R m k · (q·2^k)^A` for `A ≤ 1/2` by `2 q^A R^{-3/2}`.

The proof splits into two independent ingredients:

* `CellLayerTermLe` (pointwise): either `cellLayer R m k = 0` (so the term vanishes), or
  `R ≤ 2^k ∧ m ≤ 2^k` and the term equals `q^A · 2^{k(A-2)} ≤ q^A · (2^k)^{-3/2}`, using
  `A ≤ 1/2`;
* `GeomIndicatorSum` (sum-level): `∑_{k<N, 2^k ≥ R} (2^k)^{-3/2} ≤ 2 R^{-3/2}`, because the
  first admissible `k` already gives `(2^k)^{-3/2} ≤ R^{-3/2}` and the remaining tail is a
  geometric series with ratio `2^{-3/2} < 1/2`, summing to at most `2`.

The assembly multiplies the pointwise bound by the sum bound and factors out `q^A`.
-/

namespace Work.LinnikAreas.JMAux

open scoped BigOperators

lemma CellLayerInnerLe (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (hR : 1 ≤ R) (N m : ℕ) {A : ℝ}
    (hA : A ≤ 1/2) :
    (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
        * ((q:ℝ) * (2:ℝ)^k) ^ A)
      ≤ 2 * (q:ℝ)^A * (R:ℝ)^(-(3/2:ℝ)) := by
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  calc (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
        * ((q:ℝ) * (2:ℝ)^k) ^ A)
      ≤ ∑ k ∈ Finset.range N,
          (q:ℝ)^A * (if (R:ℝ) ≤ (2:ℝ)^k then ((2:ℝ) ^ (-(3/2:ℝ)))^k else 0) :=
        Finset.sum_le_sum (fun k _ => CellLayerTermLe q R m k hA)
    _ = (q:ℝ)^A * ∑ k ∈ Finset.range N,
          (if (R:ℝ) ≤ (2:ℝ)^k then ((2:ℝ) ^ (-(3/2:ℝ)))^k else 0) := by
        rw [Finset.mul_sum]
    _ ≤ (q:ℝ)^A * (2 * (R:ℝ) ^ (-(3/2:ℝ))) :=
        mul_le_mul_of_nonneg_left (GeomIndicatorSum R hR N) (Real.rpow_nonneg hq0 A)
    _ = 2 * (q:ℝ)^A * (R:ℝ)^(-(3/2:ℝ)) := by ring

end Work.LinnikAreas.JMAux
