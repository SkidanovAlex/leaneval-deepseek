/-
# Elementary estimates for the block decomposition of Corollary `siv`

This module collects the elementary, self-contained estimates underlying the geometry of the block
decomposition of `Submission/Work/KMTAreas/A4/sivDefs.lean`:

* `eval_abs_le_absCoeffSum` — the coefficient bound `|P.eval n| ≤ (∑|coeff|) N^deg` for
  `0 ≤ n ≤ N`;
* `eval_abs_le_winBd`, `eval_sub_self_abs_le_winBd` — the two bounds on `P.eval n` and on the
  shift `P.eval n - n` at the points `0 < n ≤ N` which make the windows of width
  `winBd P N = coefBd P * N^deg` contain the relevant pieces;
* `blkLen_pos`, `blkPiece_support` — positivity of the block length and the support of a block;
* `blkAlpha_beta_gap` — two windows whose indices differ by at least `2` are separated by at least
  `(j - i) N^deg`, which is the form in which the disjointness of the windows is used.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.sivDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

/-- The sum of the absolute values of the coefficients of `P` up to degree `P.natDegree`. -/
def absCoeffSum (P : Polynomial ℤ) : ℤ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j|

/-- `coefBd P` is `absCoeffSum P + 1`. -/
theorem coefBd_cast (P : Polynomial ℤ) : ((coefBd P : ℕ) : ℤ) = absCoeffSum P + 1 := by
  rw [coefBd, absCoeffSum]
  push_cast
  simp

/-- `winBd P N = coefBd P * N ^ deg P` after casting to `ℤ`. -/
theorem winBd_cast (P : Polynomial ℤ) (N : ℕ) :
    ((winBd P N : ℕ) : ℤ) = (coefBd P : ℤ) * (N : ℤ) ^ P.natDegree := by
  rw [winBd]
  push_cast
  ring

/-- `blkLen P N = (2 * coefBd P + 2) * N ^ deg P` after casting to `ℤ`. -/
theorem blkLen_cast (P : Polynomial ℤ) (N : ℕ) :
    ((blkLen P N : ℕ) : ℤ) = (2 * (coefBd P : ℤ) + 2) * (N : ℤ) ^ P.natDegree := by
  rw [blkLen]
  push_cast
  ring

/-- The coefficient bound for the evaluation of `P` at a point `0 ≤ n ≤ N`:
`|P.eval n| ≤ (∑|coeff|) N ^ deg P`. -/
theorem eval_abs_le_absCoeffSum {P : Polynomial ℤ} {N : ℕ} (hN : 1 ≤ N) {n : ℤ}
    (hn0 : 0 ≤ n) (hn2 : n ≤ (N : ℤ)) :
    |P.eval n| ≤ absCoeffSum P * (N : ℤ) ^ P.natDegree := by
  have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  calc |P.eval n|
      = |∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * n ^ j| := by
        rw [Polynomial.eval_eq_sum_range]
    _ ≤ ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j * n ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| * n ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_pow, abs_of_nonneg hn0]
    _ ≤ ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| * (N : ℤ) ^ P.natDegree := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hjle : j ≤ P.natDegree := by
          have := Finset.mem_range.mp hj
          omega
        calc n ^ j ≤ (N : ℤ) ^ j := pow_le_pow_left₀ hn0 hn2 j
          _ ≤ (N : ℤ) ^ P.natDegree := pow_le_pow_right₀ hN1 hjle
    _ = absCoeffSum P * (N : ℤ) ^ P.natDegree := by rw [absCoeffSum, Finset.sum_mul]

/-- `|P.eval n| ≤ winBd P N` for `0 < n ≤ N`. -/
theorem eval_abs_le_winBd {P : Polynomial ℤ} {N : ℕ} (hN : 1 ≤ N) {n : ℤ}
    (hn1 : 0 < n) (hn2 : n ≤ (N : ℤ)) : |P.eval n| ≤ (winBd P N : ℤ) := by
  have hm : (0 : ℤ) ≤ (N : ℤ) ^ P.natDegree := by positivity
  have h := eval_abs_le_absCoeffSum (P := P) hN hn1.le hn2
  rw [winBd_cast, coefBd_cast]
  calc |P.eval n| ≤ absCoeffSum P * (N : ℤ) ^ P.natDegree := h
    _ ≤ (absCoeffSum P + 1) * (N : ℤ) ^ P.natDegree := by
        rw [add_mul, one_mul]
        linarith

/-- `|P.eval n - n| ≤ winBd P N` for `0 < n ≤ N` (the window contains the shift). -/
theorem eval_sub_self_abs_le_winBd {P : Polynomial ℤ} (hP : 1 ≤ P.natDegree) {N : ℕ}
    (hN : 1 ≤ N) {n : ℤ} (hn1 : 0 < n) (hn2 : n ≤ (N : ℤ)) :
    |P.eval n - n| ≤ (winBd P N : ℤ) := by
  have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := le_trans zero_le_one hN1
  have hn_le : n ≤ (N : ℤ) ^ P.natDegree := by
    calc n ≤ (N : ℤ) := hn2
      _ = (N : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℤ) ^ P.natDegree := pow_le_pow_right₀ hN1 hP
  have hm : (0 : ℤ) ≤ (N : ℤ) ^ P.natDegree := by positivity
  have h := eval_abs_le_absCoeffSum (P := P) hN hn1.le hn2
  rw [winBd_cast, coefBd_cast]
  calc |P.eval n - n| ≤ |P.eval n| + |n| := abs_sub _ _
    _ = |P.eval n| + n := by rw [abs_of_nonneg hn1.le]
    _ ≤ absCoeffSum P * (N : ℤ) ^ P.natDegree + (N : ℤ) ^ P.natDegree := add_le_add h hn_le
    _ = (absCoeffSum P + 1) * (N : ℤ) ^ P.natDegree := by ring

/-- The block length is positive. -/
theorem blkLen_pos (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) : 0 < blkLen P N := by
  rw [blkLen]
  exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

/-- The support of the `i`-th block piece. -/
theorem blkPiece_support {P : Polynomial ℤ} {N : ℕ} {g : ℤ → ℂ} {i x : ℤ}
    (h : blkPiece P N g i x ≠ 0) :
    i * (blkLen P N : ℤ) ≤ x ∧ x < (i + 1) * (blkLen P N : ℤ) := by
  rw [blkPiece] at h
  by_cases hc : i * (blkLen P N : ℤ) ≤ x ∧ x < (i + 1) * (blkLen P N : ℤ)
  · exact hc
  · rw [if_neg hc] at h
    exact absurd rfl h

/-- The windows of two blocks whose indices differ by at least `2` are separated by at least
`(j - i) N ^ deg P`: `β_i + (j - i) N^deg ≤ α_j`. -/
theorem blkAlpha_beta_gap (P : Polynomial ℤ) (N : ℕ) :
    ∀ i j : ℤ, i + 2 ≤ j →
      (j - i) * ((N : ℤ) ^ P.natDegree) ≤ blkAlpha P N j - blkBeta P N i := by
  intro i j hij
  have hkey : j - i ≤ (j - i - 1) * (2 * (coefBd P : ℤ) + 2) - 2 * (coefBd P : ℤ) := by
    have h1 : (0 : ℤ) ≤ j - i - 2 := by omega
    have h2 : (0 : ℤ) ≤ 2 * (coefBd P : ℤ) + 1 := by positivity
    nlinarith [mul_nonneg h1 h2]
  have hm : (0 : ℤ) ≤ (N : ℤ) ^ P.natDegree := by positivity
  have hexp : blkAlpha P N j - blkBeta P N i
      = ((j - i - 1) * (2 * (coefBd P : ℤ) + 2) - 2 * (coefBd P : ℤ))
          * (N : ℤ) ^ P.natDegree := by
    rw [blkAlpha, blkBeta, blkLen_cast, winBd_cast]
    ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_right hkey hm

end Work.KMTAreas.A4
