import Mathlib
import Submission.Work.Main.defs
import Submission.Work.IntLib.chunksAPI
import Submission.Work.Main.chunks.sumPchunkMulPow

/-!
# The chunk-product evaluation: `evalChunks (hcoeff …) b = x * y`

The product of the polynomials of base-`2^b` chunks of `x` and `y` has coefficients
`hcoeff x y b N m` (`pchunk`, `hcoeff` in `Work.Main.defs`), and evaluating that coefficient list
at `2^b` gives back `x * y` when both `x, y < 2 ^ (b * N)`.

The proof is three algebraic steps, the middle one being the Cauchy-product identity for the
truncated chunk polynomials:

* `evalChunksRangeMap` : `evalChunks` of a `range`-indexed list is the weighted sum
  `∑ i < K, f i * 2 ^ (b * i)`;
* `hcoeffRangeSum` : the `hcoeff`-sum rewrites, via the Cauchy product, to the double sum over
  pairs `(i, j)` with `i, j < N` (the guard `i ≤ m` and the vanishing of the padded chunks for
  `j ≥ N` make the truncated sum exact);
* `pairSumMul` : that double sum is the product of the two one-variable sums;
* `sumPchunkMulPow` : each one-variable sum is the corresponding integer, provided it is
  `< 2 ^ (b * N)`.
-/

set_option autoImplicit false

namespace Work.Main.chunks

open Work.Main

/-- `evalChunks` of a `range`-indexed list is the weighted sum `∑ i < K, f i * 2 ^ (b * i)`. -/
theorem evalChunksRangeMap (f : ℕ → ℕ) (K b : ℕ) :
    HvdH.evalChunks ((List.range K).map f) b = ∑ i ∈ Finset.range K, f i * 2 ^ (b * i) := by
  induction K with
  | zero => simp [HvdH.evalChunks]
  | succ K ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, Work.IntLib.evalChunks_append, ih,
        Work.IntLib.evalChunks_singleton, List.length_map, List.length_range,
        Finset.sum_range_succ]
      ring

/-- Cauchy product of two truncated geometric sums, as an iterated double sum. -/
theorem pairSumMul (a c : ℕ → ℕ) (N X : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i * c j * X ^ (i + j))
      = (∑ i ∈ Finset.range N, a i * X ^ i) * (∑ j ∈ Finset.range N, c j * X ^ j) := by
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring

/-- Fixed `i < N`: the inner `m`-sum of the `hcoeff`-sum collapses to the `i`-th row of the
Cauchy product.  Terms with `i > m` are killed by the guard, terms with `m - i ≥ N` by the
padding hypothesis `hc`. -/
theorem innerSum {a c : ℕ → ℕ} {N X i : ℕ} (hi : i < N) (hc : ∀ j, N ≤ j → c j = 0) :
    (∑ m ∈ Finset.range (2 * N - 1), (if i ≤ m then a i * c (m - i) * X ^ m else 0))
      = ∑ j ∈ Finset.range N, a i * c j * X ^ (i + j) := by
  have hle : i ≤ 2 * N - 1 := by omega
  have hsplit : 2 * N - 1 = i + (2 * N - 1 - i) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst : (∑ m ∈ Finset.range i, (if i ≤ m then a i * c (m - i) * X ^ m else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hm' : m < i := Finset.mem_range.mp hm
    rw [if_neg (by omega)]
  rw [hfirst, zero_add]
  have hsimp : ∀ t, (if i ≤ i + t then a i * c (i + t - i) * X ^ (i + t) else 0)
      = a i * c t * X ^ (i + t) := by
    intro t
    rw [if_pos (Nat.le_add_right i t), Nat.add_sub_cancel_left]
  rw [Finset.sum_congr rfl (fun t _ => hsimp t)]
  have hsplit2 : 2 * N - 1 - i = N + (2 * N - 1 - i - N) := by omega
  rw [hsplit2, Finset.sum_range_add]
  have hsec : (∑ s ∈ Finset.range (2 * N - 1 - i - N), a i * c (N + s) * X ^ (i + (N + s))) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    rw [hc (N + s) (Nat.le_add_right N s), mul_zero, zero_mul]
  rw [hsec, add_zero]

/-- The `hcoeff`-sum equals the Cauchy product of the two truncated chunk polynomials. -/
theorem hcoeffRangeSum {a c : ℕ → ℕ} {N X : ℕ} (hc : ∀ j, N ≤ j → c j = 0) :
    (∑ m ∈ Finset.range (2 * N - 1),
        (∑ i ∈ Finset.range N, if i ≤ m then a i * c (m - i) else 0) * X ^ m)
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i * c j * X ^ (i + j) := by
  have hdist : ∀ m, (∑ i ∈ Finset.range N, (if i ≤ m then a i * c (m - i) else 0)) * X ^ m
      = ∑ i ∈ Finset.range N, (if i ≤ m then a i * c (m - i) * X ^ m else 0) := by
    intro m
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i ≤ m
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun m _ => hdist m), Finset.sum_comm]
  exact Finset.sum_congr rfl fun i hi => innerSum (Finset.mem_range.mp hi) hc

/-- Evaluation of the chunk-product coefficients recovers the product. -/
theorem evalChunks_hcoeff {x y b N : ℕ} (hb : 1 ≤ b) (hx : x < 2 ^ (b * N)) (hy : y < 2 ^ (b * N)) :
    HvdH.evalChunks ((List.range (2 * N - 1)).map (hcoeff x y b N)) b = x * y := by
  rw [evalChunksRangeMap]
  have hstep : ∀ m, hcoeff x y b N m * 2 ^ (b * m)
      = (∑ i ∈ Finset.range N, if i ≤ m then pchunk x b N i * pchunk y b N (m - i) else 0)
        * (2 ^ b) ^ m := by
    intro m
    simp only [hcoeff, pow_mul]
  rw [Finset.sum_congr rfl (fun m _ => hstep m),
    hcoeffRangeSum (a := fun i => pchunk x b N i) (c := fun j => pchunk y b N j) (X := 2 ^ b)
      (hc := fun j hj => by rw [pchunk, if_neg (Nat.not_lt.mpr hj)]),
    pairSumMul]
  have hx' : (∑ i ∈ Finset.range N, pchunk x b N i * (2 ^ b) ^ i) = x := by
    have h1 : (∑ i ∈ Finset.range N, pchunk x b N i * (2 ^ b) ^ i)
        = ∑ i ∈ Finset.range N, pchunk x b N i * 2 ^ (b * i) :=
      Finset.sum_congr rfl fun i _ => by rw [pow_mul]
    rw [h1, sumPchunkMulPow, Nat.mod_eq_of_lt hx]
  have hy' : (∑ j ∈ Finset.range N, pchunk y b N j * (2 ^ b) ^ j) = y := by
    have h1 : (∑ j ∈ Finset.range N, pchunk y b N j * (2 ^ b) ^ j)
        = ∑ j ∈ Finset.range N, pchunk y b N j * 2 ^ (b * j) :=
      Finset.sum_congr rfl fun j _ => by rw [pow_mul]
    rw [h1, sumPchunkMulPow, Nat.mod_eq_of_lt hy]
  rw [hx', hy']

end Work.Main.chunks
