import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseRowsL.LatticeCoulomb.maxAbsDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.block_sum_le` — the dyadic block bound for
`∑_{n ≠ 0} 1/(1 + ‖n‖⁴)`

The lattice sum `∑_{n ≠ 0} 1/(1 + ‖nvec n‖⁴)` converges, and the cheapest way to see
this (and to get an explicit constant) is to slice the lattice by the dyadic blocks
of the `ℓ^∞`-norm `maxAbs n = max_i |n_i|`:

  `B_k := {n : Nat.log 2 (maxAbs n) = k}  =  {2^k ≤ maxAbs n < 2^{k+1}}`  (for `k ≥ 1`).

Two elementary facts bound the block sum:

* **cardinality**: `maxAbs n < 2^{k+1}` means `|n_i| ≤ 2^{k+1} - 1`, so a block has at most
  `(2·(2^{k+1}-1)+1)³ ≤ (2^{k+2})³ = 2^{3k+6}` elements (any `Finset` of lattice vectors with
  `maxAbs ≤ j` lies in the box `[-j,j]³ ⊆ ℤ³`, which has `(2j+1)³` points — `block_card_le`);
* **weight**: on `B_k` one has `2^k ≤ maxAbs n` (for `k ≥ 1`; for `k = 0` the trivial
  bound `1/(1+A⁴) ≤ 1 = (1/2)^{4·0}` is exactly the same), so
  `1/(1 + maxAbs n⁴) ≤ 2^{-4k} = (1/2)^{4k}` (`inv_one_add_pow_four_le_log`).

Hence `∑_{n ∈ B_k} 1/(1+maxAbs n⁴) ≤ 2^{3k+6}·(1/2)^{4k} = 64·(1/2)^k`, which is the
statement of `block_sum_le`.  Summing the geometric series over `k` gives the uniform
`64·2 = 128` bound: this is the route of `latticeSumFourBound`
(`Submission/Work/BoseRowsL/LatticeCoulomb/latticeSumFourBound.lean`).

The statement is stated for an *arbitrary* `Finset T` (only the `T`-members of the block
count), which is what the consumer needs; no hypothesis on `T` is used.
-/

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

open scoped BigOperators

/-- **Cardinality of an `ℓ^∞`-ball in `ℤ³`.**  Any `Finset` of lattice vectors whose
`ℓ^∞`-norm is at most `j` is contained in the box `[-j,j]³`, which has `(2j+1)³` elements. -/
lemma block_card_le (S : Finset (Fin 3 → ℤ)) (j : ℕ) (hS : ∀ n ∈ S, maxAbs n ≤ j) :
    S.card ≤ (2 * j + 1) ^ 3 := by
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(j : ℤ)) (j : ℤ)) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hi : (n i).natAbs ≤ j := (maxAbs_le_iff n j).mp (hS n hn) i
    have hz : ((n i).natAbs : ℤ) ≤ (j : ℤ) := by exact_mod_cast hi
    constructor
    · have h2 : -(n i) ≤ ((n i).natAbs : ℤ) := by simpa using Int.le_natAbs (a := -(n i))
      linarith
    · exact le_trans Int.le_natAbs hz
  calc S.card ≤ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(j : ℤ)) (j : ℤ))).card :=
        Finset.card_le_card hsub
    _ = (2 * j + 1) ^ 3 := by
        have hc : (Finset.Icc (-(j : ℤ)) (j : ℤ)).card = 2 * j + 1 := by
          rw [Int.card_Icc]; omega
        rw [Fintype.card_piFinset]
        simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The weight bound on a dyadic block.**  `1/(1 + A⁴) ≤ (1/2)^{4·Nat.log 2 A}`:
if `A ≠ 0` then `2^{log A} ≤ A`, so `16^{log A} = (2^{log A})⁴ ≤ A⁴ ≤ 1 + A⁴`; if `A = 0`
the left side is `1` and the right side is `1`. -/
lemma inv_one_add_pow_four_le_log (A : ℕ) :
    1 / (1 + (A : ℝ) ^ 4) ≤ (1 / 2 : ℝ) ^ (4 * Nat.log 2 A) := by
  rcases eq_or_ne A 0 with rfl | hA
  · simp
  · have h2 : (2 : ℝ) ^ Nat.log 2 A ≤ (A : ℝ) := by
      exact_mod_cast (Nat.pow_log_le_self 2 hA)
    have h4 : ((2 : ℝ) ^ Nat.log 2 A) ^ 4 ≤ (A : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h2 4
    have h16 : (16 : ℝ) ^ Nat.log 2 A ≤ 1 + (A : ℝ) ^ 4 := by
      have hcast : (16 : ℝ) ^ Nat.log 2 A = ((2 : ℝ) ^ Nat.log 2 A) ^ 4 := by
        calc (16 : ℝ) ^ (Nat.log 2 A) = ((2 : ℝ) ^ 4) ^ (Nat.log 2 A) := by norm_num
          _ = ((2 : ℝ) ^ (Nat.log 2 A)) ^ 4 := by rw [pow_right_comm]
      rw [hcast]; linarith
    have hg : 1 / (1 + (A : ℝ) ^ 4) ≤ 1 / (16 : ℝ) ^ Nat.log 2 A :=
      one_div_le_one_div_of_le (by positivity) h16
    have hp : (1 : ℝ) / (16 : ℝ) ^ Nat.log 2 A = (1 / 2 : ℝ) ^ (4 * Nat.log 2 A) := by
      calc (1 : ℝ) / (16 : ℝ) ^ (Nat.log 2 A) = ((16 : ℝ) ^ (Nat.log 2 A))⁻¹ := by
            rw [one_div]
        _ = ((16 : ℝ)⁻¹) ^ (Nat.log 2 A) := by rw [inv_pow]
        _ = ((1 / 2 : ℝ) ^ 4) ^ (Nat.log 2 A) := by congr 1; norm_num
        _ = (1 / 2 : ℝ) ^ (4 * Nat.log 2 A) := by rw [← pow_mul]
    exact hg.trans_eq hp

/-- **The block arithmetic.**  `(2^{k+2})³ · (1/2)^{4k} = 64·(1/2)^k` exactly. -/
lemma block_sum_arith (k : ℕ) :
    ((2 : ℝ) ^ (k + 2)) ^ 3 * (1 / 2 : ℝ) ^ (4 * k) ≤ 64 * (1 / 2 : ℝ) ^ k := by
  have h4 : (1 / 2 : ℝ) ^ (4 * k) = ((1 / 2 : ℝ) ^ k) ^ 4 := by
    rw [pow_mul, pow_right_comm]
  have h2 : (2 : ℝ) ^ (k + 2) = 4 * (2 : ℝ) ^ k := by rw [pow_add]; ring
  have hkey : ((2 : ℝ) ^ k) ^ 3 * ((1 / 2 : ℝ) ^ k) ^ 4 = (1 / 2 : ℝ) ^ k := by
    rw [show ((1 / 2 : ℝ) ^ k) ^ 4 = ((1 / 2 : ℝ) ^ k) ^ 3 * (1 / 2 : ℝ) ^ k by ring,
      ← mul_assoc, ← mul_pow]
    have huc : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [huc, one_pow, one_mul]
  have hgoal : (4 * (2 : ℝ) ^ k) ^ 3 * ((1 / 2 : ℝ) ^ k) ^ 4 = 64 * (1 / 2 : ℝ) ^ k := by
    rw [show (4 * (2 : ℝ) ^ k) ^ 3 = 64 * ((2 : ℝ) ^ k) ^ 3 by ring, mul_assoc, hkey]
  rw [h4, h2]
  exact hgoal.le

/-- **The dyadic block bound.**  The part of `T` lying in the `k`-th dyadic block
`{n : Nat.log 2 (maxAbs n) = k}` of the `ℓ^∞`-norm carries total weight at most
`64·(1/2)^k`.  (For `k = 0` the block is `{maxAbs ≤ 1}`, of cardinality at most `27`, and
the same estimate holds with room to spare.) -/
theorem block_sum_le (T : Finset (Fin 3 → ℤ)) (k : ℕ) :
    ∑ n ∈ T.filter (fun n => Nat.log 2 (Work.BoseRowsL.LatticeCoulomb.maxAbs n) = k),
        1 / (1 + (Work.BoseRowsL.LatticeCoulomb.maxAbs n : ℝ) ^ 4) ≤ 64 * (1 / 2 : ℝ) ^ k := by
  classical
  set S := T.filter (fun n => Nat.log 2 (maxAbs n) = k) with hS
  have hlog : ∀ n ∈ S, Nat.log 2 (maxAbs n) = k := fun n hn => (Finset.mem_filter.mp hn).2
  -- Every element of the block satisfies `maxAbs n ≤ 2^{k+1} - 1`.
  have hcard : S.card ≤ (2 ^ (k + 2)) ^ 3 := by
    have hsub : S ⊆ T.filter (fun n => maxAbs n ≤ 2 ^ (k + 1) - 1) := by
      intro n hn
      rw [Finset.mem_filter]
      refine ⟨(Finset.mem_filter.mp hn).1, Nat.le_sub_one_of_lt ?_⟩
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (maxAbs n)
      rwa [hlog n hn] at h
    calc S.card ≤ (T.filter (fun n => maxAbs n ≤ 2 ^ (k + 1) - 1)).card :=
          Finset.card_le_card hsub
      _ ≤ (2 * (2 ^ (k + 1) - 1) + 1) ^ 3 :=
          block_card_le _ _ (fun n hn => (Finset.mem_filter.mp hn).2)
      _ ≤ (2 ^ (k + 2)) ^ 3 := by
          refine Nat.pow_le_pow_left ?_ 3
          have h2 : (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ']
          rw [h2]
          exact Nat.succ_le_iff.mpr (Nat.mul_lt_mul_of_pos_left
            (Nat.sub_one_lt (by positivity : (2 : ℕ) ^ (k + 1) ≠ 0)) (by norm_num))
  -- Every summand is at most `(1/2)^{4k}`.
  have hweight : ∀ n ∈ S, 1 / (1 + (maxAbs n : ℝ) ^ 4) ≤ (1 / 2 : ℝ) ^ (4 * k) := by
    intro n hn
    have h := inv_one_add_pow_four_le_log (maxAbs n)
    rwa [hlog n hn] at h
  have hsum : ∑ n ∈ S, 1 / (1 + (maxAbs n : ℝ) ^ 4)
      ≤ (S.card : ℝ) * (1 / 2 : ℝ) ^ (4 * k) := by
    calc ∑ n ∈ S, 1 / (1 + (maxAbs n : ℝ) ^ 4)
        ≤ ∑ _n ∈ S, (1 / 2 : ℝ) ^ (4 * k) := Finset.sum_le_sum hweight
      _ = S.card • (1 / 2 : ℝ) ^ (4 * k) := Finset.sum_const _
      _ = (S.card : ℝ) * (1 / 2 : ℝ) ^ (4 * k) := by rw [nsmul_eq_mul]
  have hcardR : (S.card : ℝ) ≤ ((2 : ℝ) ^ (k + 2)) ^ 3 := by
    have h : (S.card : ℝ) ≤ (((2 ^ (k + 2)) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcard
    simpa [Nat.cast_pow] using h
  exact hsum.trans
    (le_trans (mul_le_mul_of_nonneg_right hcardR (by positivity)) (block_sum_arith k))

end Work.BoseRowsL.LatticeCoulomb
