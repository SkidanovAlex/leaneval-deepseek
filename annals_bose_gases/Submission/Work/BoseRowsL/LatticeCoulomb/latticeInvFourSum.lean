import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseRowsL.LatticeCoulomb.card_filter_maxAbs_le
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
import Submission.Work.BoseRowsL.LatticeCoulomb.maxAbs_cast_le_norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.latticeInvFourSum`

The *uniform* bound

`∑_{n ∈ T} 1/‖nvec n‖^4 ≤ 300`

for an arbitrary finite set `T` of nonzero lattice points of `ℤ³`.  Neither the radius nor the
shape of `T` enters: the full lattice series `∑_{n ≠ 0} 1/‖n‖^4` converges (its value is
`≈ 16.5`), so *any* finite sub-sum is bounded, and `300` is a very generous stand-in for that
limit.

## The proof

Everything is controlled by the `ℓ^∞`-norm `maxAbs n = max_i |n_i|`:

* for `n ≠ 0` one has `‖nvec n‖ ≥ maxAbs n ≥ 1`, hence `1/‖nvec n‖^4 ≤ 1/maxAbs n^4`
  (`invFour_step1`);
* the sum is sliced into the dyadic blocks `{n : Nat.log 2 (maxAbs n) = k}`, i.e.
  `{2^k ≤ maxAbs n < 2^{k+1}}` (`invFour_sum_fiber`, the `sum_fiber_log` template with the
  weight `1/maxAbs^4`);
* the `k`-th block meets the `ℓ^∞`-ball of radius `2^{k+1} − 1` and hence contains at most
  `(2 * (2^{k+1}-1) + 1)^3 ≤ (2^{k+2})^3 = 64 · (2^k)^3` points of `T`
  (`card_filter_maxAbs_le`, `invFour_card_le`), while each of them carries weight at most
  `(1/2^k)^4` (`invFour_term_le`).  Multiplying gives the block bound
  `∑_{block k} 1/maxAbs^4 ≤ 64 · (2^k)^3 · (1/2^k)^4 = 64 · (1/2)^k` (`invFour_block_le`);
* the geometric series sums to `∑_{k ≥ 0} 64·(1/2)^k ≤ 128 ≤ 300` (`invFour_geom_half_le`).
-/

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

open scoped BigOperators

/-- A nonzero lattice vector has `ℓ^∞`-norm at least `1`. -/
lemma invFour_one_le_maxAbs {n : Fin 3 → ℤ} (hn : n ≠ 0) : 1 ≤ maxAbs n := by
  have h0 : maxAbs n ≠ 0 := fun h => hn ((maxAbs_eq_zero_iff n).mp h)
  omega

/-- The pointwise weight bound inside the dyadic block `k`: for `n ≠ 0` with
`Nat.log 2 (maxAbs n) = k` one has `maxAbs n ≥ 2^k`, whence `1/maxAbs n^4 ≤ (1/2^k)^4`. -/
lemma invFour_term_le {n : Fin 3 → ℤ} (hn : n ≠ 0) {k : ℕ}
    (h : Nat.log 2 (maxAbs n) = k) :
    1 / (maxAbs n : ℝ) ^ 4 ≤ (1 / (2 : ℝ) ^ k) ^ 4 := by
  have hne : maxAbs n ≠ 0 := fun h0 => hn ((maxAbs_eq_zero_iff n).mp h0)
  have hge : 2 ^ k ≤ maxAbs n := by
    have hpl := Nat.pow_log_le_self 2 hne
    rw [h] at hpl
    exact hpl
  have h1 : ((2 : ℝ) ^ k) ≤ (maxAbs n : ℝ) := by exact_mod_cast hge
  have h2 : ((2 : ℝ) ^ k) ^ 4 ≤ (maxAbs n : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) h2

/-- The cardinality bound for the `k`-th dyadic block: at most `(2^{k+2})^3`, i.e. at most
`64 · (2^k)^3`, points of `T`. -/
lemma invFour_card_le (T : Finset (Fin 3 → ℤ)) (k : ℕ) :
    ((T.filter (fun n => Nat.log 2 (maxAbs n) = k)).card : ℝ)
      ≤ 64 * ((2 : ℝ) ^ k) ^ 3 := by
  -- The block is contained in the `ℓ^∞`-ball of radius `2^{k+1} - 1`.
  have hsub : T.filter (fun n => Nat.log 2 (maxAbs n) = k)
      ⊆ T.filter (fun n => maxAbs n ≤ 2 ^ (k + 1) - 1) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    have hlt := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (maxAbs n)
    rw [hn.2] at hlt
    exact Nat.le_sub_one_of_lt (by simpa [Nat.succ_eq_add_one] using hlt)
  have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hcard : (T.filter (fun n => Nat.log 2 (maxAbs n) = k)).card
      ≤ (2 ^ (k + 2)) ^ 3 := by
    calc (T.filter (fun n => Nat.log 2 (maxAbs n) = k)).card
        ≤ (T.filter (fun n => maxAbs n ≤ 2 ^ (k + 1) - 1)).card :=
          Finset.card_le_card hsub
      _ ≤ (2 * (2 ^ (k + 1) - 1) + 1) ^ 3 := card_filter_maxAbs_le T (2 ^ (k + 1) - 1)
      _ ≤ (2 ^ (k + 2)) ^ 3 := by
          refine Nat.pow_le_pow_left ?_ 3
          have h2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
            rw [show k + 2 = (k + 1) + 1 by omega, pow_succ']
          omega
  calc ((T.filter (fun n => Nat.log 2 (maxAbs n) = k)).card : ℝ)
      ≤ (((2 ^ (k + 2)) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((2 : ℝ) ^ (k + 2)) ^ 3 := by push_cast; ring
    _ = 64 * ((2 : ℝ) ^ k) ^ 3 := by rw [pow_add]; ring

/-- The block bound: the `k`-th dyadic block contributes at most `64 · (1/2)^k`. -/
lemma invFour_block_le (T : Finset (Fin 3 → ℤ)) (h1 : ∀ n ∈ T, n ≠ 0) (k : ℕ) :
    ∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k), 1 / (maxAbs n : ℝ) ^ 4
      ≤ 64 * (1 / 2 : ℝ) ^ k := by
  have hterm : ∀ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k),
      1 / (maxAbs n : ℝ) ^ 4 ≤ (1 / (2 : ℝ) ^ k) ^ 4 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact invFour_term_le (h1 n hn.1) hn.2
  calc ∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k), 1 / (maxAbs n : ℝ) ^ 4
      ≤ ∑ _n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k), (1 / (2 : ℝ) ^ k) ^ 4 :=
        Finset.sum_le_sum hterm
    _ = ((T.filter (fun n => Nat.log 2 (maxAbs n) = k)).card : ℝ)
          * (1 / (2 : ℝ) ^ k) ^ 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (64 * ((2 : ℝ) ^ k) ^ 3) * (1 / (2 : ℝ) ^ k) ^ 4 :=
        mul_le_mul_of_nonneg_right (invFour_card_le T k) (by positivity)
    _ = 64 * (1 / 2 : ℝ) ^ k := by
        rw [one_div_pow]
        have hX : (2 : ℝ) ^ k ≠ 0 := by positivity
        field_simp
        rw [← mul_pow]
        norm_num

/-- The fiber decomposition of the weight `1/maxAbs^4` over the dyadic blocks: the
weight-`1/maxAbs^4` twin of `sum_fiber_log`. -/
lemma invFour_sum_fiber (T : Finset (Fin 3 → ℤ)) :
    ∑ n ∈ T, 1 / (maxAbs n : ℝ) ^ 4
      = ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs) + 1),
          ∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k), 1 / (maxAbs n : ℝ) ^ 4 := by
  have h : ∀ i ∈ T, Nat.log 2 (maxAbs i) ∈ Finset.range (Nat.log 2 (T.sup maxAbs) + 1) := by
    intro n hn
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (Finset.le_sup hn))
  exact (Finset.sum_fiberwise_of_maps_to h (fun n => 1 / (maxAbs n : ℝ) ^ 4)).symm

/-- The partial geometric sum of `1/2`. -/
lemma invFour_geom_half (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k = 2 - 2 * (1 / 2) ^ K := by
  induction K with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- `∑_{k<K} (1/2)^k ≤ 2`. -/
lemma invFour_geom_half_le (K : ℕ) : ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k ≤ 2 := by
  rw [invFour_geom_half K]
  have h0 : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
  linarith

/-- `1/‖nvec n‖^4 ≤ 1/maxAbs n^4`, termwise. -/
lemma invFour_step1 (T : Finset (Fin 3 → ℤ)) (h1 : ∀ n ∈ T, n ≠ 0) :
    ∑ n ∈ T, 1 / ‖nvec n‖ ^ 4 ≤ ∑ n ∈ T, 1 / (maxAbs n : ℝ) ^ 4 := by
  refine Finset.sum_le_sum fun n hn => ?_
  have hle : (maxAbs n : ℝ) ≤ ‖nvec n‖ := maxAbs_cast_le_norm n
  have h4 : (maxAbs n : ℝ) ^ 4 ≤ ‖nvec n‖ ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hle 4
  have hm : (1 : ℝ) ≤ (maxAbs n : ℝ) := by exact_mod_cast invFour_one_le_maxAbs (h1 n hn)
  exact one_div_le_one_div_of_le (pow_pos (lt_of_lt_of_le one_pos hm) 4) h4

theorem latticeInvFourSum (T : Finset (Fin 3 → ℤ)) (h1 : ∀ n ∈ T, n ≠ 0) :
    ∑ n ∈ T, 1 / ‖nvec n‖ ^ 4 ≤ 300 := by
  calc ∑ n ∈ T, 1 / ‖nvec n‖ ^ 4
      ≤ ∑ n ∈ T, 1 / (maxAbs n : ℝ) ^ 4 := invFour_step1 T h1
    _ = ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs) + 1),
          ∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k), 1 / (maxAbs n : ℝ) ^ 4 :=
        invFour_sum_fiber T
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs) + 1), 64 * (1 / 2 : ℝ) ^ k :=
        Finset.sum_le_sum fun k _ => invFour_block_le T h1 k
    _ = 64 * ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs) + 1), (1 / 2 : ℝ) ^ k := by
        rw [Finset.mul_sum]
    _ ≤ 64 * 2 := mul_le_mul_of_nonneg_left (invFour_geom_half_le _) (by norm_num)
    _ ≤ 300 := by norm_num

end Work.BoseRowsL.LatticeCoulomb
