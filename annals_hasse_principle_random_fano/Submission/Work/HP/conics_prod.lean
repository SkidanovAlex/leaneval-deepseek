import Mathlib
import Submission.Work.HP.Defs

/-!
# The product `∏ (1 - 1/(8p))` over the odd primes tends to `0`

Let `p i = Nat.nth Nat.Prime (i+1)` enumerate the primes `3, 5, 7, 11, …`.  We show that

`k ↦ ∏_{i < k} (1 - 1/(8 p i))` tends to `0`.

The proof is the standard one: since `1 - t ≤ exp(-t)` for `t ≥ 0`,

`∏_{i<k} (1 - 1/(8 p i)) ≤ exp (-(1/8) * ∑_{i<k} 1/p i)`,

and the partial sums of the reciprocals of the primes diverge
(`Nat.Primes.not_summable_one_div`).  The product is squeezed between `0` and a
quantity tending to `0`.

The divergence of `∑_{i<k} 1/p i` is obtained by transferring the non-summability of
`∑_{p prime} 1/p` along the order isomorphism `ℕ ≃o Nat.Primes`, then using the
equivalence `¬ Summable f ↔ Tendsto (partial sums) atTop atTop` for non-negative real
series.
-/

namespace Work.HP

open Filter Finset

section ConicsProd

local instance : Infinite ↥(Set.ofPred Nat.Prime) := Nat.infinite_setOfPred_prime.to_subtype

/-- The order isomorphism between `ℕ` and the primes, given by `Nat.nth Nat.Prime`. -/
private noncomputable def primeEquiv : ℕ ≃ Nat.Primes :=
  (Nat.Subtype.orderIsoOfNat (Set.ofPred Nat.Prime)).toEquiv

private theorem primeEquiv_coe (n : ℕ) :
    ((primeEquiv n : Nat.Primes) : ℕ) = Nat.nth Nat.Prime n :=
  (Nat.nth_apply_eq_orderIsoOfNat Nat.infinite_setOfPred_prime n).symm

/-- The reciprocals of the primes, indexed by `Nat.nth Nat.Prime`, are not summable. -/
private theorem not_summable_nth_prime_inv :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / ((Nat.nth Nat.Prime n : ℕ) : ℝ)) := by
  intro hs
  apply Nat.Primes.not_summable_one_div
  rw [← Equiv.summable_iff primeEquiv]
  refine hs.congr ?_
  intro n
  simp only [Function.comp_apply]
  rw [show ((primeEquiv n : Nat.Primes) : ℝ) = ((Nat.nth Nat.Prime n : ℕ) : ℝ) from by
    rw [primeEquiv_coe]]

/-- The subtracted term `1/(8 p)` of the `i`-th factor, `p` running over the odd primes. -/
private noncomputable def u (i : ℕ) : ℝ := 1 / (8 * ((Nat.nth Nat.Prime (i + 1) : ℕ) : ℝ))

private theorem nth_succ_ge_three (i : ℕ) : 3 ≤ Nat.nth Nat.Prime (i + 1) := by
  have h := (Nat.nth_le_nth Nat.infinite_setOfPred_prime (k := 1) (n := i + 1)).2 (by omega)
  simpa using h

private theorem u_le_one (i : ℕ) : u i ≤ 1 := by
  rw [u]
  have h3 : (3 : ℝ) ≤ ((Nat.nth Nat.Prime (i + 1) : ℕ) : ℝ) := by
    exact_mod_cast nth_succ_ge_three i
  have hpos : (0 : ℝ) < 8 * ((Nat.nth Nat.Prime (i + 1) : ℕ) : ℝ) := by nlinarith
  rw [div_le_one hpos]
  nlinarith

/-- `log(1-t) ≤ -t` in exponentiated form: the product is bounded by `exp` of minus the sum. -/
private theorem prod_le_exp (k : ℕ) :
    ∏ i ∈ range k, (1 - u i) ≤ Real.exp (-(∑ i ∈ range k, u i)) := by
  have hle : ∏ i ∈ range k, (1 - u i) ≤ ∏ i ∈ range k, Real.exp (-(u i)) := by
    apply Finset.prod_le_prod₀
    · intro i _; linarith [u_le_one i]
    · intro i _; linarith [Real.add_one_le_exp (-(u i))]
  calc ∏ i ∈ range k, (1 - u i) ≤ ∏ i ∈ range k, Real.exp (-(u i)) := hle
    _ = Real.exp (∑ i ∈ range k, -(u i)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(∑ i ∈ range k, u i)) := by rw [Finset.sum_neg_distrib]

/-- The partial sums `∑_{i<k} 1/(8 p_i)` tend to `+∞`. -/
private theorem tendsto_sum_u :
    Tendsto (fun k : ℕ => ∑ i ∈ range k, u i) atTop atTop := by
  have hv : Tendsto (fun N : ℕ => ∑ n ∈ range N,
      (1 : ℝ) / ((Nat.nth Nat.Prime n : ℕ) : ℝ)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => by positivity)).1
      not_summable_nth_prime_inv
  -- Shift the index by one: `∑_{i<k} 1/p_{i+1} = (∑_{n<k+1} 1/p_n) - 1/2`.
  have hw : Tendsto (fun k : ℕ => ∑ i ∈ range k,
      (1 : ℝ) / ((Nat.nth Nat.Prime (i + 1) : ℕ) : ℝ)) atTop atTop := by
    have h2 := Filter.tendsto_atTop_add_const_right atTop (-(1/2 : ℝ))
      (hv.comp (tendsto_add_atTop_nat 1))
    convert h2 using 1
    funext k
    simp only [Function.comp_apply]
    rw [Finset.sum_range_succ', Nat.nth_prime_zero_eq_two]
    norm_num
  -- Then rescale by `1/8`.
  have h3 := hw.const_mul_atTop (show (0 : ℝ) < 1/8 by norm_num)
  convert h3 using 1
  funext k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [u]
  ring_nf

/-- The product of `1 - 1/(8p)` over the first `k` odd primes tends to `0`.
(`Nat.nth Nat.Prime (i+1)` for `i ∈ range k` enumerates `3,5,7,…`.)

Suggested route: `log(1-t) ≤ -t` gives `∏ ≤ exp (-(1/8) Σ_{i<k} 1/p_i)`, and the reciprocal
sum over the primes diverges (`Nat.Primes.not_summable_one_div`); `Nat.nth_mem_of_infinite`
identifies `Nat.nth Nat.Prime (i+1)` as an (odd) prime. -/
theorem conics_prod :
    Filter.Tendsto (fun k : ℕ => ∏ i ∈ Finset.range k,
        (1 - 1 / (8 * ((Nat.nth Nat.Prime (i + 1) : ℕ) : ℝ)))) Filter.atTop (nhds 0) := by
  have hS : Tendsto (fun k : ℕ => ∑ i ∈ range k, u i) atTop atTop := tendsto_sum_u
  have hexp : Tendsto (fun k : ℕ => Real.exp (-(∑ i ∈ range k, u i))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hS)
  show Tendsto (fun k : ℕ => ∏ i ∈ range k, (1 - u i)) atTop (nhds 0)
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hexp
  · exact Finset.prod_nonneg (fun i _ => by linarith [u_le_one i])
  · exact prod_le_exp k

end ConicsProd

end Work.HP
