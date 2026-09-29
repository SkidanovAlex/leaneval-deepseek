import Mathlib
import Submission.Work.Haupt.penta_summable_a
import Submission.Work.Haupt.penta_summable_pair
import Submission.Work.Haupt.penta_summable_int
import Submission.Work.Haupt.penta_tail_tendsto

/-!
# Euler's pentagonal number theorem, analytic form

For `‖q‖ < 1`,

`∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2} = ∏_{n ≥ 0} (1 - q^{n+1})`.

The two sides are produced by Mathlib's `Pentagonal.tprod_one_sub_pow`, which gives the
product as the `ℕ`-indexed sum
`∑_{k ≥ 0} (-1)^k (q^{pentagonal (-k)} - q^{pentagonal (k+1)})`
once its five analytic side conditions (nilpotence, summability of the auxiliary summands,
multipliability of the factors, summability of the right hand side, and vanishing of the tail)
are discharged.  What remains is a regrouping of the two-sided sum over `ℤ` into pairs of
consecutive indices:  the pairing used by `tprod_one_sub_pow` is `n = -k, k+1`, and both sides
equal `∑_ℤ pentagonalTerm` because the series is absolutely summable.
-/

open scoped BigOperators

namespace Work.Haupt

noncomputable section

/-- The summand `(-1)^n q^{n(3n-1)/2}` of the two-sided pentagonal series, as a function of the
integer index.  This is definitionally the summand occurring in `pentagonal_analytic`. -/
noncomputable def pentagonalTerm (q : ℂ) (n : ℤ) : ℂ :=
  (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2)

/-- Powers of a complex number of norm `< 1` tend to `0`. -/
lemma isTopologicallyNilpotent_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) :
    IsTopologicallyNilpotent q :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq

/-- `∏_n (1 - q^{n+k+1})` is multipliable; this is `ModularForm.multipliable_one_sub_pow`
shifted by `k`. -/
lemma multipliable_one_sub_pow_shift (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + k + 1)) := by
  have hgeom : Summable (fun m : ℕ => ‖q‖ ^ (m + 1)) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (norm_nonneg q) hq)
  have h : Summable (fun n : ℕ => ‖q‖ ^ ((n + k) + 1)) := (summable_nat_add_iff k).2 hgeom
  have h' : Summable (fun n : ℕ => ‖-q ^ (n + k + 1)‖) := by
    refine h.congr (fun n => ?_)
    rw [norm_neg, norm_pow]
  exact multipliable_one_add_of_summable (f := fun n : ℕ => -q ^ (n + k + 1)) h'

/-- The terms of the two-sided sum group in pairs `(-k, k+1)` into the terms of the
`ℕ`-indexed sum appearing in the pentagonal number theorem. -/
lemma pentagonalTerm_add_neg (q : ℂ) (k : ℕ) :
    pentagonalTerm q (-(k : ℤ)) + pentagonalTerm q ((k : ℤ) + 1) =
      (-1 : ℂ) ^ k * (q ^ pentagonal (-(k : ℤ)) - q ^ pentagonal ((k : ℤ) + 1)) := by
  rw [pentagonalTerm, pentagonalTerm]
  have h1 : (-1 : ℂ) ^ (-(k : ℤ)) = (-1 : ℂ) ^ k := by
    rw [← inv_zpow' (-1 : ℂ) (k : ℤ), inv_neg_one, zpow_natCast]
  have h2 : (-1 : ℂ) ^ ((k : ℤ) + 1) = -((-1 : ℂ) ^ k) := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
    ring
  have he1 : q ^ ((-(k : ℤ)) * (3 * (-(k : ℤ)) - 1) / 2) = q ^ pentagonal (-(k : ℤ)) := by
    rw [← zpow_natCast q (pentagonal (-(k : ℤ))), natCast_pentagonal]
  have he2 : q ^ (((k : ℤ) + 1) * (3 * ((k : ℤ) + 1) - 1) / 2)
      = q ^ pentagonal ((k : ℤ) + 1) := by
    rw [← zpow_natCast q (pentagonal ((k : ℤ) + 1)), natCast_pentagonal]
  rw [h1, h2, he1, he2]
  ring

/-- Regrouping the two-sided pentagonal sum over `ℤ` into the `ℕ`-indexed paired sum used by
`Pentagonal.tprod_one_sub_pow`. -/
lemma pair_tsum_eq_int_tsum (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' k : ℕ, (-1 : ℂ) ^ k *
        (q ^ pentagonal (-(k : ℤ)) - q ^ pentagonal ((k : ℤ) + 1)))
      = ∑' n : ℤ, pentagonalTerm q n := by
  have hsum : Summable (fun n : ℤ => pentagonalTerm q n) := penta_summable_int q hq
  have hneg : Summable (fun n : ℤ => pentagonalTerm q (-n)) := by
    simpa [Function.comp_def, Equiv.neg_apply] using (Equiv.summable_iff (Equiv.neg ℤ)).2 hsum
  rw [← tsum_comp_neg (pentagonalTerm q), ← tsum_nat_add_neg_add_one hneg]
  refine tsum_congr (fun k => ?_)
  rw [neg_neg]
  exact (pentagonalTerm_add_neg q k).symm

/-- **Euler's pentagonal number theorem**, analytic form. -/
theorem pentagonal_analytic (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (3 * k - 1) / 2)) = ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  have hmain : ∏' n : ℕ, (1 - q ^ (n + 1))
      = ∑' k : ℕ, (-1 : ℂ) ^ k *
          (q ^ pentagonal (-(k : ℤ)) - q ^ pentagonal ((k : ℤ) + 1)) :=
    Pentagonal.tprod_one_sub_pow (R := ℂ) (x := q) (isTopologicallyNilpotent_of_norm_lt_one hq)
      (fun k => penta_summable_a q hq k) (fun k => multipliable_one_sub_pow_shift q hq k)
      (penta_summable_pair q hq) (penta_tail_tendsto q hq)
  change (∑' k : ℤ, pentagonalTerm q k) = ∏' n : ℕ, (1 - q ^ (n + 1))
  rw [hmain, pair_tsum_eq_int_tsum q hq]

end

end Work.Haupt
