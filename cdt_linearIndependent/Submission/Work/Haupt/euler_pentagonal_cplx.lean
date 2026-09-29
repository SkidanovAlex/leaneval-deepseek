import Mathlib
import Submission.Work.Haupt.pentagonal_prelim
import Submission.Work.Haupt.penta_summable_pair
import Submission.Work.Haupt.penta_tail_tendsto

/-!
# Euler's pentagonal number theorem, `ℕ`-indexed paired form

For `‖q‖ < 1`,

`∏_{n ≥ 1} (1 - q^n) = ∑_{k ≥ 0} (-1)^k (q^{P(-k)} - q^{P(k+1)})`

where `P(n) = n(3n-1)/2` is the generalized pentagonal number (`pentagonal n`).  This is the
specialization to `ℂ` of Mathlib's `Pentagonal.tprod_one_sub_pow`, whose side conditions
(nilpotence of `q`, summability of the auxiliary summands, multipliability of the factors,
summability of the right-hand side and vanishing of the tail) are discharged with the estimates
from `Submission.Work.Haupt.pentagonal_prelim`.
-/

open scoped BigOperators

namespace Work.Haupt

/-- Summability of the auxiliary summands `q^{(k+1)n} ∏_{i=0}^{n}(1 - q^{k+i+1})` of the
pentagonal number theorem, for `‖q‖ < 1`.  The partial products are uniformly bounded by
`exp (‖q‖/(1-‖q‖))` (`norm_prod_range_one_sub_pow_le`), so each summand is dominated by a
geometric term of ratio `‖q‖^{k+1} < 1`. -/
private theorem euler_pentagonal_hsum (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (fun n : ℕ =>
      q ^ ((k + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))) := by
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hrk : ‖q‖ ^ (k + 1) < 1 := pow_lt_one₀ hr0 hq (Nat.succ_ne_zero k)
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => Real.exp (‖q‖ / (1 - ‖q‖)) * (‖q‖ ^ (k + 1)) ^ n) ?_ ?_
  · exact (summable_geometric_of_lt_one (by positivity) hrk).mul_left _
  · intro n
    calc ‖q ^ ((k + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖
        = ‖q‖ ^ ((k + 1) * n) * ‖∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖ := by
          rw [norm_mul, norm_pow]
      _ ≤ ‖q‖ ^ ((k + 1) * n) * Real.exp (‖q‖ / (1 - ‖q‖)) :=
          mul_le_mul_of_nonneg_left (norm_prod_range_one_sub_pow_le hq k n) (by positivity)
      _ = Real.exp (‖q‖ / (1 - ‖q‖)) * (‖q‖ ^ (k + 1)) ^ n := by rw [pow_mul]; ring

/-- The factors `1 - q^{n+k+1}` are multipliable for `‖q‖ < 1`: their norms are summable. -/
private theorem euler_pentagonal_hlhs (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + k + 1)) := by
  have hgeom : Summable (fun n : ℕ => ‖q‖ ^ (n + k + 1)) := by
    refine ((summable_nat_add_iff (k + 1)).mpr
      (summable_geometric_of_lt_one (norm_nonneg q) hq)).congr (fun n => ?_)
    rw [Nat.add_assoc]
  have h2 : Summable (fun n : ℕ => ‖-(q ^ (n + k + 1))‖) := by
    refine hgeom.congr (fun n => ?_)
    rw [norm_neg, norm_pow]
  refine (multipliable_one_add_of_summable (f := fun n : ℕ => -(q ^ (n + k + 1))) h2).congr
    (fun n => ?_)
  ring

theorem euler_pentagonal_cplx (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1))
      = ∑' k : ℕ, (-1) ^ k * (q ^ pentagonal (-(k : ℤ)) - q ^ pentagonal ((k : ℤ) + 1)) := by
  have hx : IsTopologicallyNilpotent q := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  exact Pentagonal.tprod_one_sub_pow (x := q) hx (fun k => euler_pentagonal_hsum q hq k)
    (fun k => euler_pentagonal_hlhs q hq k) (penta_summable_pair q hq)
    (penta_tail_tendsto q hq)

end Work.Haupt
