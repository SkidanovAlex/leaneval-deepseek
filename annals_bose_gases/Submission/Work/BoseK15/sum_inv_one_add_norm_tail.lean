import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.annulus_sum_bound
import Submission.Work.BoseK15.annulus_terms_sum_bound
import Submission.Work.BoseK15.exists_pow_mul_gt_norm
import Submission.Work.BoseK15.sum_le_sum_annuli
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.sum_inv_one_add_norm_tail` — the *tail* decay of the box mode sum

The sibling `Work.BoseK15.sum_inv_one_add_norm_le` bounds the *full* lattice sum
`∑_{n} (1 + ‖vec n‖²)^{-s}` by a constant.  FS §10 also needs the **tail form**:
for `M + 3 ≤ 2s`, a lattice set all of whose momenta lie outside the ball of
radius `R ≥ 1` contributes at most `C/R^M`.  This is the statement proved here,
with the explicit constant `C = 128`.

The estimate is the natural one: in three dimensions
`∑_{‖vec n‖ ≥ R} (1 + ‖vec n‖²)^{-s} ≲ R^{3-2s} ≤ R^{-M}`.  Note that a purely
pointwise argument cannot work: for `n` with `‖vec n‖ ≥ R` one only gets
`(1+‖vec n‖²)^{-s} ≤ R^{-M}‖vec n‖^{-(2s-M)}`, and `∑_{n} ‖vec n‖^{-3}` diverges
in `ℤ³`.  The slack `(1 + ρ²) ≥ ρ²` is what makes the series converge, so the
count of lattice points in dyadic shells must be used.

The proof is the dyadic annulus decomposition:

* `exists_pow_mul_gt_norm` — the finite set `S` lies in some dyadic ball
  `‖vec n‖ < 2^(K+1) R`;
* `sum_le_sum_annuli` — hence `S` is covered by the annuli
  `A_k = {n ∈ S | 2^k R ≤ ‖vec n‖ < 2^(k+1) R}`, `k = 0, …, K`, and (the
  summand being nonnegative) the sum over `S` is at most the sum of the annulus
  sums;
* `annulus_sum_bound` — on `A_k` each term is at most `((2^k R)²)^{-s}` and
  `A_k` has at most `(2^(k+1) R/π + 1)³` points (`card_le_of_vec_norm_le`), so
  the `k`-th annulus sum is at most
  `((2^(k+1) R/π) + 1)³ · ((2^k R)²)^{-s}`;
* `annulus_terms_sum_bound` — summing the geometric majorant over `k < K+1`
  gives `128/R^(2s-3)`;
* and `2s - 3 ≥ M` together with `R ≥ 1` upgrades `128/R^(2s-3)` to
  `128/R^M`.

The constant `128` (rather than the sharp volume constant) is an artefact of the
crude lattice count `card_le_of_vec_norm_le`; only existence of a constant is
used downstream.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

theorem sum_inv_one_add_norm_tail (s M : ℕ) (hM : M + 3 ≤ 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) ≤ C / R ^ M := by
  refine ⟨128, by norm_num, ?_⟩
  intro R S hR hS
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hs2 : 2 ≤ s := by omega
  have hMs : M ≤ 2 * s - 3 := by omega
  obtain ⟨K, hK⟩ := exists_pow_mul_gt_norm R hR S
  -- dyadic annulus decomposition + per-annulus bound + geometric summation
  have hstep : (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹)
      ≤ 128 / R ^ (2 * s - 3) := by
    refine le_trans (sum_le_sum_annuli s K R S hR hS hK) ?_
    refine le_trans (Finset.sum_le_sum (fun k _ => annulus_sum_bound s k R _ hR ?_ ?_)) ?_
    · intro n hn
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
    · intro n hn
      exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hn).2)
    · exact annulus_terms_sum_bound s (K + 1) R hR hs2
  -- `R^(2s-3) ≥ R^M` since `R ≥ 1` and `M ≤ 2s-3`
  refine le_trans hstep ?_
  have hfin : (1 : ℝ) / R ^ (2 * s - 3) ≤ 1 / R ^ M :=
    one_div_le_one_div_of_le (pow_pos hRpos M) (pow_le_pow_right₀ hR hMs)
  calc (128 : ℝ) / R ^ (2 * s - 3) = 128 * (1 / R ^ (2 * s - 3)) := by ring
    _ ≤ 128 * (1 / R ^ M) := mul_le_mul_of_nonneg_left hfin (by norm_num)
    _ = 128 / R ^ M := by ring

end Work.BoseK15
