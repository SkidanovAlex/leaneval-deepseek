import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.sum_inv_one_add_norm_tail
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.sum_inv_one_add_norm_tail_const` — the sharp-constant tail bound

This is the explicit-constant form of `Work.BoseK15.sum_inv_one_add_norm_tail`:
the sibling states `∃ C, 0 ≤ C ∧ … ≤ C / R^M`, while FS §10 downstream needs the
statement with the *specific* value `C = 128` (the value used by that proof).
The argument is the dyadic annulus decomposition, reproduced here so that the
constant is fixed rather than existentially quantified.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

theorem sum_inv_one_add_norm_tail_const (s M : ℕ) (hM : M + 3 ≤ 2 * s) :
    ∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) ≤ 128 / R ^ M := by
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
