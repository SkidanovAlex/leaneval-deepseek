import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Ring.Finset
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open scoped BigOperators

/-- For a fixed index `i` of `Fin N`, summing a constant `c` over the `j ≠ i` (i.e. over
`N - 1` values) gives `c * ((N : ℝ) - 1)`. -/
lemma sum_ite_ne_eq (N : ℕ) (i : Fin N) (c : ℝ) :
    (∑ j : Fin N, (if i ≠ j then c else 0)) = c * ((N : ℝ) - 1) := by
  have hN : 1 ≤ N := by
    have := i.isLt
    omega
  have hfilter : (Finset.univ.filter (fun j : Fin N => i ≠ j)) = Finset.univ.erase i := by
    ext j
    simp [Finset.mem_erase, ne_comm]
  have hcard : (Finset.univ.filter (fun j : Fin N => i ≠ j)).card = N - 1 := by
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_sub hN]
  ring

/-- The sum of `g` over the first coordinate of the ordered pair set
`pairSet N = {(i,j) : i ≠ j}` equals `(N - 1) * ∑ i, g i`. -/
theorem sum_pairSet_fst_eq {N : ℕ} (g : Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, g p.1) = ((N : ℝ) - 1) * ∑ i : Fin N, g i := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
  change (∑ x : Fin N, ∑ y : Fin N, (if x ≠ y then g x else 0)) =
    ((N : ℝ) - 1) * ∑ i : Fin N, g i
  simp_rw [sum_ite_ne_eq]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

end Work.BoseFixB1S
