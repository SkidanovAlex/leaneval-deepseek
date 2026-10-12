import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Ring.Finset
import Submission.Work.BoseFixB1S.sum_pairSet_fst_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- Summing the two coordinate projections of `g` over the ordered pair set
`pairSet N = {(i,j) : i ≠ j}`: each coordinate contributes
`((N : ℝ) - 1) * ∑ i, g i`, because for a fixed `i` the index `i` occurs as a first (resp.
second) coordinate in exactly `N - 1` ordered pairs.  The auxiliary `have` below is the
`second coordinate` half; it is stated locally to avoid clashing with the identically named
`Work.BoseFixB1S.sum_pairSet_snd_eq` living in `Submission/Work/BoseFixB1S/mfManifestLowerV2B1.lean`. -/
theorem sum_pairSet_add_eq {N : ℕ} (g : Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, (g p.1 + g p.2))
      = 2 * ((N : ℝ) - 1) * ∑ i : Fin N, g i := by
  have hsnd : (∑ p ∈ Submission.BoseGases.pairSet N, g p.2)
      = ((N : ℝ) - 1) * ∑ i : Fin N, g i := by
    rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
    change (∑ x : Fin N, ∑ y : Fin N, (if x ≠ y then g y else 0))
      = ((N : ℝ) - 1) * ∑ i : Fin N, g i
    rw [Finset.sum_comm]
    have h : ∀ y : Fin N, (∑ x : Fin N, (if x ≠ y then g y else 0)) = g y * ((N : ℝ) - 1) := by
      intro y
      rw [← sum_ite_ne_eq N y (g y)]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [if_pos hxy, if_pos (Ne.symm hxy)]
    simp_rw [h]
    rw [← Finset.sum_mul]
    exact mul_comm _ _
  rw [Finset.sum_add_distrib, sum_pairSet_fst_eq g, hsnd]
  ring

end Work.BoseFixB1S
