import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_helpers
import Submission.Work.LinnikBurgess.frame_count_prov_aux.bsum_expansion
import Submission.Work.LinnikBurgess.frame_count_prov_aux.masterSum_eq_masterSum2
import Submission.Work.LinnikBurgess.sumSqrtGcd_Icc_le_aux
import Submission.Work.LinnikBurgess.sum_sqrtGcd_Icc_le

/-!
# Case S of the frame count: the "collapsed" sum

In Case S the two non-pivot entries of the first triple coincide (`a 1 = a 2 = s`).  Writing
`α = x0 = a 0` for the pivot, `g ∣ contAB a b` forces `g ∣ ∏_k |α - b k|`
(`contAB_dvd_prod_del`), the condition `DLd d a b` is *dropped*, and the weight is
`(wg m α s)^2 · ∏_k wg m α (b k)` (`wtAB_caseS`).

This file sets up the two building blocks of the resulting relaxed sum:

* `Ss H m α = ∑_{s ∈ [1,H], s ≠ α} (wg m α s)^2`, the (collapsed) `x`-weight;
* `Ys H m g α = ∑_{y ∈ [1,H]^3} [∀l, y l ≠ α] [g ∣ ∏_k |α - y k|] ∏_k wg m α (y k)`.

The main estimate of §Case S is
`sum2 H m d g CaseS ≤ ∑_{α ∈ [1,H]} Ss H m α * Ys H m g α`
(`caseS_collapse`), with the two factors bounded by `H τ(m)` (`caseS_ss_le`) and
`τ(g)^2 H^3 τ(m)^3 / g` (`caseS_ys_le`).
-/

open scoped BigOperators

namespace Work.ZeroFreeTables.P9F

open Classical
open Work.LinnikBurgess

/-- The `s`-sum of Case S for a fixed pivot `α = x0`: `∑_{s ∈ [1,H], s ≠ α} (wg m α s)^2`. -/
noncomputable def Ss (H m : ℕ) (α : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 H, (if s ≠ α then (wg m α s) ^ 2 else 0)

/-- The `y`-sum of Case S for a fixed pivot `α = x0`. -/
noncomputable def Ys (H m g : ℕ) (α : ℕ) : ℝ :=
  ∑ y ∈ box3 H,
    (if (∀ l : Fin 3, y l ≠ α) ∧ g ∣ ∏ k : Fin 3, del α (y k)
      then ∏ k : Fin 3, wg m α (y k) else 0)

lemma Ss_nonneg (H m : ℕ) (α : ℕ) : 0 ≤ Ss H m α := by
  unfold Ss
  refine Finset.sum_nonneg fun s _ => ?_
  by_cases h : s ≠ α
  · rw [if_pos h]; positivity
  · rw [if_neg h]

lemma Ys_nonneg (H m g : ℕ) (α : ℕ) : 0 ≤ Ys H m g α := by
  unfold Ys
  refine Finset.sum_nonneg fun y _ => ?_
  by_cases h : (∀ l : Fin 3, y l ≠ α) ∧ g ∣ ∏ k : Fin 3, del α (y k)
  · rw [if_pos h]
    exact Finset.prod_nonneg fun k _ => wg_nonneg m α (y k)
  · rw [if_neg h]

/-- `Ss` as a sum of `gcd`'s. -/
lemma Ss_eq_gcd_sum (H m : ℕ) (α : ℕ) :
    Ss H m α = ∑ s ∈ (Finset.Icc 1 H).filter (fun s => s ≠ α),
      ((Nat.gcd m (del α s) : ℕ) : ℝ) := by
  rw [Ss, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s ≠ α
  · rw [if_pos h, if_pos h, wg_sq]
  · rw [if_neg h, if_neg h]

/-- The inner triple sum of `sum2` in `box3` form. -/
lemma sum_iterate3_eq_box3 (H : ℕ) (F : (Fin 3 → ℕ) → ℝ) :
    (∑ y0 ∈ Finset.Icc 1 H, ∑ y1 ∈ Finset.Icc 1 H, ∑ y2 ∈ Finset.Icc 1 H,
        F ![y0, y1, y2])
      = ∑ y ∈ box3 H, F y :=
  (Work.LinnikBurgess.sum_piFinset_fin3 (Finset.Icc 1 H) F).symm

/-- `sum2` with the `b`-sum written as a sum over the box. -/
lemma sum2_eq_box3 (H m d g : ℕ) (P : (Fin 3 → ℕ) → (Fin 3 → ℕ) → Prop) :
    sum2 H m d g P
      = ∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          ∑ y ∈ box3 H,
            (if condAB d g ![x0, x1, x2] y ∧ P ![x0, x1, x2] y
              then wtAB m ![x0, x1, x2] y else 0) := by
  unfold sum2
  refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun x2 _ => ?_
  exact (Work.LinnikBurgess.sum_piFinset_fin3 (Finset.Icc 1 H)
    (fun y => (if condAB d g ![x0, x1, x2] y ∧ P ![x0, x1, x2] y
      then wtAB m ![x0, x1, x2] y else 0))).symm

end Work.ZeroFreeTables.P9F
