import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBoxFock.NormEqKcast
import Submission.Work.BoseBoxFock.ShellCard
import Submission.Work.BoseBoxFock.ShellTermLe
import Submission.Work.BoseBoxFock.SumRangeInvSqLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Finset

noncomputable section

/-- The fiber of `K` over `k` is contained in the `k`-th shell. -/
lemma fiber_subset_shell (M k : ℕ) (hk : 1 ≤ k) :
    (box M).filter (fun m => K m = k) ⊆ shell k := by
  intro m hm
  rw [mem_filter] at hm
  obtain ⟨_, hK⟩ := hm
  rw [shell, mem_sdiff]
  exact ⟨mem_box_of_K_eq m k hK, not_mem_box_pred_of_K_eq hk hK⟩

lemma card_fiber_le (M k : ℕ) (hk : 1 ≤ k) :
    ((box M).filter (fun m => K m = k)).card ≤ 24 * k ^ 2 + 2 :=
  le_trans (card_le_card (fiber_subset_shell M k hk)) (ShellCard hk)

/-- The sum over a fiber, when the fiber carries no contributing term. -/
lemma fiber_sum_eq_zero (M k : ℕ) (hk : ¬ 2 ≤ k) :
    (∑ m ∈ (box M).filter (fun m => K m = k),
        (if 2 ≤ K m then ((K m : ℝ) - 1) ^ (-(4 : ℝ)) else 0)) = 0 := by
  refine Finset.sum_eq_zero (fun m hm => ?_)
  rw [mem_filter] at hm
  rw [hm.2, if_neg hk]

/-- The sum over one fiber, in the regime `2 ≤ k`. -/
lemma fiber_sum_le (M k : ℕ) (hk : 2 ≤ k) :
    (∑ m ∈ (box M).filter (fun m => K m = k),
        (if 2 ≤ K m then ((K m : ℝ) - 1) ^ (-(4 : ℝ)) else 0))
      ≤ 98 * ((k : ℝ) - 1) ^ (-(2 : ℝ)) := by
  have hconst : ∀ m ∈ (box M).filter (fun m => K m = k),
      (if 2 ≤ K m then ((K m : ℝ) - 1) ^ (-(4 : ℝ)) else 0)
        = ((k : ℝ) - 1) ^ (-(4 : ℝ)) := by
    intro m hm
    rw [mem_filter] at hm
    rw [hm.2, if_pos hk]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (((box M).filter (fun m => K m = k)).card : ℝ) ≤ 24 * (k : ℝ) ^ 2 + 2 :=
    by
      have h := card_fiber_le M k (show 1 ≤ k by omega)
      exact_mod_cast h
  have hbase : 0 ≤ ((k : ℝ) - 1) ^ (-(4 : ℝ)) := by
    apply Real.rpow_nonneg
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    linarith
  calc (((box M).filter (fun m => K m = k)).card : ℝ) * ((k : ℝ) - 1) ^ (-(4 : ℝ))
      ≤ (24 * (k : ℝ) ^ 2 + 2) * ((k : ℝ) - 1) ^ (-(4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hbase
    _ ≤ 98 * ((k : ℝ) - 1) ^ (-(2 : ℝ)) := ShellTermLe k hk

/-- The sum over the box `[-M,M]³`. -/
lemma box_sum_le (M : ℕ) :
    (∑ m ∈ box M, (if 2 ≤ K m then ((K m : ℝ) - 1) ^ (-(4 : ℝ)) else 0)) ≤ 197 := by
  have hmaps : ∀ m ∈ box M, K m ∈ Finset.range (M + 1) := by
    intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (K_le_of_mem_box m M hm)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun m => (if 2 ≤ K m then ((K m : ℝ) - 1) ^ (-(4 : ℝ)) else 0))]
  rw [Finset.sum_range_succ']
  rw [fiber_sum_eq_zero M 0 (by norm_num)]
  simp only [add_zero]
  calc (∑ j ∈ Finset.range M,
        (∑ m ∈ (box M).filter (fun m => K m = (j + 1)),
          (if 2 ≤ K m then ((K m : ℝ) - 1) ^ (-(4 : ℝ)) else 0)))
      ≤ ∑ j ∈ Finset.range M,
          (if 2 ≤ j + 1 then 98 * ((((j : ℕ) + 1 : ℕ) : ℝ) - 1) ^ (-(2 : ℝ)) else 0) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        by_cases h : 2 ≤ j + 1
        · rw [if_pos h]
          exact fiber_sum_le M (j + 1) h
        · rw [if_neg h]
          exact le_of_eq (fiber_sum_eq_zero M (j + 1) h)
    _ = ∑ j ∈ Finset.range M, (if 1 ≤ j then 98 * ((j : ℝ)) ^ (-(2 : ℝ)) else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hcond : (2 ≤ j + 1) ↔ (1 ≤ j) := by omega
        have hcast : ((((j : ℕ) + 1 : ℕ) : ℝ) - 1) = (j : ℝ) := by push_cast; ring
        rw [hcast]
        by_cases h : 1 ≤ j
        · rw [if_pos (hcond.mpr h), if_pos h]
        · rw [if_neg (mt hcond.mp h), if_neg h]
    _ ≤ ∑ j ∈ Finset.range M, 98 * (1 / ((j : ℝ) ^ 2)) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        by_cases h : 1 ≤ j
        · rw [if_pos h]
          have hj : (0 : ℝ) < (j : ℝ) := by exact_mod_cast h
          rw [Real.rpow_neg (le_of_lt hj) 2, Real.rpow_ofNat, inv_eq_one_div]
        · rw [if_neg h]
          have hj0 : j = 0 := by omega
          subst hj0
          norm_num
    _ = 98 * ∑ j ∈ Finset.range M, (1 / ((j : ℝ) ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ 98 * 2 := mul_le_mul_of_nonneg_left (SumRangeInvSqLe M) (by norm_num)
    _ ≤ 197 := by norm_num

theorem lattice_sum_inv_fourth_le (u : Finset (Fin 3 → ℤ)) :
    (∑ m ∈ u, if 2 ≤ ‖m‖ then (‖m‖ - 1) ^ (-(4 : ℝ)) else 0) ≤ 200 := by
  have hsub : u ⊆ box (u.sup K) := by
    intro m hm
    rw [mem_box_iff]
    intro i
    exact le_trans (K_spec m i) (Finset.le_sup hm)
  calc (∑ m ∈ u, if 2 ≤ ‖m‖ then (‖m‖ - 1) ^ (-(4 : ℝ)) else 0)
      ≤ ∑ m ∈ box (u.sup K), (if 2 ≤ ‖m‖ then (‖m‖ - 1) ^ (-(4 : ℝ)) else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => ?_)
        by_cases h : 2 ≤ ‖m‖
        · rw [if_pos h]
          apply Real.rpow_nonneg
          linarith
        · rw [if_neg h]
    _ = ∑ m ∈ box (u.sup K),
          (if 2 ≤ K m then ((K m : ℝ) - 1) ^ (-(4 : ℝ)) else 0) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [NormEqKcast m]
        by_cases h : 2 ≤ K m
        · rw [if_pos (by exact_mod_cast h), if_pos h]
        · rw [if_neg (by exact_mod_cast h), if_neg h]
    _ ≤ 197 := box_sum_le (u.sup K)
    _ ≤ 200 := by norm_num

end

end Work.BoseBoxFock
