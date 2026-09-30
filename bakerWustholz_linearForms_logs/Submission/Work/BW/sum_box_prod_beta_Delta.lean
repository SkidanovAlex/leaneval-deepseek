import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.sum_fin_box_eq_sum_piFinset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-- Sums over the box `{t' : Fin q → Fin N // ∀ m, t' m ≤ u m}` equal sums over the product box,
as long as `u m ≤ N` for all `m` and the summand only depends on `t'` through its values. -/
theorem sum_box_prod_beta_Delta {q : ℕ} (t t'' : Fin q → ℕ) (β : Fin q → ℕ → ℂ)
    (hβ : ∀ m e, t m + t'' m < e → β m e = 0) (Z : Fin q → ℂ) :
    (∑ t' ∈ (Finset.univ : Finset (Fin q → Fin ((∑ m, t m) + (∑ m, t'' m) + 1))).filter
        (fun t' => ∑ m, (t' m : ℕ) ≤ ∑ m, t m + ∑ m, t'' m),
        ∏ m, β m (t' m) * Work.BW.Delta (Z m) (t' m))
      = ∏ m, ∑ e ∈ Finset.range (t m + t'' m + 1), β m e * Work.BW.Delta (Z m) e := by
  classical
  -- (1) Discard the box points at which some coordinate exceeds `t m + t'' m`: there `β` vanishes.
  have hstep : (∑ t' ∈ (Finset.univ : Finset (Fin q → Fin ((∑ m, t m) + (∑ m, t'' m) + 1))).filter
        (fun t' => ∑ m, (t' m : ℕ) ≤ ∑ m, t m + ∑ m, t'' m),
        ∏ m, β m (t' m) * Delta (Z m) (t' m))
      = ∑ t' ∈ (Finset.univ : Finset (Fin q → Fin ((∑ m, t m) + (∑ m, t'' m) + 1))).filter
        (fun t' => ∀ m, (t' m : ℕ) ≤ t m + t'' m),
        ∏ m, β m (t' m) * Delta (Z m) (t' m) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · -- the smaller box is contained in the simplex
      intro t' ht'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
      calc ∑ m, (t' m : ℕ) ≤ ∑ m, (t m + t'' m) := Finset.sum_le_sum fun m _ => ht' m
        _ = ∑ m, t m + ∑ m, t'' m := Finset.sum_add_distrib
    · -- off the smaller box, some coordinate exceeds the threshold, so `β` kills the term
      intro t' ht' hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht'
      have hnot' : ¬ (∀ m, (t' m : ℕ) ≤ t m + t'' m) := by
        intro hc
        exact hnot (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc)
      obtain ⟨m, hm⟩ := not_forall.mp hnot'
      have hβm : β m (t' m) = 0 := hβ m (t' m) (by omega)
      exact Finset.prod_eq_zero (Finset.mem_univ m) (by simp [hβm])
  -- (2) Compute the sum over the smaller box as a sum over the product box.
  have hle : ∀ m, t m + t'' m ≤ (∑ m, t m) + (∑ m, t'' m) := by
    intro m
    have h1 := Finset.single_le_sum (s := Finset.univ) (f := fun m => t m + t'' m)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
    rwa [Finset.sum_add_distrib] at h1
  have hbox := sum_fin_box_eq_sum_piFinset (q := q) (t := fun m => t m + t'' m)
    (N := (∑ m, t m) + (∑ m, t'' m)) (g := fun n => ∏ m, β m (n m) * Delta (Z m) (n m)) hle
  -- (3) Assemble.
  rw [hstep, hbox]
  exact (Finset.prod_univ_sum (fun m : Fin q => Finset.range (t m + t'' m + 1))
    (fun m e => β m e * Delta (Z m) e)).symm

end Work.BW
