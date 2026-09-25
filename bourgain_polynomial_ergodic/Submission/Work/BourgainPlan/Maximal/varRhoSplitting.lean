import Mathlib
import Submission.Work.BourgainPlan.Maximal.rhoVariationDefs
import Submission.Work.BourgainPlan.Maximal.varSeminormDefs
import Submission.Work.BourgainPlan.Maximal.varTwoSplitting

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Minkowski's inequality for the `ρ`-variation chains (clipping).**  The `ℓ^ρ`-length of the
increments of a chain `t` is at most the sum of the `ℓ^ρ`-lengths of the increments of the two
chains obtained by clipping `t` at the threshold `K` from above and from below: `j ↦ min (t j) K`
and `j ↦ max (t j) K`.  This is the min/max splitting identity plus Minkowski's inequality for
`ℓ^ρ`, `ρ ≥ 1` (`Real.Lp_add_le_of_nonneg`). -/
lemma chainLp_le_clip (ρ : ℝ) (hρ : 1 ≤ ρ) (J K : ℕ) (a : ℕ → E) (t : ℕ → ℕ) :
    chainLp ρ J a t
      ≤ chainLp ρ J a (fun j => min (t j) K) + chainLp ρ J a (fun j => max (t j) K) := by
  have hminmax : ∀ m : ℕ, a (min m K) + a (max m K) = a m + a K := by
    intro m
    rcases le_or_gt m K with h | h
    · rw [min_eq_left h, max_eq_right h, add_comm]
    · rw [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h), add_comm]
  have hkey : ∀ j, a (t (j + 1)) - a (t j)
      = (a (min (t (j + 1)) K) - a (min (t j) K))
        + (a (max (t (j + 1)) K) - a (max (t j) K)) := by
    intro j
    calc a (t (j + 1)) - a (t j)
        = (a (t (j + 1)) + a K) - (a (t j) + a K) := by abel
      _ = (a (min (t (j + 1)) K) + a (max (t (j + 1)) K))
            - (a (min (t j) K) + a (max (t j) K)) := by
            rw [← hminmax (t (j + 1)), ← hminmax (t j)]
      _ = (a (min (t (j + 1)) K) - a (min (t j) K))
            + (a (max (t (j + 1)) K) - a (max (t j) K)) := by abel
  have hbound : ∀ j, ‖a (t (j + 1)) - a (t j)‖
      ≤ ‖a (min (t (j + 1)) K) - a (min (t j) K)‖
        + ‖a (max (t (j + 1)) K) - a (max (t j) K)‖ := by
    intro j; rw [hkey j]; exact norm_add_le _ _
  have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ
  have hsum : ∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ ρ
      ≤ ∑ j ∈ Finset.range J,
          (‖a (min (t (j + 1)) K) - a (min (t j) K)‖
            + ‖a (max (t (j + 1)) K) - a (max (t j) K)‖) ^ ρ :=
    Finset.sum_le_sum fun j _ => Real.rpow_le_rpow (norm_nonneg _) (hbound j) hρ0
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ ρ :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _
  have hρinv : 0 ≤ (1 : ℝ) / ρ := by positivity
  calc chainLp ρ J a t
      = (∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ ρ) ^ (1 / ρ) := rfl
    _ ≤ (∑ j ∈ Finset.range J,
          (‖a (min (t (j + 1)) K) - a (min (t j) K)‖
            + ‖a (max (t (j + 1)) K) - a (max (t j) K)‖) ^ ρ) ^ (1 / ρ) :=
        Real.rpow_le_rpow hsum_nonneg hsum hρinv
    _ ≤ (∑ j ∈ Finset.range J, ‖a (min (t (j + 1)) K) - a (min (t j) K)‖ ^ ρ) ^ (1 / ρ)
        + (∑ j ∈ Finset.range J, ‖a (max (t (j + 1)) K) - a (max (t j) K)‖ ^ ρ) ^ (1 / ρ) :=
        Real.Lp_add_le_of_nonneg (Finset.range J) (p := ρ) hρ
          (fun j _ => norm_nonneg _) (fun j _ => norm_nonneg _)
    _ = chainLp ρ J a (fun j => min (t j) K) + chainLp ρ J a (fun j => max (t j) K) := rfl

/-- An admissible chain of `[lo, hi]` is dominated by `varRho ρ lo hi a`. -/
lemma ofReal_chainLp_le_varRho (ρ : ℝ) (lo hi J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) (ht : Monotone t)
    (h : ∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi) :
    ENNReal.ofReal (chainLp ρ J a t) ≤ varRho ρ lo hi a := by
  rw [varRho]
  apply le_iSup_of_le J
  apply le_iSup_of_le t
  apply le_iSup_of_le ht
  apply le_iSup_of_le h
  exact le_rfl

/-- To bound `varRho` above it suffices to bound every admissible chain. -/
lemma varRho_le_of_forall {ρ : ℝ} {lo hi : ℕ} {C : ℝ≥0∞} {a : ℕ → E}
    (h : ∀ J t, Monotone t → (∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi) →
      ENNReal.ofReal (chainLp ρ J a t) ≤ C) :
    varRho ρ lo hi a ≤ C := by
  rw [varRho]
  refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun hh => h J t ht hh

/-- **Splitting the `ρ`-variation at an interior index** (KMSZ arXiv:2606.12663, Definition 5.1,
condition (1)).  The `ρ`-variation of a sequence over an index window is subadditive with respect
to cutting the window at an interior index `K`.  The proof is the same clipping argument as for
`varTwoSplitting` (`Work.BourgainPlan.Maximal.varTwoSplitting`, the case `ρ = 2`): given a
monotone chain `t` with values in `[lo, hi]`, clip it to `j ↦ min (t j) K` and
`j ↦ max (t j) K`, whose increments add up to the increments of `t` (the min/max identity
`a (min m K) + a (max m K) = a m + a K`), and use Minkowski's inequality for `ℓ^ρ`, `ρ ≥ 1`
(for `ρ = 2` this is `sqrt_sum_sq_add_le` of `varTwoSplitting`; for general `ρ` we use
`Real.Lp_add_le_of_nonneg`). -/
theorem varRhoSplitting {E : Type*} [SeminormedAddCommGroup E] {ρ : ℝ} (hρ : 1 ≤ ρ)
    {lo K hi : ℕ} (hlo : lo ≤ K) (hhi : K ≤ hi) (a : ℕ → E) :
    varRho ρ lo hi a ≤ varRho ρ lo K a + varRho ρ K hi a := by
  refine varRho_le_of_forall fun J t ht h => ?_
  have hclip := chainLp_le_clip (E := E) ρ hρ J K a t
  refine le_trans (ENNReal.ofReal_le_ofReal hclip) ?_
  rw [ENNReal.ofReal_add (chainLp_nonneg ρ J a _) (chainLp_nonneg ρ J a _)]
  refine add_le_add ?_ ?_
  · exact ofReal_chainLp_le_varRho ρ lo K J a (fun j => min (t j) K)
      (fun i j hij => min_le_min (ht hij) le_rfl)
      (fun j hj => ⟨le_min (h j hj).1 hlo, min_le_right _ _⟩)
  · exact ofReal_chainLp_le_varRho ρ K hi J a (fun j => max (t j) K)
      (fun i j hij => max_le_max (ht hij) le_rfl)
      (fun j hj => ⟨le_max_right _ _, max_le (h j hj).2 hhi⟩)

end

end Work.BourgainPlan.Maximal
