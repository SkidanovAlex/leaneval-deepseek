import Mathlib
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs
import Submission.Work.BourgainPlan.Maximal.varRhoSplitting

/-!
# Gluing the `ρ`-variation at a threshold

The `ρ`-variation over the whole index range `[0,∞)` is bounded by the variation over the tail
`[K,∞)` plus the *initial* part, which is controlled by the norms of the values below the
threshold.  Concretely, for `ρ ≥ 1`, `K : ℕ` and `a : ℕ → E`,

  `varRhoAll ρ a ≤ varRhoFrom ρ K a + 4 * Σ_{i ≤ K} ‖a i‖ₑ`.

The two ingredients of the proof are:

* the **splitting** of the window at the interior index `K` (`varRhoSplitting`),
  `varRho ρ 0 hi a ≤ varRho ρ 0 K a + varRho ρ K hi a`,
  applied with `hi` replaced by `max hi K` (so that the splitting hypothesis `K ≤ hi` holds and
  the second term is dominated by the tail variation `varRhoFrom ρ K a`), and
* the bound `varRho ρ 0 K a ≤ Σ_{k < K} ‖a (k+1) - a k‖ₑ ≤ 2 Σ_{i ≤ K} ‖a i‖ₑ` for the initial
  window, obtained from `varRho_le_sum_increments` and the triangle inequality.

The factor `4` in the statement is not optimal — the argument gives `2` — but the slack is
harmless for the applications.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Monotonicity of `varRho` in the upper end of the window**: enlarging the window can only
increase the set of admissible chains. -/
lemma varRho_le_varRho_of_le_hi (ρ : ℝ) {lo hi hi' : ℕ} (h : hi ≤ hi') (a : ℕ → E) :
    varRho ρ lo hi a ≤ varRho ρ lo hi' a := by
  refine varRho_le_of_forall fun J t ht hc => ?_
  exact ofReal_chainLp_le_varRho ρ lo hi' J a t ht
    (fun j hj => ⟨(hc j hj).1, le_trans (hc j hj).2 h⟩)

/-- **The variation over the initial window `[0,K]` is bounded by the sum of the norms of the
values.**  Since `ℓ^ρ ≤ ℓ^1` for `ρ ≥ 1`, the variation is at most the total variation of the
consecutive increments over `[0,K)`, and each increment is at most the sum of the two norms. -/
lemma varRho_zero_le_two_sum_norms {ρ : ℝ} (hρ : 1 ≤ ρ) (K : ℕ) (a : ℕ → E) :
    varRho ρ 0 K a ≤ 2 * ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ := by
  have hstep : varRho ρ 0 K a ≤ ∑ k ∈ Finset.range K, ‖a (k + 1) - a k‖ₑ := by
    rw [Finset.range_eq_Ico]
    exact varRho_le_sum_increments (E := E) (ρ := ρ) hρ a
  refine le_trans hstep ?_
  calc ∑ k ∈ Finset.range K, ‖a (k + 1) - a k‖ₑ
      ≤ ∑ k ∈ Finset.range K, (‖a (k + 1)‖ₑ + ‖a k‖ₑ) :=
        Finset.sum_le_sum fun k _ => enorm_sub_le
    _ = ∑ k ∈ Finset.range K, ‖a (k + 1)‖ₑ + ∑ k ∈ Finset.range K, ‖a k‖ₑ :=
        Finset.sum_add_distrib
    _ ≤ ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ + ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ := by
        refine add_le_add ?_ ?_
        · rw [Finset.sum_range_succ']
          exact le_add_right le_rfl
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.le_succ K)) (fun i _ _ => by simp)
    _ = 2 * ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ := (two_mul _).symm

/-- The `ρ`-variation of a sequence over the whole index range `[0,∞)` is bounded by its variation over the tail `[K,∞)` plus the initial increments `Σ_{i ≤ K} ‖a i‖` (with a small slack constant), for `ρ ≥ 1`. -/
theorem varRho_tail_glue {E : Type*} [SeminormedAddCommGroup E]
    (ρ : ℝ) (hρ : 1 ≤ ρ) (K : ℕ) (a : ℕ → E) :
    Work.BourgainPlan.Maximal.varRhoAll ρ a
      ≤ Work.BourgainPlan.Maximal.varRhoFrom ρ K a
        + 4 * ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ := by
  have hhead : varRho ρ 0 K a ≤ 2 * ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ :=
    varRho_zero_le_two_sum_norms hρ K a
  -- splitting the window at `K`, enlarged so that the tail includes the whole window
  have hmain : varRhoAll ρ a ≤ varRho ρ 0 K a + varRhoFrom ρ K a := by
    rw [varRhoAll]
    refine iSup_le fun hi => ?_
    refine le_trans (varRho_le_varRho_of_le_hi ρ (le_max_left hi K) a) ?_
    refine le_trans (varRhoSplitting (E := E) hρ (lo := 0) (K := K) (hi := max hi K)
      (Nat.zero_le K) (le_max_right hi K) a) ?_
    exact add_le_add le_rfl (le_iSup (fun hh : ℕ => varRho ρ K hh a) (max hi K))
  have h24 : (2 : ℝ≥0∞) * (∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ)
      ≤ 4 * ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ := by
    have h : (2 : ℝ≥0∞) * (∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ)
        ≤ 2 * (∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ)
          + 2 * (∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ) := le_add_right le_rfl
    rw [← add_mul, show ((2 : ℝ≥0∞) + 2) = 4 by norm_num] at h
    exact h
  calc varRhoAll ρ a ≤ varRho ρ 0 K a + varRhoFrom ρ K a := hmain
    _ ≤ 4 * ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ + varRhoFrom ρ K a :=
        add_le_add (le_trans hhead h24) le_rfl
    _ = varRhoFrom ρ K a + 4 * ∑ i ∈ Finset.range (K + 1), ‖a i‖ₑ := add_comm _ _

end Work.BourgainPlan.Maximal
