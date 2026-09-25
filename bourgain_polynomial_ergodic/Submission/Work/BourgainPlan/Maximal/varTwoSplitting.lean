import Mathlib
import Submission.Work.BourgainPlan.Maximal.varSeminormDefs

/-!
# Splitting the `2`-variation seminorm at an intermediate index

Kosz–Mirek–Słomian–Zhang, Definition 5.1, condition (1): the `2`-variation seminorm over an index
window is subadditive with respect to cutting the window at an interior index `K`.

The proof is the `ℓ²` triangle inequality.  Given a monotone chain `t` with values in `[lo, hi]`,
clip it at the threshold `K` on both sides:

* `j ↦ min (t j) K` is a monotone chain with values in `[lo, K]`,
* `j ↦ max (t j) K` is a monotone chain with values in `[K, hi]`,

and, pointwise in `j`, the increment of `t` is the *sum* of the two clipped increments
(`a (min m K) + a (max m K) = a m + a K`, a min/max identity).  Minkowski's inequality for finite
`ℓ²` sums (proved here from Cauchy–Schwarz) then bounds the chain square function of `t` by the two
clipped chain square functions, each of which is dominated by the corresponding `varTwo`.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Minkowski's inequality for finite `ℓ²` sums of reals.**  Derived from the Cauchy–Schwarz
inequality `Real.sum_mul_le_sqrt_mul_sqrt`. -/
lemma sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2) := by
  have hA : 0 ≤ ∑ i ∈ s, x i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hB : 0 ≤ ∑ i ∈ s, y i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hCS : ∑ i ∈ s, x i * y i
      ≤ Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt s x y
  have hpt : ∀ i ∈ s, (x i + y i) ^ 2 = x i ^ 2 + 2 * (x i * y i) + y i ^ 2 := by
    intro i _; ring
  have hsq : ∑ i ∈ s, (x i + y i) ^ 2
      ≤ (Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2)) ^ 2 := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    calc (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, x i * y i) + ∑ i ∈ s, y i ^ 2
        ≤ (∑ i ∈ s, x i ^ 2)
            + 2 * (Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2))
            + ∑ i ∈ s, y i ^ 2 := by linarith
      _ = (Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2)) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]; ring
  calc Real.sqrt (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2) :=
        Real.sqrt_sq (by positivity)

/-- **Clipping a chain at `K`.**  The `ℓ²`-length of the increments of a chain `t` is at most the
sum of the `ℓ²`-lengths of the increments of the two chains obtained by clipping `t` at the
threshold `K` from below and from above: `j ↦ min (t j) K` and `j ↦ max (t j) K`. -/
lemma chainSq_le_clip (J K : ℕ) (a : ℕ → E) (t : ℕ → ℕ) :
    chainSq J a t ≤ chainSq J a (fun j => min (t j) K) + chainSq J a (fun j => max (t j) K) := by
  -- The increments of `t` split as the sum of the clipped increments.
  have hkey : ∀ j, a (t (j + 1)) - a (t j)
      = (a (min (t (j + 1)) K) - a (min (t j) K))
        + (a (max (t (j + 1)) K) - a (max (t j) K)) := by
    intro j
    have hminmax : ∀ m : ℕ, a (min m K) + a (max m K) = a m + a K := by
      intro m
      rcases le_or_gt m K with h | h
      · rw [min_eq_left h, max_eq_right h, add_comm]
      · rw [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h), add_comm]
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
  have hsum : ∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2
      ≤ ∑ j ∈ Finset.range J, (‖a (min (t (j + 1)) K) - a (min (t j) K)‖
          + ‖a (max (t (j + 1)) K) - a (max (t j) K)‖) ^ 2 :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hbound j) 2
  calc chainSq J a t
      = Real.sqrt (∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2) := rfl
    _ ≤ Real.sqrt (∑ j ∈ Finset.range J, (‖a (min (t (j + 1)) K) - a (min (t j) K)‖
          + ‖a (max (t (j + 1)) K) - a (max (t j) K)‖) ^ 2) := Real.sqrt_le_sqrt hsum
    _ ≤ Real.sqrt (∑ j ∈ Finset.range J, ‖a (min (t (j + 1)) K) - a (min (t j) K)‖ ^ 2)
        + Real.sqrt (∑ j ∈ Finset.range J, ‖a (max (t (j + 1)) K) - a (max (t j) K)‖ ^ 2) :=
        sqrt_sum_sq_add_le _ _ _
    _ = chainSq J a (fun j => min (t j) K) + chainSq J a (fun j => max (t j) K) := rfl

/-- An admissible chain of `[lo, hi]` is dominated by `varTwo lo hi a`. -/
lemma ofReal_chainSq_le_varTwo (lo hi J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) (ht : Monotone t)
    (h : ∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi) :
    ENNReal.ofReal (chainSq J a t) ≤ varTwo lo hi a := by
  rw [varTwo]
  apply le_iSup_of_le J
  apply le_iSup_of_le t
  apply le_iSup_of_le ht
  apply le_iSup_of_le h
  exact le_rfl

/-- To bound `varTwo` above it suffices to bound every admissible chain. -/
lemma varTwo_le_of_forall {lo hi : ℕ} {C : ℝ≥0∞} {a : ℕ → E}
    (h : ∀ J t, Monotone t → (∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi) →
      ENNReal.ofReal (chainSq J a t) ≤ C) :
    varTwo lo hi a ≤ C := by
  rw [varTwo]
  refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun hh => h J t ht hh

/-- (Splitting property, condition (1) of KMSZ Definition 5.1.) A chain of indices in `[lo,hi]` can be cut at the index `K`: by the `ℓ²` triangle inequality the crossing increment is dominated by the two halves, hence the `2`-variation over `[lo,hi]` is at most the `2`-variation over `[lo,K]` plus the `2`-variation over `[K,hi]`. -/
theorem varTwoSplitting {E : Type*} [SeminormedAddCommGroup E] {lo K hi : ℕ} (hlo : lo ≤ K)
    (hhi : K ≤ hi) (a : ℕ → E) :
    Work.BourgainPlan.Maximal.varTwo lo hi a
      ≤ Work.BourgainPlan.Maximal.varTwo lo K a + Work.BourgainPlan.Maximal.varTwo K hi a := by
  refine varTwo_le_of_forall fun J t ht h => ?_
  have hclip := chainSq_le_clip (E := E) J K a t
  refine le_trans (ENNReal.ofReal_le_ofReal hclip) ?_
  rw [ENNReal.ofReal_add (chainSq_nonneg _ _ _) (chainSq_nonneg _ _ _)]
  refine add_le_add ?_ ?_
  · exact ofReal_chainSq_le_varTwo lo K J a (fun j => min (t j) K)
      (fun i j hij => min_le_min (ht hij) le_rfl)
      (fun j hj => ⟨le_min (h j hj).1 hlo, min_le_right _ _⟩)
  · exact ofReal_chainSq_le_varTwo K hi J a (fun j => max (t j) K)
      (fun i j hij => max_le_max (ht hij) le_rfl)
      (fun j hj => ⟨le_max_right _ _, max_le (h j hj).2 hhi⟩)

end

end Work.BourgainPlan.Maximal
