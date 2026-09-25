import Mathlib
import Submission.Work.BourgainPlan.Maximal.rhoVariationDefs

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Telescoping bound.**  The distance between two values of a sequence is at most the sum of the
norms of the consecutive increments between the two indices:
`a m - a l = Σ_{k = l}^{m-1} (a (k+1) - a k)`, and the triangle inequality. -/
lemma norm_sub_le_sum_Ico_norm_sub (a : ℕ → E) {l m : ℕ} (h : l ≤ m) :
    ‖a m - a l‖ ≤ ∑ k ∈ Finset.Ico l m, ‖a (k + 1) - a k‖ := by
  have htel : a m - a l = ∑ k ∈ Finset.Ico l m, (a (k + 1) - a k) :=
    (Finset.sum_Ico_sub a h).symm
  rw [htel]
  exact norm_sum_le _ _

/-- **`ℓ^ρ ≤ ℓ^1` for finite nonnegative vectors.**  For `ρ ≥ 1` and `x i ≥ 0`,
`(Σ_i (x i)^ρ)^{1/ρ} ≤ Σ_i x i`.  The key step is the two-term inequality
`a^ρ + b^ρ ≤ (a + b)^ρ` (`Real.add_rpow_le_rpow_add`), assembled by induction. -/
lemma sum_rpow_inv_le_sum {ρ : ℝ} (hρ : 1 ≤ ρ) {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    (∑ i ∈ s, x i ^ ρ) ^ (1 / ρ) ≤ ∑ i ∈ s, x i := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hkey : ∑ i ∈ s, x i ^ ρ ≤ (∑ i ∈ s, x i) ^ ρ := by
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow (ne_of_gt hρ0)]
    | insert a s ha ih =>
        calc ∑ i ∈ insert a s, x i ^ ρ
            = x a ^ ρ + ∑ i ∈ s, x i ^ ρ := Finset.sum_insert ha
          _ ≤ x a ^ ρ + (∑ i ∈ s, x i) ^ ρ := by linarith
          _ ≤ (x a + ∑ i ∈ s, x i) ^ ρ :=
              Real.add_rpow_le_rpow_add (hx a) (Finset.sum_nonneg fun i _ => hx i) hρ
          _ = (∑ i ∈ insert a s, x i) ^ ρ := by rw [Finset.sum_insert ha]
  have hA : 0 ≤ ∑ i ∈ s, x i ^ ρ :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hx i) _
  have hB : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
  calc (∑ i ∈ s, x i ^ ρ) ^ (1 / ρ)
      ≤ ((∑ i ∈ s, x i) ^ ρ) ^ (1 / ρ) :=
        Real.rpow_le_rpow hA hkey (le_of_lt (one_div_pos.mpr hρ0))
    _ = ∑ i ∈ s, x i := by
        rw [← Real.rpow_mul hB, mul_one_div, div_self (ne_of_gt hρ0), Real.rpow_one]

/-- **The blocks of a monotone chain are disjoint and contained in the window.**  For a monotone
chain `t` with `lo ≤ t j ≤ hi` for `j ≤ J`, the intervals `[t j, t (j+1))`, `j < J`, are pairwise
disjoint and all contained in `[lo, hi)`; hence the sum of a nonnegative sequence over the blocks is
at most its sum over the whole window. -/
lemma sum_Ico_blocks_le {J lo hi : ℕ} {t : ℕ → ℕ} (ht : Monotone t)
    (h : ∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi) {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) :
    ∑ j ∈ Finset.range J, ∑ k ∈ Finset.Ico (t j) (t (j + 1)), c k
      ≤ ∑ k ∈ Finset.Ico lo hi, c k := by
  classical
  have hdisj : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint
      (fun j => Finset.Ico (t j) (t (j + 1))) := by
    intro j hj l hl hjl
    have hj' : j < J := by simpa using hj
    have hl' : l < J := by simpa using hl
    rcases lt_or_gt_of_ne hjl with hlt | hlt
    · refine Finset.disjoint_left.mpr fun k hk1 hk2 => ?_
      rw [Finset.mem_Ico] at hk1 hk2
      have hstep : t (j + 1) ≤ t l := ht (by omega)
      omega
    · exact (Finset.disjoint_left.mpr fun k hk1 hk2 => by
        rw [Finset.mem_Ico] at hk1 hk2
        have hstep : t (l + 1) ≤ t j := ht (by omega)
        omega).symm
  rw [← Finset.sum_biUnion (f := c) hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hc k)
  intro k hk
  rw [Finset.mem_biUnion] at hk
  obtain ⟨j, hj, hkj⟩ := hk
  rw [Finset.mem_range] at hj
  rw [Finset.mem_Ico] at hkj ⊢
  obtain ⟨h1, h2⟩ := hkj
  have hlo0 : lo ≤ t 0 := (h 0 (Nat.zero_le J)).1
  have hhi : t J ≤ hi := (h J le_rfl).2
  have h1' : t 0 ≤ t j := ht (Nat.zero_le j)
  have h2' : t (j + 1) ≤ t J := ht (by omega)
  exact ⟨le_trans hlo0 (le_trans h1' h1), lt_of_lt_of_le h2 (le_trans h2' hhi)⟩

/-- **The chain `ℓ^ρ`-length is bounded by the total variation of the consecutive increments.**
On each leg of the chain, `a (t (j+1)) − a (t j)` is the sum of the consecutive increments between
the two indices, so the leg is dominated by the sum of their norms; the blocks of consecutive
increments of the legs are disjoint pieces of `[lo, hi)`, and `ℓ^ρ ≤ ℓ^1`. -/
lemma chainLp_le_sum_increments {ρ : ℝ} (hρ : 1 ≤ ρ) (a : ℕ → E) {lo hi J : ℕ} {t : ℕ → ℕ}
    (ht : Monotone t) (h : ∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi) :
    chainLp ρ J a t ≤ ∑ k ∈ Finset.Ico lo hi, ‖a (k + 1) - a k‖ := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hc : ∀ k, 0 ≤ ‖a (k + 1) - a k‖ := fun k => norm_nonneg _
  have hstep : ∀ j, ‖a (t (j + 1)) - a (t j)‖
      ≤ ∑ k ∈ Finset.Ico (t j) (t (j + 1)), ‖a (k + 1) - a k‖ :=
    fun j => norm_sub_le_sum_Ico_norm_sub a (ht (Nat.le_succ j))
  calc chainLp ρ J a t
      = (∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ ρ) ^ (1 / ρ) := rfl
    _ ≤ (∑ j ∈ Finset.range J,
          (∑ k ∈ Finset.Ico (t j) (t (j + 1)), ‖a (k + 1) - a k‖) ^ ρ) ^ (1 / ρ) := by
        refine Real.rpow_le_rpow
          (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _)
          (Finset.sum_le_sum fun j _ => ?_)
          (le_of_lt (one_div_pos.mpr hρ0))
        exact Real.rpow_le_rpow (norm_nonneg _) (hstep j) (le_trans zero_le_one hρ)
    _ ≤ ∑ j ∈ Finset.range J,
          (∑ k ∈ Finset.Ico (t j) (t (j + 1)), ‖a (k + 1) - a k‖) :=
        sum_rpow_inv_le_sum hρ _ _ (fun j => Finset.sum_nonneg fun k _ => hc k)
    _ ≤ ∑ k ∈ Finset.Ico lo hi, ‖a (k + 1) - a k‖ :=
        sum_Ico_blocks_le ht h hc

/-- **The `ρ`-variation is dominated by the total variation of the consecutive increments.**

For every `ρ ≥ 1` and every index window `[lo, hi]`, the `ρ`-variation of a sequence over `[lo, hi]`
is at most the sum of the `enorm`s of the *consecutive* increments `a (k+1) − a k`, `k ∈ [lo, hi)`.

This is the `V^ρ ≤ V^1` comparison (`‖x‖_ρ ≤ ‖x‖_1` for finite vectors) together with the
telescoping bound: along a monotone chain,
`a (t (j+1)) − a (t j) = Σ_{k = t j}^{t (j+1) − 1} (a (k+1) − a k)`, so by the triangle inequality
the total variation of the chain is at most the total variation of the sequence over the interval.

Consumers: the "error-term" step (6.17) of KMSZ arXiv:2606.12663, where a family whose `ℓ^p` norms
are summable in the scale `N` must have bounded `ρ`-variation over the scale set `D_τ`, and more
generally the standard fact that variation is controlled by summability of the increments. -/
theorem varRho_le_sum_increments {E : Type*} [SeminormedAddCommGroup E] {ρ : ℝ} (hρ : 1 ≤ ρ)
    {lo hi : ℕ} (a : ℕ → E) :
    varRho ρ lo hi a ≤ ∑ k ∈ Finset.Ico lo hi, ‖a (k + 1) - a k‖ₑ := by
  rw [varRho]
  refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun h => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal (chainLp_le_sum_increments hρ a ht h)) ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => norm_nonneg _)]
  exact le_of_eq (Finset.sum_congr rfl fun k _ => ofReal_norm (a (k + 1) - a k))

end

end Work.BourgainPlan.Maximal
