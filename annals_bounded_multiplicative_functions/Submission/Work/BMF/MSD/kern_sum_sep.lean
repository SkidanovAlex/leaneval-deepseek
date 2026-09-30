import Mathlib
import Submission.Work.BMF.MSD.basic
import Submission.Work.BMF.MSD.arc_count
import Submission.Work.BMF.MSD.kern_le_filter_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.MSD

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF
open Work.BMF.MSD

/-- Counting bound for `δ`-separated frequencies: if the reals `α r` have pairwise circular
distance at least `δ ∈ (0,1]`, then for each `r` the sum of the kernel majorants
`kern N (α r - α s)` is at most `2N + (8/δ)(2 + log (2N+2))`. -/
theorem kern_sum_sep (ι : Type*) [DecidableEq ι] (S : Finset ι) (α : ι → ℝ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ circDist (α r - α s)) (N : ℕ) (r : ι) :
    (∑ s ∈ S, kern N (α r - α s))
      ≤ 2 * (N : ℝ) + (8 / δ) * (2 + Real.log (2 * N + 2)) := by
  -- Step 1: bound each `kern N (α r - α s)` by the number of "small multiples" `k < N`, and
  -- exchange the order of summation.
  have hred : (∑ s ∈ S, kern N (α r - α s))
      ≤ ∑ k ∈ Finset.range N,
          ((S.filter (fun s => 2 * circDist (α r - α s) * (k : ℝ) < 1)).card : ℝ) := by
    have h1 : (∑ s ∈ S, kern N (α r - α s))
        ≤ ∑ s ∈ S,
            (((Finset.range N).filter
              (fun k : ℕ => 2 * circDist (α r - α s) * (k : ℝ) < 1)).card : ℝ) :=
      Finset.sum_le_sum (fun s _ => kern_le_filter_card N (α r - α s))
    have h2 : (∑ s ∈ S,
            (((Finset.range N).filter
              (fun k : ℕ => 2 * circDist (α r - α s) * (k : ℝ) < 1)).card : ℝ))
        = ∑ k ∈ Finset.range N,
            ((S.filter (fun s => 2 * circDist (α r - α s) * (k : ℝ) < 1)).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [Finset.sum_comm]
    exact le_trans h1 (le_of_eq h2)
  refine le_trans hred ?_
  -- The `k = 0` layer counts all of `S`, hence at most `1/δ + 1` by `arc_count` at `y = 1/2`.
  have hg0 : ((S.filter (fun s => 2 * circDist (α r - α s) * ((0 : ℕ) : ℝ) < 1)).card : ℝ)
      ≤ 1 / δ + 1 := by
    rw [Finset.filter_true_of_mem (fun s _ => by simp)]
    have h2 : (S.card : ℝ) = ((S.filter (fun s => circDist (α r - α s) ≤ 1 / 2)).card : ℝ) := by
      rw [Finset.filter_true_of_mem (fun s _ => circDist_le_half (α r - α s))]
    rw [h2]
    have h3 := arc_count S α r δ (1 / 2) hδ0 (by norm_num) hsep
    have h4 : 2 * (1 / 2) / δ + 1 = 1 / δ + 1 := by ring
    linarith [h3, h4]
  -- Each layer `k = j + 1` counts a `δ`-separated set inside an arc of radius `1/(2(j+1))`.
  have hgj : ∀ j : ℕ,
      ((S.filter (fun s => 2 * circDist (α r - α s) * ((j + 1 : ℕ) : ℝ) < 1)).card : ℝ)
        ≤ 1 / ((j + 1 : ℝ) * δ) + 1 := by
    intro j
    have hsub : (S.filter (fun s => 2 * circDist (α r - α s) * ((j + 1 : ℕ) : ℝ) < 1))
        ⊆ (S.filter (fun s => circDist (α r - α s) ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ)))) := by
      intro s hs
      simp only [Finset.mem_filter] at hs ⊢
      refine ⟨hs.1, ?_⟩
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((j + 1 : ℕ) : ℝ))]
      nlinarith [hs.2]
    calc ((S.filter (fun s => 2 * circDist (α r - α s) * ((j + 1 : ℕ) : ℝ) < 1)).card : ℝ)
        ≤ ((S.filter (fun s => circDist (α r - α s) ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ)))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 2 * (1 / (2 * ((j + 1 : ℕ) : ℝ))) / δ + 1 :=
          arc_count S α r δ (1 / (2 * ((j + 1 : ℕ) : ℝ))) hδ0 (by positivity) hsep
      _ = 1 / ((j + 1 : ℝ) * δ) + 1 := by field_simp; push_cast; ring
  -- Harmonic bound for the remaining layers.
  have hT : ∑ k ∈ Finset.range (N - 1), ((k + 1 : ℝ))⁻¹ ≤ 1 + Real.log (N : ℝ) := by
    calc ∑ k ∈ Finset.range (N - 1), ((k + 1 : ℝ))⁻¹
        ≤ ∑ k ∈ Finset.range N, ((k + 1 : ℝ))⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.sub_le N 1))
            (fun i _ _ => by positivity)
      _ = (harmonic N : ℝ) := by rw [harmonic]; push_cast; rfl
      _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
  by_cases hN0 : N = 0
  · subst hN0
    rw [Finset.range_zero, Finset.sum_empty]
    have hlog : (0 : ℝ) ≤ Real.log (2 * ((0 : ℕ) : ℝ) + 2) := Real.log_nonneg (by norm_num)
    have : (0 : ℝ) ≤ (8 / δ) * (2 + Real.log (2 * ((0 : ℕ) : ℝ) + 2)) :=
      mul_nonneg (by positivity) (by linarith)
    simp only [Nat.cast_zero]
    linarith
  · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hδinv : (0 : ℝ) ≤ (1 : ℝ) / δ := div_nonneg zero_le_one (le_of_lt hδ0)
    have hmain : ∑ k ∈ Finset.range N,
          ((S.filter (fun s => 2 * circDist (α r - α s) * (k : ℝ) < 1)).card : ℝ)
        ≤ (N : ℝ) + (1 / δ) * (2 + Real.log (N : ℝ)) := by
      conv_lhs => rw [show N = (N - 1) + 1 by omega]
      rw [Finset.sum_range_succ']
      have hb : (∑ k ∈ Finset.range (N - 1),
            ((S.filter (fun s => 2 * circDist (α r - α s) * ((k + 1 : ℕ) : ℝ) < 1)).card : ℝ))
          ≤ (1 / δ) * (∑ k ∈ Finset.range (N - 1), ((k + 1 : ℝ))⁻¹) + ((N : ℝ) - 1) := by
        have e1 : (∑ k ∈ Finset.range (N - 1),
              ((S.filter (fun s => 2 * circDist (α r - α s) * ((k + 1 : ℕ) : ℝ) < 1)).card : ℝ))
            ≤ ∑ k ∈ Finset.range (N - 1), (1 / ((k + 1 : ℝ) * δ) + 1) :=
          Finset.sum_le_sum (fun k _ => hgj k)
        have e2 : (∑ k ∈ Finset.range (N - 1), (1 / ((k + 1 : ℝ) * δ) + 1))
            = (1 / δ) * (∑ k ∈ Finset.range (N - 1), ((k + 1 : ℝ))⁻¹) + ((N : ℝ) - 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Finset.mul_sum,
              nsmul_eq_mul, mul_one, Nat.cast_sub hNpos, Nat.cast_one]
          congr 1
          apply Finset.sum_congr rfl; intro k _
          rw [one_div, mul_inv_rev, one_div]
        exact e1.trans (le_of_eq e2)
      have hb2 : (1 / δ) * (∑ k ∈ Finset.range (N - 1), ((k + 1 : ℝ))⁻¹) + ((N : ℝ) - 1)
          ≤ (1 / δ) * (1 + Real.log (N : ℝ)) + ((N : ℝ) - 1) := by nlinarith [hT, hδinv]
      have hc : ((S.filter (fun s => 2 * circDist (α r - α s) * ((0 : ℕ) : ℝ) < 1)).card : ℝ)
          ≤ 1 / δ + 1 := hg0
      have hbb := le_trans hb hb2
      nlinarith [hbb, hc, hT, hδinv]
    have hlog2 : 0 ≤ Real.log (2 * (N : ℝ) + 2) := by
      apply Real.log_nonneg
      have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hlogNle : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ) + 2) := by
      apply Real.log_le_log (by exact_mod_cast hNpos)
      have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hkey : (2 + Real.log (N : ℝ)) ≤ 8 * (2 + Real.log (2 * (N : ℝ) + 2)) := by nlinarith
    have hA : (1 / δ) * (2 + Real.log (N : ℝ))
        ≤ (8 / δ) * (2 + Real.log (2 * (N : ℝ) + 2)) := by
      have h8 : (8 / δ) = 8 * (1 / δ) := by ring
      rw [h8]; nlinarith [hkey, hδinv]
    linarith [hmain, hA]

end Work.BMF.MSD
