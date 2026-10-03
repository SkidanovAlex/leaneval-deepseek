/-
# `Work.FIFinal.sum_abs_Ksum_le_KmergeD`

The *pointwise* (i.e. for every real `y`, not merely in the mean) bound underlying §7 of the
companion paper:

`∑_{k ≤ N} |Ksum_k(y)| ≤ KmergeD(y)`,

where `Ksum` is the inner `k`-sum of (7.1) (`Submission.ASP.Ksum`) and `KmergeD` is the merged
`(ν₁,k,ν₂)`-sum of §7 (7.2) with the fibre `ν₁` evaluated at `y/ν₁` (`Submission.ASP.KmergeD`).

The proof has two regimes:

* `y > 0`: apply the pointwise expansion `Ksum_abs_le_merge` (`Submission.ASP.S7b`) for each
  `k ≤ N`, swap the `k`- and `ν₁`-sums, drop the `ν₁`-range from `Icc 1 N` down to `Icc 1 Δ`
  (the terms with `Δ < ν₁` vanish identically, by the support hypothesis on `λ`, since
  `ν₁ | ν₁ν₂` forces `Δ < ν₁ν₂`), and identify the result with `KmergeD`;
* `y ≤ 0`: the `b`-range of `Ksum` is empty (`1 ≤ b ≤ s·y ≤ 0`), and the right-hand side is
  nonnegative by `KmergeD_nonneg`.

This is the same argument that is carried out inline (as `hpt`) inside
`Submission.ASP.smAvg_abs_Ksum_le`; it is isolated here because the integrated restatements in
`Submission/Work/FIFinal` consume it as a stand-alone step.
-/
import Mathlib
import Submission.Work.FIChain.BprimeWindowIntegrated
import Submission.Work.FIChain.RhoWindowIntegrated2
import Submission.ASP.Defs
import Submission.ASP.S3v
import Submission.ASP.S7b
import Submission.ASP.S7c
import Submission.ASP.S7d
import Submission.ASP.S7e
import Submission.ASP.S8
import Submission.ASP.S8b

namespace Work.FIFinal

open Finset

lemma sum_abs_Ksum_le_KmergeD (a lam : ℕ → ℝ) (N : ℕ) {s : ℝ} {Δ : ℕ}
    (hspos : 0 < s) (hΔ : 1 ≤ Δ)
    (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (ha : ∀ n, ¬ Squarefree n → a n = 0) :
    ∀ y : ℝ, (∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k|)
      ≤ Submission.ASP.KmergeD a lam N s Δ y := by
  intro y
  by_cases hy : 0 < y
  · -- ## The pointwise expansion of `Ksum_k`, for each `k ≤ N`
    have h1 : (∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k|)
        ≤ ∑ k ∈ Finset.Icc 1 N, ∑ ν₁ ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Submission.ASP.Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)| :=
      Finset.sum_le_sum (fun k hk => Submission.ASP.Ksum_abs_le_merge a lam N k y (s * y) hy
        (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2 ha)
    rw [Finset.sum_comm] at h1
    -- ## The terms with `Δ < ν₁` vanish: `ν₁ | ν₁ν₂`, and `λ` is supported on `[1,Δ]`
    have hGzero : ∀ x : ℕ, Δ < x → (∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
          |lam (x * ν₂)| * |Submission.ASP.Xsum a N (x * k) (y / x) (s * y / x)|) = 0 := by
      intro x hx
      refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun ν₂ hν₂ => ?_))
      have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
      have hν₂1 : 1 ≤ ν₂ :=
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hν₂).1 (Nat.pos_of_ne_zero hk0)
      have hlt : Δ < x * ν₂ :=
        calc Δ < x := hx
          _ = x * 1 := (mul_one _).symm
          _ ≤ x * ν₂ := Nat.mul_le_mul_left x hν₂1
      rw [hlam_supp (x * ν₂) hlt, abs_zero, zero_mul]
    have hsub1 : Finset.Icc 1 (min N Δ) ⊆ Finset.Icc 1 N := fun x hx => by
      rw [Finset.mem_Icc] at hx ⊢
      exact ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
    have hsub2 : Finset.Icc 1 (min N Δ) ⊆ Finset.Icc 1 Δ := fun x hx => by
      rw [Finset.mem_Icc] at hx ⊢
      exact ⟨hx.1, le_trans hx.2 (min_le_right _ _)⟩
    have hzero' : ∀ x ∈ Finset.Icc 1 N, x ∉ Finset.Icc 1 (min N Δ) →
        (∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
          |lam (x * ν₂)| * |Submission.ASP.Xsum a N (x * k) (y / x) (s * y / x)|) = 0 := by
      intro x hx hxs
      rw [Finset.mem_Icc] at hx
      refine hGzero x ?_
      by_contra hcon
      rw [not_lt] at hcon
      exact hxs (Finset.mem_Icc.mpr ⟨hx.1, le_min hx.2 hcon⟩)
    -- ## Shrink the `ν₁`-range from `Icc 1 N` down to `Icc 1 Δ`
    have h2 : (∑ ν₁ ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Submission.ASP.Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)|)
        ≤ ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Submission.ASP.Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)| := by
      have heq : (∑ ν₁ ∈ Finset.Icc 1 (min N Δ), ∑ k ∈ Finset.Icc 1 N,
            ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Submission.ASP.Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)|)
          = ∑ ν₁ ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Submission.ASP.Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)| :=
        Finset.sum_subset hsub1 hzero'
      rw [← heq]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun x _ _ =>
        Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))
    -- ## Identify the target with `KmergeD`
    refine h1.trans (h2.trans ?_)
    simp only [Submission.ASP.KmergeD, Submission.ASP.Kfac]
    refine Finset.sum_le_sum (fun ν₁ _ => Finset.sum_le_sum (fun k _ =>
      Finset.sum_le_sum (fun ν₂ _ => ?_)))
    rw [mul_div_assoc]
  · -- ## The degenerate regime `y ≤ 0`
    have hy' : y ≤ 0 := not_lt.mp hy
    have hzero : ∀ k, Submission.ASP.Ksum a lam N y (s * y) k = 0 := fun k =>
      Submission.ASP.Ksum_eq_zero_of_sy_nonpos a lam N k y (s * y)
        (mul_nonpos_of_nonneg_of_nonpos hspos.le hy')
    rw [Finset.sum_eq_zero (fun k _ => by rw [hzero k, abs_zero])]
    exact Submission.ASP.KmergeD_nonneg a lam N s Δ y

end Work.FIFinal
