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

open Submission.ASP

/-- The merged sum `Kmerge` at the scale `s = 2^J` is bounded by the sum of the dyadic
(B′)-integrands `Bint` at the scales `2^j z`, `0 ≤ j < J`.

This is the pointwise "dyadic split + merge" step of §7 of the companion paper
("Asymptotic sieve for primes"); it is the local `hKmerge` of `smAvg_abs_Ksum_le`
(see `Submission/ASP/S7e.lean`), restated as a standalone lemma. -/
lemma Kmerge_le_dyadic_Bint (a lam : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) {s z : ℝ} {J : ℕ} (Δ : ℕ)
    (hs : s = (2 : ℝ) ^ J) (hΔ : 1 ≤ Δ)
    (hw : ∀ ℓ, 1 ≤ ℓ → ((ℓ.divisors.card : ℝ)) ^ 2 ≤ w ℓ)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1) :
    Submission.ASP.Kmerge a lam N s Δ z
      ≤ ∑ j ∈ Finset.range J, Submission.ASP.Bint a N w ((2 : ℝ) ^ j * z) := by
  rw [hs]
  simp only [Kmerge, Kfac, Bint]
  have htw : ∀ (j : ℕ) (u : ℝ), (2 : ℝ) ^ (j + 1) * u = 2 * ((2 : ℝ) ^ j * u) := by
    intro j u; rw [pow_succ]; ring
  have hperm1 : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
        ∑ j ∈ Finset.range J,
          |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|)
      = ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range J,
        ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
    Finset.sum_congr rfl (fun ν₁ _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
  have hperm2 : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range J,
        ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|)
      = ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.Icc 1 N,
        ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
    Finset.sum_congr rfl (fun ν₁ _ => Finset.sum_comm)
  have hperm3 : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.Icc 1 N,
        ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|)
      = ∑ j ∈ Finset.range J, ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N,
        ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
    Finset.sum_comm
  calc ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) z ((2 : ℝ) ^ J * z)|
      ≤ ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * ∑ j ∈ Finset.range J,
            |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
        Finset.sum_le_sum (fun ν₁ _ => Finset.sum_le_sum (fun k _ =>
          Finset.sum_le_sum (fun ν₂ _ => mul_le_mul_of_nonneg_left
            (Xsum_abs_dyadic_le a N (ν₁ * k) J z) (abs_nonneg _))))
    _ = ∑ j ∈ Finset.range J, ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N,
          ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| := by
        simp_rw [Finset.mul_sum]
        exact hperm1.trans (hperm2.trans hperm3)
    _ ≤ ∑ j ∈ Finset.range J, ∑ ℓ ∈ Finset.Icc 1 N,
          w ℓ * |Xsum a N ℓ ((2 : ℝ) ^ j * z) (2 * ((2 : ℝ) ^ j * z))| := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        refine (le_of_eq ?_).trans
          (sum_merge_le_Icc a lam w N Δ ((2 : ℝ) ^ j * z) hΔ hlam_le1 hw)
        refine Finset.sum_congr rfl (fun ν₁ _ => Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun ν₂ _ => ?_)))
        rw [htw j z]

end Work.FIFinal
