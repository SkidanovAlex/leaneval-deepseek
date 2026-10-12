import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.UBBInputs3.MatLoc.prof_norm
import Submission.Work.UBBInputs3.MatLoc.qform_winVec
import Submission.Work.UBBInputs3.MatLoc.sum_Icc_neg_split
import Submission.Work.UBBInputs3.MatLoc.sum_diff_reindex
import Submission.Work.UBBInputs3.MatLoc.sum_prof_translate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.sum_winVec_qform`

The Lieb–Solovej summation identity for the windowed vectors:

    Σ_{m ∈ mRange p n} ⟪φ_m, A φ_m⟫
      = d₀ + Σ_{k=1}^{n-1} R(k) d_k ,

where `φ_m = winVec p ψ m` (`φ_m j = prof p (j - m) * ψ j`), `d_k` is the `k`-th diagonal
expectation of `A` (`Work.UBBInputs3.dk`), and `R(k) = Σ_s prof(s) prof(s+k)`
(`Work.UBBInputs3.Rcorr`) is the autocorrelation of the profile.

The proof expands the quadratic form of `winVec p ψ m` (`qform_winVec`), exchanges the sum
over the translation parameter `m` with the sums over the indices, and uses that the
correlation sum over `m` telescopes into `R(j - i)` (`sum_prof_translate`).  Grouping the
resulting double sum by the difference `k = j - i` (`sum_diff_reindex`, the support
hypothesis on `A` being what lets the truncation along the diagonal be relaxed) and
splitting the symmetric range `[-(n-1), n-1]` into `{0}` and the pairs `±k`
(`sum_Icc_neg_split`), the evenness of `R` (`Rcorr_even`) and the normalisation `R(0) = 1`
(`Rcorr_zero`, from `Σ_s prof(s)² = 1`) give exactly the stated right-hand side.

Note that neither the hermiticity of `A` nor the support of `ψ` is needed: the identity is
purely algebraic.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-- The normalisation of the profile as an autocorrelation: `R(0) = Σ_s prof(s)² = 1`. -/
theorem Rcorr_zero (p : ℕ) : Work.UBBInputs3.Rcorr p 0 = 1 := by
  rw [Work.UBBInputs3.Rcorr]
  simp only [add_zero]
  rw [← prof_norm p]
  exact Finset.sum_congr rfl (fun s _ => by ring)

/-- The `k`-th diagonal expectation as the real part of the corresponding complex sum. -/
theorem re_sum_dSup (A : ℤ → ℤ → ℂ) (n : ℕ) (ψ : ℤ → ℂ) (k : ℤ) :
    (∑ i ∈ Work.UBBInputs3.iRange n, star (ψ i) * A i (i + k) * ψ (i + k)).re
      = Work.UBBInputs3.dSup A n ψ k := by
  rw [Work.UBBInputs3.dSup, Complex.re_sum]

theorem sum_winVec_qform (A : ℤ → ℤ → ℂ) (n p : ℕ) (ψ : ℤ → ℂ)
    (hAsupp : ∀ i j, A i j ≠ 0 → i ∈ Work.UBBInputs3.iRange n ∧ j ∈ Work.UBBInputs3.iRange n)
    (hAherm : ∀ i j, A j i = star (A i j))
    (hψsupp : ∀ j, ψ j ≠ 0 → j ∈ Work.UBBInputs3.iRange n) :
    ∑ m ∈ Work.UBBInputs3.mRange p n,
        Work.UBBInputs3.qform A (Work.UBBInputs3.iRange n)
          (Work.UBBInputs3.winVec p ψ m) (Work.UBBInputs3.winVec p ψ m)
      = Work.UBBInputs3.dSup A n ψ 0
        + ∑ k ∈ Finset.Icc 1 ((n : ℤ) - 1),
            Work.UBBInputs3.Rcorr p k * Work.UBBInputs3.dk A n ψ k := by
  rcases Nat.eq_zero_or_pos n with hn | hnpos
  · -- `n = 0`: the index range is empty and both sides vanish.
    subst hn
    have h1 : Work.UBBInputs3.iRange 0 = (∅ : Finset ℤ) := Finset.Icc_eq_empty (by norm_num)
    simp [Work.UBBInputs3.qform, Work.UBBInputs3.dSup, h1]
  · -- `A` vanishes outside the index range, so the "truncated" products `A i (i+k)` vanish
    -- whenever `i + k` leaves `iRange n`.
    have hC : ∀ i, i ∈ Work.UBBInputs3.iRange n → ∀ j, j ∉ Work.UBBInputs3.iRange n →
        star (ψ i) * A i j * ψ j = 0 := by
      intro i _ j hj
      have hAij : A i j = 0 := by
        by_contra h
        exact hj (hAsupp i j h).2
      simp [hAij]
    -- Step 1: expand the quadratic form and sum the correlation over the translation `m`.
    have hmain :
        ∑ m ∈ Work.UBBInputs3.mRange p n,
            Work.UBBInputs3.qform A (Work.UBBInputs3.iRange n)
              (Work.UBBInputs3.winVec p ψ m) (Work.UBBInputs3.winVec p ψ m)
          = ∑ i ∈ Work.UBBInputs3.iRange n, ∑ j ∈ Work.UBBInputs3.iRange n,
              Work.UBBInputs3.Rcorr p (j - i) * (star (ψ i) * A i j * ψ j).re := by
      calc ∑ m ∈ Work.UBBInputs3.mRange p n,
              Work.UBBInputs3.qform A (Work.UBBInputs3.iRange n)
                (Work.UBBInputs3.winVec p ψ m) (Work.UBBInputs3.winVec p ψ m)
          = ∑ m ∈ Work.UBBInputs3.mRange p n, ∑ i ∈ Work.UBBInputs3.iRange n,
              ∑ j ∈ Work.UBBInputs3.iRange n,
                (Work.UBBInputs3.prof p (i - m) * Work.UBBInputs3.prof p (j - m))
                  * (star (ψ i) * A i j * ψ j).re :=
            Finset.sum_congr rfl (fun m _ => qform_winVec A n p ψ m)
        _ = ∑ i ∈ Work.UBBInputs3.iRange n, ∑ m ∈ Work.UBBInputs3.mRange p n,
              ∑ j ∈ Work.UBBInputs3.iRange n,
                (Work.UBBInputs3.prof p (i - m) * Work.UBBInputs3.prof p (j - m))
                  * (star (ψ i) * A i j * ψ j).re := by
            rw [Finset.sum_comm]
        _ = ∑ i ∈ Work.UBBInputs3.iRange n, ∑ j ∈ Work.UBBInputs3.iRange n,
              ∑ m ∈ Work.UBBInputs3.mRange p n,
                (Work.UBBInputs3.prof p (i - m) * Work.UBBInputs3.prof p (j - m))
                  * (star (ψ i) * A i j * ψ j).re := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_comm]
        _ = ∑ i ∈ Work.UBBInputs3.iRange n, ∑ j ∈ Work.UBBInputs3.iRange n,
              (∑ m ∈ Work.UBBInputs3.mRange p n,
                Work.UBBInputs3.prof p (i - m) * Work.UBBInputs3.prof p (j - m))
                * (star (ψ i) * A i j * ψ j).re := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [Finset.sum_mul]
        _ = ∑ i ∈ Work.UBBInputs3.iRange n, ∑ j ∈ Work.UBBInputs3.iRange n,
              Work.UBBInputs3.Rcorr p (j - i) * (star (ψ i) * A i j * ψ j).re := by
            refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
            rw [sum_prof_translate n p i j hi hj]
    -- Step 2: regroup the double sum by the difference `k = j - i`.
    rw [hmain, sum_diff_reindex (fun i j => star (ψ i) * A i j * ψ j)
          (Work.UBBInputs3.Rcorr p) n hC]
    -- Step 3: identify the inner sums with the diagonal expectations `d_k`.
    have hre : ∀ k : ℤ, (∑ i ∈ Work.UBBInputs3.iRange n,
          (fun i j => star (ψ i) * A i j * ψ j) i (i + k)).re
        = Work.UBBInputs3.dSup A n ψ k := by
      intro k
      show (∑ i ∈ Work.UBBInputs3.iRange n, star (ψ i) * A i (i + k) * ψ (i + k)).re
        = Work.UBBInputs3.dSup A n ψ k
      exact re_sum_dSup A n ψ k
    have hstep : (∑ k ∈ Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1),
          Work.UBBInputs3.Rcorr p k *
            (∑ i ∈ Work.UBBInputs3.iRange n,
              (fun i j => star (ψ i) * A i j * ψ j) i (i + k)).re)
        = ∑ k ∈ Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1),
            Work.UBBInputs3.Rcorr p k * Work.UBBInputs3.dSup A n ψ k :=
      Finset.sum_congr rfl (fun k _ => by rw [hre k])
    rw [hstep]
    -- Step 4: split the symmetric range into the central term and the pairs `±k`; the
    -- diagonal expectation for `k ≠ 0` is `d_k = dSup k + dSup (-k)`.
    have hN : (0 : ℤ) ≤ (n : ℤ) - 1 := by
      have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
      omega
    rw [sum_Icc_neg_split ((n : ℤ) - 1) hN
        (fun k => Work.UBBInputs3.Rcorr p k * Work.UBBInputs3.dSup A n ψ k)]
    have hfin : (∑ k ∈ Finset.Icc 1 ((n : ℤ) - 1),
          (Work.UBBInputs3.Rcorr p k * Work.UBBInputs3.dSup A n ψ k
            + Work.UBBInputs3.Rcorr p (-k) * Work.UBBInputs3.dSup A n ψ (-k)))
        = ∑ k ∈ Finset.Icc 1 ((n : ℤ) - 1),
            Work.UBBInputs3.Rcorr p k * Work.UBBInputs3.dk A n ψ k := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk1 : k ≠ 0 := by
        have hk1' := (Finset.mem_Icc.mp hk).1
        omega
      rw [Work.UBBInputs3.dk, if_neg hk1, Rcorr_even p k]
      ring
    rw [Rcorr_zero p, one_mul, hfin]

end Work.UBBInputs3.MatLoc
