import Mathlib
import Submission.Work.Analysis.Complex.dirichletPoly_normsq_expansion
import Submission.Work.Analysis.Integral.norm_intervalIntegral_exp_I_mul_le
import Submission.Work.Analysis.Real.log_diff_ge_div
import Submission.Work.ZeroDensity.Montgomery.norm_sq_cpow_neg_sigma
import Submission.Work.ZeroDensity.Zeta.dirichletPoly_meanValue_integral_corrected
import Submission.Commons.Analysis.Complex.intervalIntegral_re_comm
import Submission.Work.ZeroDensity.Ingham.norm_intervalIntegral_exp_I_mul_le_arbitrary
import Submission.Work.ZeroDensity.Ingham.abs_sub_le_max_mul_abs_log_sub
import Submission.Work.ZeroDensity.Ingham.dirichletPolyNegNormsqExpansion
import Submission.Work.ZeroDensity.Ingham.offdiag_kernel_sum_bound

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

noncomputable section

/-- `iTheta m n = log n - log m`, the frequency attached to the pair `(m, n)`; it is the
phase of `m^{-it} · conj (n^{-it})`. -/
private def iTheta (m n : ℕ) : ℝ := Real.log (n : ℝ) - Real.log (m : ℝ)

/-- The complex double sum whose real part is `‖∑ b n · n^{-it}‖²`. -/
private def iPhi (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    (b m * (starRingEnd ℂ) (b n)) * Complex.exp (Complex.I * ((t * iTheta m n : ℝ) : ℂ))

/-- The oscillatory integral `∫_A^B exp (i t θ) dt` for `θ = iTheta m n`. -/
private def iK (A B : ℝ) (m n : ℕ) : ℂ :=
  ∫ t in A..B, Complex.exp (Complex.I * ((t * iTheta m n : ℝ) : ℂ))

private lemma iPhi_continuous (b : ℕ → ℂ) (N : ℕ) : Continuous (iPhi b N) := by
  unfold iPhi
  fun_prop

/-- Pointwise expansion of the squared norm of `∑ b n · n^{-it}` as a double sum. -/
private lemma iPhi_expansion (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2
      = (iPhi b N t).re := by
  rw [dirichletPolyNegNormsqExpansion]
  simp only [iPhi, iTheta]

/-- The integral of the double sum is the double sum of the integrals. -/
private lemma iPhi_integral (b : ℕ → ℂ) (N : ℕ) (A B : ℝ) :
    (∫ t in A..B, iPhi b N t)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (b m * (starRingEnd ℂ) (b n)) * iK A B m n := by
  simp only [iPhi, iK, iTheta]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro n hn
      rw [intervalIntegral.integral_const_mul]
    · intro n hn
      exact (by fun_prop : Continuous fun t : ℝ => (b m * (starRingEnd ℂ) (b n)) *
        Complex.exp (Complex.I * ((t * (Real.log (n : ℝ) - Real.log (m : ℝ)) : ℝ) : ℂ))).intervalIntegrable _ _
  · intro m hm
    exact (by fun_prop : Continuous fun t : ℝ => ∑ n ∈ Finset.Icc 1 N,
      (b m * (starRingEnd ℂ) (b n)) *
        Complex.exp (Complex.I * ((t * (Real.log (n : ℝ) - Real.log (m : ℝ)) : ℝ) : ℂ))).intervalIntegrable _ _

/-- `iK A B m m = B - A`. -/
private lemma iK_self (A B : ℝ) (m : ℕ) : iK A B m m = ((B - A : ℝ) : ℂ) := by
  rw [iK, iTheta]
  have h : (fun t : ℝ => Complex.exp (Complex.I * ((t * (Real.log (m : ℝ) - Real.log (m : ℝ)) : ℝ) : ℂ)))
      = fun _ : ℝ => (1 : ℂ) := by
    funext t; rw [sub_self, mul_zero]; simp
  rw [h, intervalIntegral.integral_const]; simp

/-- Norm bound for the oscillatory integral. -/
private lemma iK_norm_le (A B : ℝ) (m n : ℕ) (h : iTheta m n ≠ 0) :
    ‖iK A B m n‖ ≤ 2 / |iTheta m n| := by
  rw [iK]
  have hfun : (fun t : ℝ => Complex.exp (Complex.I * ((t * iTheta m n : ℝ) : ℂ)))
      = fun t : ℝ => Complex.exp (Complex.I * ((iTheta m n * t : ℝ) : ℂ)) := by
    funext t; simp only [mul_comm t (iTheta m n)]
  rw [hfun]
  exact norm_intervalIntegral_exp_I_mul_le_arbitrary A B (iTheta m n) h

/-- `iTheta m n ≠ 0` when `m ≠ n` are positive. -/
private lemma iTheta_ne_zero {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) :
    iTheta m n ≠ 0 := by
  rw [iTheta, sub_ne_zero]
  intro hc
  exact h (by
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have := Real.log_injOn_pos hn0 hm0 hc
    exact_mod_cast this.symm)

/-- Sharp norm bound `‖iK A B m n‖ ≤ 2 · max(m,n)/|m-n|` for `m ≠ n` positive. -/
private lemma iK_norm_le' (A B : ℝ) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    ‖iK A B m n‖ ≤ 2 * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)| := by
  have hθ : iTheta m n ≠ 0 := iTheta_ne_zero hm hn hmn
  refine (iK_norm_le A B m n hθ).trans ?_
  have hLne : Real.log (m : ℝ) - Real.log (n : ℝ) ≠ 0 := by
    intro hc
    exact hmn (by
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have := Real.log_injOn_pos hm0 hn0 (by linarith)
      exact_mod_cast this)
  have hD : 0 < |(m : ℝ) - (n : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hmn))
  have hL : 0 < |Real.log (m : ℝ) - Real.log (n : ℝ)| := abs_pos.mpr hLne
  have hkey := abs_sub_le_max_mul_abs_log_sub m n hm hn
  have hsub : iTheta m n = -(Real.log (m : ℝ) - Real.log (n : ℝ)) := by
    rw [iTheta]; ring
  rw [hsub, abs_neg, div_le_div_iff₀ hL hD]
  nlinarith [hkey]

/-- Split the double sum into its diagonal and off-diagonal parts. -/
private lemma iPhi_split (b : ℕ → ℂ) (N : ℕ) (A B : ℝ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (b m * (starRingEnd ℂ) (b n)) * iK A B m n)
      = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (b m * (starRingEnd ℂ) (b n)) * iK A B m n)
        + ∑ m ∈ Finset.Icc 1 N, (b m * (starRingEnd ℂ) (b m)) * iK A B m m := by
  have h1 : ∀ m ∈ Finset.Icc 1 N,
      (∑ n ∈ Finset.Icc 1 N, (b m * (starRingEnd ℂ) (b n)) * iK A B m n)
        = (∑ n ∈ (Finset.Icc 1 N).erase m, (b m * (starRingEnd ℂ) (b n)) * iK A B m n)
          + (b m * (starRingEnd ℂ) (b m)) * iK A B m m := by
    intro m hm
    exact (Finset.sum_erase_add _ _ hm).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]

/-- The diagonal part evaluates to `(B - A) · ∑ ‖b n‖²`. -/
private lemma iPhi_diag (b : ℕ → ℂ) (N : ℕ) (A B : ℝ) :
    (∑ m ∈ Finset.Icc 1 N, (b m * (starRingEnd ℂ) (b m)) * iK A B m m)
      = ↑((B - A) * ∑ m ∈ Finset.Icc 1 N, ‖b m‖ ^ 2) := by
  simp only [iK_self]
  have hstep : ∀ m, (b m * (starRingEnd ℂ) (b m)) * ((B - A : ℝ) : ℂ) = ↑((B - A) * ‖b m‖ ^ 2) := by
    intro m
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  simp only [hstep]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The real part of the integral of the double sum, split into diagonal and off-diagonal. -/
private lemma main_integral (b : ℕ → ℂ) (N : ℕ) (A B : ℝ) :
    (∫ t in A..B, iPhi b N t).re
      = (B - A) * (∑ m ∈ Finset.Icc 1 N, ‖b m‖ ^ 2)
        + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (b m * (starRingEnd ℂ) (b n)) * iK A B m n).re := by
  rw [iPhi_integral, iPhi_split, Complex.add_re, iPhi_diag]
  simp only [Complex.ofReal_re]
  ring

/-- **The exact mean value identity** for the Dirichlet polynomial integral over `[A,B]`. -/
private lemma integral_identity (b : ℕ → ℂ) (N : ℕ) (A B : ℝ) :
    (∫ t in A..B, ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
      = (B - A) * (∑ m ∈ Finset.Icc 1 N, ‖b m‖ ^ 2)
        + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (b m * (starRingEnd ℂ) (b n)) * iK A B m n).re := by
  rw [← main_integral]
  rw [show (∫ t in A..B, ‖∑ n ∈ Finset.Icc 1 N,
        b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
      = ∫ t in A..B, (iPhi b N t).re from
    intervalIntegral.integral_congr (fun t _ => iPhi_expansion b N t)]
  exact Commons.Analysis.Complex.intervalIntegral_re_comm (iPhi b N) A B (iPhi_continuous b N)

/-- **Off-diagonal bound** in the sharp Montgomery kernel form. -/
private lemma ioffdiag_bound (b : ℕ → ℂ) (N : ℕ) (A B : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        (b m * (starRingEnd ℂ) (b n)) * iK A B m n‖
      ≤ 2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := by
  refine offdiag_kernel_sum_bound b N (iK A B) ?_
  intro m n hm hn hmn
  obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
  exact iK_norm_le' A B m n hm1 hn1 hmn

/-- **Montgomery's mean value bound for a Dirichlet polynomial, in the sharp "1/log" kernel form,
on an arbitrary interval `[A,B]`.**  There is an absolute `C > 0` such that for all `b : ℕ → ℂ`,
all `N`, and all `A ≤ B`,
`|∫_A^B ‖∑_{n≤N} b n · n^{-it}‖² dt − (B−A) ∑_{n≤N} ‖b n‖²|`
`  ≤ C · ∑_{m≤N} ∑_{n≤N} ‖b m‖ ‖b n‖ · max(m,n)/|m−n|`  (the diagonal `m = n` is junk-zero).

Route: the exact expansion `∫_A^B ‖z‖² = (B−A)∑‖b n‖² + Re ∑_{m≠n} b m conj(b n) ∫_A^B (n/m)^{-it} dt`
(this is the same computation as in `Submission/Work/ZeroDensity/Zeta/dirichletPoly_meanValue_integral_corrected.lean`,
whose private lemmas `mvPhi_expansion`, `mvPhi_integral`, `mvPhi_split`, `mvPhi_diag`, `mvK_norm_le`,
`mvK_norm_le'`, `integral_identity` can be copied/adapted; the shift `t ↦ A + t` reduces to the
interval `0..(B−A)`, the shift being absorbed into the coefficients `b n · n^{-iA}`, which have the
same moduli because `‖n^{-iA}‖ = 1` (`Complex.norm_natCast_cpow_of_pos`));
the off-diagonal integral is `(e^{iBθ} − e^{iAθ})/(iθ)` with `θ = log(n/m) ≠ 0`, so it is at most
`2/|log(n/m)|`, and `|log(n/m)| ≥ |n−m|/max(m,n)` gives `2/|log(n/m)| ≤ 2 max(m,n)/|m−n|`.
This is sharper than the `C·N·log(N+2)·∑‖b n‖²` error term of the existing corrected theorem:
the `max(m,n)/|m−n|` kernel is what makes the subsequent divisor-sum bound work.
The intended use is with `b n = c n · n^{-1/2}`, `A = -1`, `B = T+1`. -/
theorem dirPolyIntervalMeanValueBound : ∃ C : ℝ, 0 < C ∧
    ∀ (b : ℕ → ℂ) (N : ℕ) (A B : ℝ), A ≤ B →
      |(∫ t in A..B, ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
        - (B - A) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2|
      ≤ C * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := by
  refine ⟨2, by norm_num, ?_⟩
  intro b N A B _hAB
  have hkey := integral_identity b N A B
  have hb := ioffdiag_bound b N A B
  have hEq : (∫ t in A..B, ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
      - (B - A) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2
      = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (b m * (starRingEnd ℂ) (b n)) * iK A B m n).re := by
    rw [hkey]; ring
  rw [hEq]
  calc |(∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (b m * (starRingEnd ℂ) (b n)) * iK A B m n).re|
      ≤ ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (b m * (starRingEnd ℂ) (b n)) * iK A B m n‖ := Complex.abs_re_le_norm _
    _ ≤ 2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := hb

end

end Work.ZeroDensity.Ingham
