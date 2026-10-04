import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.wt_pow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Symbol calculus on the torus: the flat Laplacian symbol `λ`

This is the vocabulary layer for the *flat* commutator estimate
`Work.Diff.STE.B3.SymCalcStep1.laplacian_pow_mul_comm_le` (the "Leibniz" piece of the symbol
calculus of `Submission/Work/Diff/STE/B3/SymCalc.lean`).

The flat Laplacian on the torus has symbol

  `lam m = Σⱼ (2π mⱼ)²`   (`m : ι → ℤ` a frequency),

so that `lam m = (2π)² (wt m - 1)`, in particular `0 ≤ lam m` and `lam m ≤ (2π)² wt m`.
The multiplier with symbol `lam^k` is written `cLam k` (a complex-valued family on the lattice);
it is the Fourier side of `Λ^k`, `Λ` the flat Laplacian.

Only elementary facts are recorded here: nonnegativity, the comparison with the slowly varying
weight `wt`, the norm of `cLam`, and the Peetre-type inequality for `wt`.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep1

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The symbol of the flat Laplacian: `lam m = Σⱼ (2π mⱼ)²`. -/
def lam (m : ι → ℤ) : ℝ := ∑ j, (2 * Real.pi * (m j : ℝ)) ^ 2

/-- The multiplier with symbol `lam^k`, as a complex-valued family on the lattice. -/
def cLam (k : ℕ) (m : ι → ℤ) : ℂ := ((lam m ^ k : ℝ) : ℂ)

lemma lam_nonneg (m : ι → ℤ) : 0 ≤ lam m :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

lemma lam_eq (m : ι → ℤ) :
    lam m = (2 * Real.pi) ^ 2 * ∑ j, (((m j : ℤ)) : ℝ) ^ 2 := by
  simp only [lam, mul_pow, Finset.mul_sum]

lemma sum_sq_le_wt (m : ι → ℤ) :
    (∑ j, (((m j : ℤ)) : ℝ) ^ 2) ≤ Work.Diff.STE.wt m := by
  simp only [Work.Diff.STE.wt]
  linarith [show (0:ℝ) ≤ 1 by norm_num]

lemma lam_le (m : ι → ℤ) : lam m ≤ (2 * Real.pi) ^ 2 * Work.Diff.STE.wt m := by
  rw [lam_eq]
  exact mul_le_mul_of_nonneg_left (sum_sq_le_wt m) (sq_nonneg _)

lemma cLam_norm (k : ℕ) (m : ι → ℤ) : ‖cLam k m‖ = lam m ^ k := by
  rw [cLam, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (lam_nonneg m) k)]

lemma wt_pos (m : ι → ℤ) : 0 < Work.Diff.STE.wt m := Work.Diff.STE.wt_pos m

lemma wt_one_le (m : ι → ℤ) : 1 ≤ Work.Diff.STE.wt m := Work.Diff.STE.wt_one_le m

/-- Peetre's inequality for the weight, in the direction used below:
`wt m ≤ 2 · wt (m - j) · wt j`. -/
lemma wt_le_peetre (m j : ι → ℤ) :
    Work.Diff.STE.wt m ≤ 2 * (Work.Diff.STE.wt j * Work.Diff.STE.wt (m - j)) :=
  Work.Diff.STE.wt_le_two_mul m j

/-- The difference of the symbols, as a complex multiplier. -/
def dlam (k : ℕ) (m j : ι → ℤ) : ℂ := ((lam m ^ k - lam j ^ k : ℝ) : ℂ)

lemma cLam_sub (k : ℕ) (m j : ι → ℤ) : cLam k m - cLam k j = dlam k m j := by
  rw [cLam, cLam, dlam, Complex.ofReal_sub]

lemma dlam_norm (k : ℕ) (m j : ι → ℤ) : ‖dlam k m j‖ = |lam m ^ k - lam j ^ k| := by
  rw [dlam, Complex.norm_real, Real.norm_eq_abs]

end Work.Diff.STE.B3.SymCalcStep1
