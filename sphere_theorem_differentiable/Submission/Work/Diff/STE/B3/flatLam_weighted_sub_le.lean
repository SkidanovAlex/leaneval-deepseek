import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep1.Defs
import Submission.Work.Diff.STE.B3.flatLam_core
import Submission.Work.Diff.STE.B3.sqrt_wt_sub_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weighted symbol-difference bound for `λ^k`

`λ(m) = Σⱼ (2π mⱼ)²` is the symbol of the flat Laplacian on the torus (`SymCalcStep1.lam`) and
`wt m = 1 + Σⱼ mⱼ²` is the Sobolev weight (`Work.Diff.STE.wt`).  This file proves the **weighted**
symbol-difference estimate used by the symbol calculus of
`Submission/Work/Diff/STE/B3/SymCalc.lean`: with `‖m - n‖ = √(Σᵢ (mᵢ - nᵢ)²)` one has

  `|λ(m)^k - λ(n)^k| ≤ 2k (2π)^{2k} 3^k · (1 + ‖m - n‖)^{2k} · ⟨m⟩^{k-1} ⟨n⟩^k`,  `⟨m⟩ = √(wt m)`.

Unlike the unweighted `flatLam_pow_sub_bound` (`≲ ‖m-n‖ (‖m‖+‖n‖)^{2k-1}`), the weight powers here
are `k - 1` and `k` — only *half* the order — which forces the factor `(1 + ‖m - n‖)^{2k}`: this is a
Peetre-type inequality in which the *difference* of the frequencies controls their size whenever
they are far apart, so no polynomial loss in `⟨m⟩` is needed.

## Proof

Write `A = ⟨m⟩`, `B = ⟨n⟩`, `w = ‖m - n‖`, `u = ‖m‖`, `v = ‖n‖`.  Then
`λ(m) = (2π)² u² = (2π)² (A² - 1)`, and the whole content is the *pure real* inequality

  `flatLam_core`  :  `|(A² - 1)^k - (B² - 1)^k| ≤ 2k 3^k (1 + w)^{2k} A^{k-1} B^k`,  `A, B ≥ 1`,
                                                                                    `|A - B| ≤ w`,

proved in `Submission/Work/Diff/STE/B3/flatLam_core.lean` by the mean-value bound
`|x^k - y^k| ≤ k M^{k-1} |x - y|` with `x = A² - 1`, `y = B² - 1`, `M = max(A,B)²`:
* `|x - y| = |A - B| (A + B) ≤ 2 w max(A,B)`;
* hence `|x^k - y^k| ≤ 2 k w max(A,B)^{2k-1}`;
* `max(A,B) ≤ (1 + w) min(A,B)` (because `|A - B| ≤ w` and `min ≥ 1`), and
  `min(A,B)^{2k-1} = min^{k-1} min^k ≤ A^{k-1} B^k`;
* `w (1 + w)^{2k-1} ≤ 3^k (1 + w)^{2k}` (since `w ≤ 1 + w ≤ 3^k (1 + w)`).

Its two inputs are supplied here:
* `one_le_sqrt_wt` : `1 ≤ ⟨m⟩`, and `lam_eq_sqrt_wt` : `λ(m) = (2π)² (⟨m⟩² - 1)`;
* `sqrt_wt_sub_le` (`Submission/Work/Diff/STE/B3/sqrt_wt_sub_le.lean`) : `|⟨m⟩ - ⟨n⟩| ≤ ‖m - n‖`,
  the `ℓ²` fact that `x ↦ √(1+x²)` is `1`-Lipschitz (proved there from the reverse triangle
  inequality in `EuclideanSpace ℝ (Option ι)`, i.e. Cauchy–Schwarz).

The final multiplication by `(2π)^{2k} > 0` gives the target.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma one_le_sqrt_wt (m : ι → ℤ) : 1 ≤ Real.sqrt (Work.Diff.STE.wt m) := by
  rw [Real.one_le_sqrt]
  have : (0 : ℝ) ≤ ∑ i, (((m i : ℤ)) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Work.Diff.STE.wt]; linarith

/-- `λ(m) = (2π)² (⟨m⟩² - 1)`: the symbol of the flat Laplacian in terms of the weight. -/
lemma lam_eq_sqrt_wt (m : ι → ℤ) :
    Work.Diff.STE.B3.SymCalcStep1.lam m
      = (2 * Real.pi) ^ 2 * ((Real.sqrt (Work.Diff.STE.wt m)) ^ 2 - 1) := by
  rw [Work.Diff.STE.B3.SymCalcStep1.lam_eq]
  have h : (Real.sqrt (Work.Diff.STE.wt m)) ^ 2 - 1 = ∑ j, (((m j : ℤ)) : ℝ) ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt (Work.Diff.STE.wt_pos m)), Work.Diff.STE.wt]
    ring
  rw [h]

theorem flatLam_weighted_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (m n : ι → ℤ) :
    |Work.Diff.STE.B3.SymCalcStep1.lam m ^ k - Work.Diff.STE.B3.SymCalcStep1.lam n ^ k|
      ≤ (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k)
          * (1 + Real.sqrt (∑ i, (((m i - n i : ℤ)) : ℝ) ^ 2)) ^ (2 * k)
          * Real.sqrt (Work.Diff.STE.wt m) ^ (k - 1)
          * Real.sqrt (Work.Diff.STE.wt n) ^ k := by
  have hcore := flatLam_core k hk (one_le_sqrt_wt m) (one_le_sqrt_wt n)
    (Real.sqrt_nonneg _) (sqrt_wt_sub_le m n)
  have hm : Work.Diff.STE.B3.SymCalcStep1.lam m ^ k
      = (2 * Real.pi) ^ (2 * k) * ((Real.sqrt (Work.Diff.STE.wt m)) ^ 2 - 1) ^ k := by
    rw [lam_eq_sqrt_wt m, mul_pow, pow_mul]
  have hn : Work.Diff.STE.B3.SymCalcStep1.lam n ^ k
      = (2 * Real.pi) ^ (2 * k) * ((Real.sqrt (Work.Diff.STE.wt n)) ^ 2 - 1) ^ k := by
    rw [lam_eq_sqrt_wt n, mul_pow, pow_mul]
  have hfac : (0 : ℝ) ≤ (2 * Real.pi) ^ (2 * k) := by positivity
  rw [hm, hn, ← mul_sub, abs_mul, abs_of_nonneg hfac]
  calc (2 * Real.pi) ^ (2 * k)
        * |((Real.sqrt (Work.Diff.STE.wt m)) ^ 2 - 1) ^ k
            - ((Real.sqrt (Work.Diff.STE.wt n)) ^ 2 - 1) ^ k|
      ≤ (2 * Real.pi) ^ (2 * k)
          * (2 * (k : ℝ) * 3 ^ k
              * (1 + Real.sqrt (∑ i, (((m i - n i : ℤ)) : ℝ) ^ 2)) ^ (2 * k)
              * Real.sqrt (Work.Diff.STE.wt m) ^ (k - 1)
              * Real.sqrt (Work.Diff.STE.wt n) ^ k) :=
        mul_le_mul_of_nonneg_left hcore hfac
    _ = (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k)
          * (1 + Real.sqrt (∑ i, (((m i - n i : ℤ)) : ℝ) ^ 2)) ^ (2 * k)
          * Real.sqrt (Work.Diff.STE.wt m) ^ (k - 1)
          * Real.sqrt (Work.Diff.STE.wt n) ^ k := by ring

end Work.Diff.STE.B3
