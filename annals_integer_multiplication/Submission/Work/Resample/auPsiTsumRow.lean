import Mathlib
import Submission.Work.Resample.auRowDefs
import Submission.Work.ResMath.resA_norm_le
import Submission.Work.ResMath.resS_rowsum_reindex

/-!
# The full Gaussian row sum of `auPsi` (`Work.Resample.auPsiTsumRow`)

For `s > 0`, `α > 0` and `k : Fin t`, the total Gaussian weight

`∑' n : ℤ, auPsi α s t k n = (1/(2α))·∑' n, e^{−π (n − s k/t)²/α²}`

equals the `k`-th row sum `∑ j : Fin s, ‖(resA s t α) k j‖` of the Gaussian resampling
matrix `resA = S/2`.  The identification is by definition of `resA`, `resSmat`, `auPsi`
together with the reindexing lemma `Work.ResMath.resS_rowsum_reindex` for the row sums
of `resSmat` (§4.2 step (c) of Harvey–van der Hoeven).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Resample

theorem auPsiTsumRow (α s t : ℕ) (hs : 0 < s) (hα : 0 < α) (k : Fin t) :
    ∑' n : ℤ, Work.Resample.auPsi α s t (k : ℕ) n = ∑ j : Fin s, ‖(HvdH.resA s t α) k j‖ := by
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  have hnorm1 : ∀ x : ℝ, ‖((x : ℂ))‖ = |x| := fun x => RCLike.norm_ofReal x
  -- The left-hand side: pull out the constant `1/(2α)` from the `tsum`.
  have hL : (∑' n : ℤ, auPsi α s t (k : ℕ) n)
      = (1 / (2 * (α : ℝ))) * ∑' n : ℤ, Real.exp (-(Real.pi / (α : ℝ) ^ 2) *
          ((n : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ)) ^ 2) := by
    have h1 : (∑' n : ℤ, auPsi α s t (k : ℕ) n)
        = ∑' n : ℤ, (1 / (2 * (α : ℝ))) * Real.exp (-(Real.pi / (α : ℝ) ^ 2) *
            ((n : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ)) ^ 2) := by
      apply tsum_congr; intro n; simp only [auPsi]
    rw [h1, tsum_mul_left]
  -- Reindex the single `ℤ`-sum into the double `Fin s × ℤ`-sum over the row of `resSmat`.
  have hreindex : (∑' n : ℤ, Real.exp (-(Real.pi / (α : ℝ) ^ 2) *
          ((n : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ)) ^ 2))
      = ∑ j : Fin s, ∑' q : ℤ, Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
          ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) := by
    have h1 : (∑' n : ℤ, Real.exp (-(Real.pi / (α : ℝ) ^ 2) *
          ((n : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ)) ^ 2))
        = ∑' n : ℤ, Real.exp (-(Real.pi / (α : ℝ) ^ 2) *
          ((s : ℝ) * ((k : ℝ) / (t : ℝ)) - (n : ℝ)) ^ 2) := by
      apply tsum_congr; intro n
      apply congrArg Real.exp
      ring
    rw [h1, Work.ResMath.resS_rowsum_reindex s hs (α : ℝ) hαR ((k : ℝ) / (t : ℝ))]
  -- Each entry of `resA` is `(1/(2α))` times the real theta sum of the corresponding `resSmat` entry.
  have hstep : ∀ j : Fin s, ‖(HvdH.resA s t α) k j‖
      = (1 / (2 * (α : ℝ))) * ∑' q : ℤ, Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
          ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) := by
    intro j
    have hA : (HvdH.resA s t α) k j = (1 / 2 : ℂ) * HvdH.resSmat s t α k j := by
      simp only [HvdH.resA, Matrix.smul_apply, smul_eq_mul]
    rw [hA, norm_mul, Work.ResMath.resSmat_apply]
    rw [show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    have hT : (0 : ℝ) ≤ ∑' q : ℤ, Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
            ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) :=
        tsum_nonneg fun q => Real.exp_nonneg _
    rw [hnorm1, abs_of_nonneg (mul_nonneg (by positivity) hT)]
    have hcoef : (1 / (2 * (α : ℝ))) = (1 / 2) * (1 / (α : ℝ)) := by
      have hαne : (α : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hcoef]; ring
  -- Assemble: the row sum of `resA` is `(1/(2α))` times the double sum computed above.
  have hR : (∑ j : Fin s, ‖(HvdH.resA s t α) k j‖)
      = (1 / (2 * (α : ℝ))) * ∑ j : Fin s, ∑' q : ℤ,
          Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
            ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hstep j)
  rw [hL, hreindex, hR]

end Work.Resample
