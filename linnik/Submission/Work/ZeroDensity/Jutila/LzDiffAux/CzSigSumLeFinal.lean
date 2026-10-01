import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux
import Submission.Work.ZeroDensity.Jutila.SigmaHalfAvg
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzAbelHard

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset

/-- `czSig` is the same divisor sum as `sigmaHalf`: `σ_{-1/2}(t) = Σ_{d | t} d^{-1/2}`. -/
lemma czSig_eq_sigmaHalf (t : ℕ) :
    Work.ZeroDensity.Jutila.BzCross.czSig t = Work.LinnikAreas.Density4.sigmaHalf t := by
  simp [Work.ZeroDensity.Jutila.BzCross.czSig, Work.LinnikAreas.Density4.sigmaHalf]

theorem CzSigSumLeFinal :
    ∀ M : ℕ, (∑ r ∈ Finset.Icc 1 M, Work.ZeroDensity.Jutila.BzCross.czSig r) ≤ 3 * (M : ℝ) := by
  intro M
  rw [show (∑ r ∈ Finset.Icc 1 M, Work.ZeroDensity.Jutila.BzCross.czSig r)
      = ∑ r ∈ Finset.Icc 1 M, Work.LinnikAreas.Density4.sigmaHalf r from
        Finset.sum_congr rfl (fun r _ => czSig_eq_sigmaHalf r)]
  rw [Work.ZeroDensity.Jutila.sum_sigmaHalf_eq M]
  calc ∑ d ∈ Finset.Icc 1 M, ((M / d : ℕ) : ℝ) * (1 / Real.sqrt (d : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 M, (M : ℝ) * (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hcast : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) := Nat.cast_div_le
        have hnn : (0 : ℝ) ≤ 1 / Real.sqrt (d : ℝ) := by positivity
        calc ((M / d : ℕ) : ℝ) * (1 / Real.sqrt (d : ℝ))
            ≤ ((M : ℝ) / (d : ℝ)) * (1 / Real.sqrt (d : ℝ)) :=
              mul_le_mul_of_nonneg_right hcast hnn
          _ = (M : ℝ) * (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
              have hs : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdpos)
              have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdpos
              field_simp
    _ = (M : ℝ) * ∑ d ∈ Finset.Icc 1 M, 1 / ((d : ℝ) * Real.sqrt (d : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left (cz_sum_inv_mul_sqrt_le M) (Nat.cast_nonneg M)
    _ = 3 * (M : ℝ) := by ring

end Work.ZeroDensity.Jutila.LzDiffAux
