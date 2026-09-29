import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C7.g_form
import Submission.Work.C7.evA_Lps

namespace Work.A14D

open Complex Metric

theorem pullback_B3_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDTPlan.B3.subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ n)
      (-(Complex.log (1 - z)) ^ 2 / 2) := by
  have hB3 : Submission.CDTPlan.B3.subst Submission.CDT.sympY
      = -(PowerSeries.C (1 / 2 : ℚ)) * (Work.C7.Lps * Work.C7.Lps) := by
    have hg2 : Work.C7.g 2 = Submission.CDTPlan.B3.subst Submission.CDT.sympY := by
      simp [Work.C7.g, Submission.CDTPlan.pureB, Work.C7.yps]
    rw [← hg2, Work.C7.g_form.2.1, pow_two]
  set F : ℕ → ℂ := fun n => ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n with hF
  have hL : HasSum F (Complex.log (1 - z)) := Work.C7.hasSum_Lps hz
  have hLs : Summable F := hL.summable
  have hLn : Summable fun n => ‖F n‖ := hL.summable.norm
  have hprod : Summable (fun n : ℕ =>
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl.1 * F kl.2) :=
    summable_sum_mul_antidiagonal_of_summable_norm' (f := F) (g := F) hLn hLs hLn hLs
  have hval : (∑' n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl.1 * F kl.2)
      = (Complex.log (1 - z)) ^ 2 := by
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'
      (f := F) (g := F) hLn hLs hLn hLs, hL.tsum_eq]
    ring
  have hcoeff : ∀ n : ℕ,
      ((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n
        = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl.1 * F kl.2 := by
    intro n
    rw [PowerSeries.coeff_mul]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    simp only [hF]
    rw [← hp', pow_add]
    ring
  have hLL : HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n)
      ((Complex.log (1 - z)) ^ 2) := by
    have h := hprod.hasSum
    rw [hval] at h
    exact h.congr_fun (fun n => hcoeff n)
  have hhalf : HasSum (fun n : ℕ =>
      (-(1 / 2 : ℂ)) * (((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n))
      (-(Complex.log (1 - z)) ^ 2 / 2) := by
    have h := hLL.mul_left (-(1 / 2 : ℂ))
    rw [show (-(1 / 2 : ℂ)) * (Complex.log (1 - z)) ^ 2
        = -(Complex.log (1 - z)) ^ 2 / 2 by ring] at h
    exact h
  have hhalf' : HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (-(PowerSeries.C (1 / 2 : ℚ)) * (Work.C7.Lps * Work.C7.Lps)) : ℚ) : ℂ)
        * z ^ n)
      (-(Complex.log (1 - z)) ^ 2 / 2) := by
    refine hhalf.congr_fun (fun n => ?_)
    rw [show (-(PowerSeries.C (1 / 2 : ℚ)) : PowerSeries ℚ) = PowerSeries.C (-(1 / 2 : ℚ)) by simp]
    rw [PowerSeries.coeff_C_mul]
    push_cast
    ring
  refine hhalf'.congr_fun (fun n => ?_)
  rw [hB3]

end Work.A14D
