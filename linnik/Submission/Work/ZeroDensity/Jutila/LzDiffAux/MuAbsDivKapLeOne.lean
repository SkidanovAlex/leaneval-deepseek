import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.LzAux.SigHalfLogAux.kappa_ge_self

namespace Work.ZeroDensity.Jutila.LzDiffAux

/-- The Möbius function vanishes off the squarefree integers, and on a squarefree `t` its
absolute value is `1` while `t ≤ ∏_{p | t} (p+1) = kap t`.  Hence `|μ t| * t ≤ kap t`. -/
private lemma absMu_mul_self_le_kap (t : ℕ) :
    |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * (t : ℝ) ≤ Work.ZeroDensity.Jutila.kap t := by
  by_cases h : Squarefree t
  · have h1 : |((ArithmeticFunction.moebius t : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree h]
      norm_num
    rw [h1, one_mul]
    exact Work.ZeroDensity.Jutila.LzAux.SigHalfLogAux.kappa_ge_self h
  · have h0 : ((ArithmeticFunction.moebius t : ℤ) : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
      simp
    rw [h0]
    simp only [abs_zero, zero_mul]
    exact le_of_lt (Work.ZeroDensity.Jutila.kap_pos t)

theorem MuAbsDivKapLeOne (t : ℕ) :
    |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) ≤ 1 := by
  have hk := Work.ZeroDensity.Jutila.kap_pos t
  rw [mul_div_assoc', div_le_one hk]
  exact absMu_mul_self_le_kap t

end Work.ZeroDensity.Jutila.LzDiffAux
