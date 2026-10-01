import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

/-- `|P_r| ≤ 1/r`: the coefficient `P_r = [r ⟂ t]·μ(r)/kap(r)` of the row sums is bounded by
`1/r`.  Indeed if `r` is not squarefree then `μ(r) = 0`; otherwise `|μ(r)| = 1` and
`kap r = ∏_{p | r}(p+1) ≥ ∏_{p | r} p = r`. -/
lemma rowCoef_abs_le {t r : ℕ} (hr : 1 ≤ r) :
    |Work.ZeroDensity.Jutila.LzDiffAux.rowCoef t r| ≤ 1 / (r : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hmu : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  unfold Work.ZeroDensity.Jutila.LzDiffAux.rowCoef
  by_cases hc : Nat.Coprime r t
  · rw [if_pos hc]
    by_cases hs : Squarefree r
    · have hkap : (r : ℝ) ≤ Work.ZeroDensity.Jutila.kap r :=
        Work.ZeroDensity.Jutila.BzCross.kap_ge_self hs
      have hkpos : (0 : ℝ) < Work.ZeroDensity.Jutila.kap r :=
        Work.ZeroDensity.Jutila.kap_pos r
      rw [abs_div, abs_of_pos hkpos]
      have h1 : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| / Work.ZeroDensity.Jutila.kap r
          ≤ 1 / Work.ZeroDensity.Jutila.kap r :=
        div_le_div_of_nonneg_right hmu hkpos.le
      have h2 : 1 / Work.ZeroDensity.Jutila.kap r ≤ 1 / (r : ℝ) :=
        one_div_le_one_div_of_le hr0 hkap
      linarith
    · have h0 : (ArithmeticFunction.moebius r : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; norm_num
      rw [h0, zero_div, abs_zero]
      exact le_of_lt (one_div_pos.mpr hr0)
  · rw [if_neg hc, abs_zero]
    exact le_of_lt (one_div_pos.mpr hr0)

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
