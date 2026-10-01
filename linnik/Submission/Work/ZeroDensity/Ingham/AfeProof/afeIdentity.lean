import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeAux
import Submission.Work.ZeroDensity.Ingham.AfeProof.sawFourier
import Submission.Work.ZeroDensity.Ingham.zetaEMIntegral
import Submission.Work.ZeroDensity.Zeta.sinIntegralSubstBalanced

/-!
# The exact approximate-functional-equation identity for `ζ` at the balanced point

`Work.ZeroDensity.Ingham.AfeProof.afeIdentity`:

`ζ(1/2+it) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - N^{-s}/2 + (s/π)(2π)^s·Σ_k (k+1)^{s-1}·afeT(s, 2π(k+1)N)`

with `N = afeNt t`.  It combines the Euler–Maclaurin formula `zetaEMIntegral`, the sawtooth
Fourier expansion `afeSawtoothFourier` and the substitution `sinIntegralSubstBalanced`.
-/

namespace Work.ZeroDensity.Ingham.AfeProof

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The Euler–Maclaurin remainder, rewritten as the sawtooth–Fourier sum. -/
theorem afeIntegral_eq (t : ℝ) :
    -(cls t * ∫ u in Set.Ioi (afeNt t : ℝ),
        (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-(cls t) - 1))
      = (cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t) * afeTsum t := by
  have hsre : 0 < (cls t).re := cls_re_pos t
  have hsre1 : (cls t).re < 1 := cls_re_lt_one t
  have hN1 : 1 ≤ afeNt t := one_le_afeNt t
  have hInt := afeSawtoothFourier (s := cls t) hsre hsre1 (afeNt t) hN1
  have hterm : ∀ (k : ℕ),
      (1 / (Real.pi * ((k : ℝ) + 1))) *
          (∫ u in Set.Ioi (afeNt t : ℝ),
            ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ)
              * (u : ℂ) ^ (-(cls t) - 1))
        = ((2 * (Real.pi : ℂ)) ^ (cls t) / (Real.pi : ℂ)) * afeTerm t k := by
    intro k
    have hJ : (∫ u in Set.Ioi (afeNt t : ℝ),
          ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ)
            * (u : ℂ) ^ (-(cls t) - 1))
        = ((2 * (Real.pi : ℂ) * (((k + 1 : ℕ)) : ℂ))) ^ (cls t)
            * afeT (cls t) (2 * Real.pi * ((k + 1 : ℕ)) * (afeNt t : ℝ)) := by
      have h := Work.ZeroDensity.Zeta.sinIntegralSubstBalanced (s := cls t) hsre (afeNt t) hN1
        (k := k + 1) (Nat.succ_le_succ (Nat.zero_le k))
      simp only [afeT]
      convert h using 2 <;> push_cast <;> ring
    rw [hJ, afeTerm]
    push_cast
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have hm : ((((k : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    have hcast : ((k : ℂ) + 1) = ((((k : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast]
    have hA : (2 : ℂ) * (Real.pi : ℂ) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
    rw [hA]
    rw [Complex.mul_cpow_ofReal_nonneg h2pi hk1]
    rw [Complex.cpow_sub (cls t) 1 hm, Complex.cpow_one]
    field_simp
  have htsum :
      (∑' k : ℕ, (1 / (Real.pi * ((k : ℝ) + 1))) *
          (∫ u in Set.Ioi (afeNt t : ℝ),
            ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ)
              * (u : ℂ) ^ (-(cls t) - 1)))
        = ((2 * (Real.pi : ℂ)) ^ (cls t) / (Real.pi : ℂ)) * afeTsum t := by
    calc ∑' k : ℕ, (1 / (Real.pi * ((k : ℝ) + 1))) *
            (∫ u in Set.Ioi (afeNt t : ℝ),
              ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ)
                * (u : ℂ) ^ (-(cls t) - 1))
        = ∑' k : ℕ, ((2 * (Real.pi : ℂ)) ^ (cls t) / (Real.pi : ℂ)) * afeTerm t k :=
          tsum_congr hterm
      _ = ((2 * (Real.pi : ℂ)) ^ (cls t) / (Real.pi : ℂ)) * ∑' k : ℕ, afeTerm t k :=
          tsum_mul_left
      _ = ((2 * (Real.pi : ℂ)) ^ (cls t) / (Real.pi : ℂ)) * afeTsum t := by rw [afeTsum]
  rw [hInt, htsum]
  ring

/-- **The balanced approximate functional equation, exact identity form.** -/
theorem afeIdentity (t : ℝ) :
    riemannZeta (cls t) = afeMain t
      + ((afeNt t : ℂ) ^ (1 - cls t)) / (cls t - 1)
      - ((afeNt t : ℂ) ^ (-(cls t))) / 2
      + (cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t) * afeTsum t := by
  have hsre : 0 < (cls t).re := cls_re_pos t
  have hsne1 : cls t ≠ 1 := cls_ne_one t
  have hN1 : 1 ≤ afeNt t := one_le_afeNt t
  have hEM := zetaEMIntegral (s := cls t) hsre hsne1 (afeNt t) hN1
  have hkey : cls t * (∫ u in Set.Ioi (afeNt t : ℝ),
        (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-(cls t) - 1))
      = -((cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t) * afeTsum t) :=
    neg_eq_iff_eq_neg.mp (afeIntegral_eq t)
  rw [hEM, hkey]
  simp only [afeMain, sub_neg_eq_add]

end

end Work.ZeroDensity.Ingham.AfeProof
