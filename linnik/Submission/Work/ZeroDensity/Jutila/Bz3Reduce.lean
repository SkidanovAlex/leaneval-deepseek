/-
# The `κ`-form of the summands of `s3exact` / `s3cont`

For squarefree coprime `r,t` one has `s3c (r*t) = ζ(2)⁻¹ (r/κ(r))(t/κ(t))`
(`Bz3Defs.s3c_mul_eq_of_coprime`); since the coprimality indicator already vanishes off the
coprime pairs and `μ(r)μ(t) = 0` kills the non-squarefree ones, this identity may be applied
term by term.  The results below are the two sums in the "good weight" form that the Abel
summation consumes.
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- Pointwise `κ`-form of the summand of `s3cont`. -/
lemma summand_cont_eq_kappa (q r t z N : ℕ) :
    (if Nat.Coprime r t then
        (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
      (LinnikAreas.Density4.BzS3.s3c (r * t) * ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) *
        ((Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)) - 1) *
            (Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)) - 1) + 1))
    = (if Nat.Coprime r t then
        (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
      ((Real.pi ^ 2 / 6)⁻¹ * (((r : ℝ) / kap r) * ((t : ℝ) / kap t)) *
        (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) *
          ((Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)) - 1) *
              (Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)) - 1) + 1))) := by
  by_cases hc : Nat.Coprime r t
  · rw [if_pos hc]
    by_cases hr : ArithmeticFunction.moebius r = 0
    · simp [hr]
    · by_cases ht : ArithmeticFunction.moebius t = 0
      · simp [ht]
      · have hsr : Squarefree r := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hr
        have hst : Squarefree t := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp ht
        rw [s3c_mul_eq_of_coprime hsr hst hc]
        ring
  · simp [hc]

/-- Pointwise `κ`-form of the summand of `s3exact`. -/
lemma summand_exact_eq_kappa (q r t z N : ℕ) :
    (if Nat.Coprime r t then
        (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
      (LinnikAreas.Density4.BzS3.s3c (r * t) * ((N / (q * r * t) : ℕ) : ℝ) *
        ((Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1) *
            (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1))
    = (if Nat.Coprime r t then
        (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
      ((Real.pi ^ 2 / 6)⁻¹ * (((r : ℝ) / kap r) * ((t : ℝ) / kap t)) *
        (((N / (q * r * t) : ℕ) : ℝ) *
          ((Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1) *
              (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1))) := by
  by_cases hc : Nat.Coprime r t
  · rw [if_pos hc]
    by_cases hr : ArithmeticFunction.moebius r = 0
    · simp [hr]
    · by_cases ht : ArithmeticFunction.moebius t = 0
      · simp [ht]
      · have hsr : Squarefree r := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hr
        have hst : Squarefree t := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp ht
        rw [s3c_mul_eq_of_coprime hsr hst hc]
        ring
  · simp [hc]

/-- `s3cont` in `κ`-form. -/
lemma s3cont_eq_kappa (z N : ℕ) :
    s3cont z N = (Real.pi ^ 2 / 6)⁻¹ *
      ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (if Nat.Coprime r t then
              (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
            (((r : ℝ) / kap r) * ((t : ℝ) / kap t) *
              (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) *
                ((Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)) - 1) *
                    (Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)) - 1)
                  + 1))) := by
  unfold s3cont
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [summand_cont_eq_kappa q r t z N]
  ring

/-- `s3exact` in `κ`-form. -/
lemma s3exact_eq_kappa (z N : ℕ) :
    s3exact z N = (Real.pi ^ 2 / 6)⁻¹ *
      ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (if Nat.Coprime r t then
              (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
            (((r : ℝ) / kap r) * ((t : ℝ) / kap t) *
              (((N / (q * r * t) : ℕ) : ℝ) *
                ((Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1) *
                    (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1))) := by
  unfold s3exact
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [summand_exact_eq_kappa q r t z N]
  ring

end

end Work.ZeroDensity.Jutila
