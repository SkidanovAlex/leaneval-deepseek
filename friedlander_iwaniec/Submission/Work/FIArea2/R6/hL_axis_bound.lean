/-
# `Work.FIArea2.R6.hL_axis_bound`

The axis part of the §9 `h`-sum of Friedlander–Iwaniec: the contribution of the tuples
`(u1,u2,h1,h2) ∈ [-R,R]² × [-X,X] × [-Y,Y]` having at least one vanishing coordinate,
weighted by `gcd(|u1|,|u2|)` and by `τ(u1h1²-u2h2²)⁴`, is bounded by
`C R² X Y (1 + log(R+X+Y+2))^1000`.

The sum is rearranged (`gcd` pulled out of the inner `h`-sum) and identified with the sum of
`Work.FIArea2.R6.hbox6_axis`, which gives the sharper bound with exponent `300`; the extra
slack is absorbed by `300 ≤ 1000` and `1 ≤ log(R+X+Y+2)`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.hbox6_axis

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

/-- `g * (if A then t else 0) = (if A then g else 0) * t`. -/
private lemma mul_ite_zero_mul (A : Prop) [Decidable A] (g t : ℝ) :
    g * (if A then t else 0) = (if A then g else 0) * t := by
  by_cases h : A <;> simp [h]

theorem hL_axis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (R X Y : ℕ), 1 ≤ R → 1 ≤ X → 1 ≤ Y →
      (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
              then (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)
              else 0)))
      ≤ C * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000 := by
  obtain ⟨C, hCpos, hC⟩ := hbox6_axis
  refine ⟨C, hCpos, ?_⟩
  intro R X Y hR hX hY
  -- the `gcd` weight does not depend on `h1,h2`, so it can be pulled out of the inner sum
  have hrewrite :
      (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
              then (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)
              else 0)))
      = (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
          ∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
                then (Nat.gcd u1.natAbs u2.natAbs : ℝ) else 0)
              * (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)) := by
    refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun u2 _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h1 _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h2 _ => mul_ite_zero_mul _ _ _)
  -- the logarithm of the argument is at least `1`
  have hlog1 : (1 : ℝ) ≤ Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hpos : (0 : ℝ) < (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by linarith
    rw [Real.le_log_iff_exp_le hpos]
    linarith [Real.exp_one_lt_three]
  have hpowlog : (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300
      ≤ (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000 := by
    have h0 : (0 : ℝ) ≤ Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by linarith
    have h1 : (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300
        ≤ (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000 :=
      pow_le_pow_right₀ hlog1 (by norm_num)
    have h2 : (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000
        ≤ (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000 :=
      pow_le_pow_left₀ h0 (by linarith) 1000
    exact le_trans h1 h2
  calc (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
              then (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)
              else 0)))
      = (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
          ∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
                then (Nat.gcd u1.natAbs u2.natAbs : ℝ) else 0)
              * (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)) := hrewrite
    _ ≤ C * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := hC R hR X hX Y hY
    _ ≤ C * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000 :=
        mul_le_mul_of_nonneg_left hpowlog (by positivity)

end

end Work.FIArea2.R6
