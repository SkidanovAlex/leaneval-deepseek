/-
# `Work.FIArea2.R6.hbox6_axis`

The "axis" part of the box sum of Friedlander-Iwaniec: the contribution of the
tuples `(u1,u2,h1,h2)` in `[-R,R]² × [-X,X] × [-Y,Y]` in which at least one of the four
coordinates vanishes, weighted by `gcd(|u1|,|u2|)` and by the fourth power of the
divisor function of `u1 h1² - u2 h2²`.
-/
import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea2.Count.sec9_box4_rect_helpers
import Submission.Work.FIArea2.R6.Hbox6AxisDefs

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable
set_option exponentiation.threshold 600

namespace Hbox6Axis

open Work.FIArea2.R6.Hbox6Axis

/-- The four-fold indicator splits into the four disjoint slices `A1`-`A4`. -/
lemma axis_split (R X Y : ℕ) :
    AxisSum R X Y = A1 R X Y + A2 R X Y + A3 R X Y + A4 R X Y := by
  have hpt : ∀ u1 u2 h1 h2 : ℤ,
      (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0 then gcdZ u1 u2 else 0)
          * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4
        = (if u1 = 0 then gcdZ u1 u2 else 0) * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4
          + (if u1 ≠ 0 ∧ u2 = 0 then gcdZ u1 u2 else 0)
              * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4
          + (if (u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 = 0 then gcdZ u1 u2 else 0)
              * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4
          + (if ((u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 ≠ 0) ∧ h2 = 0 then gcdZ u1 u2 else 0)
              * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4 := by
    intro u1 u2 h1 h2
    rw [indicator_split (gcdZ u1 u2) u1 u2 h1 h2]
    ring
  rw [AxisSum, A1, A2, A3, A4]
  rw [show (∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
        (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0 then gcdZ u1 u2 else 0)
          * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4)
      = (∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
          ((if u1 = 0 then gcdZ u1 u2 else 0) * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4
            + (if u1 ≠ 0 ∧ u2 = 0 then gcdZ u1 u2 else 0)
                * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4
            + (if (u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 = 0 then gcdZ u1 u2 else 0)
                * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4
            + (if ((u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 ≠ 0) ∧ h2 = 0 then gcdZ u1 u2 else 0)
                * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4)) from
      Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun u2 _ =>
        Finset.sum_congr rfl (fun h1 _ => Finset.sum_congr rfl (fun h2 _ =>
          hpt u1 u2 h1 h2))))]
  exact sum4_add4 (boxZ R) (boxZ R) (boxZ X) (boxZ Y) _ _ _ _

/-- `A1 ≤ 3X · Uweight R Y`: the `u1 = 0` slice. -/
lemma A1_le (R X Y : ℕ) (hX : 1 ≤ X) :
    A1 R X Y ≤ 3 * (X : ℝ) * Uweight R Y := by
  have hcollapse : A1 R X Y
      = ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
          gcdZ 0 u2 * tauZ (0 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4 := by
    rw [A1]
    refine (Finset.sum_eq_single (0 : ℤ) ?_ ?_).trans ?_
    · intro b _ hbne
      simp [hbne]
    · intro h0; exact absurd (zero_mem_boxZ R) h0
    · simp
  have hcollapse2 : (∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
        gcdZ 0 u2 * tauZ (0 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4)
      = ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
          (u2.natAbs : ℝ) * tauZ (u2 * h2 ^ 2) ^ 4 := by
    refine Finset.sum_congr rfl (fun u2 _ => Finset.sum_congr rfl (fun h1 _ =>
      Finset.sum_congr rfl (fun h2 _ => ?_)))
    rw [gcdZ_zero_left]
    congr 1
    rw [show (0 : ℤ) * h1 ^ 2 - u2 * h2 ^ 2 = -(u2 * h2 ^ 2) by ring, tauZ_neg]
  have hconst : (∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
        (u2.natAbs : ℝ) * tauZ (u2 * h2 ^ 2) ^ 4)
      = ((boxZ X).card : ℝ) * Uweight R Y := by
    rw [Uweight, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u2 _ => ?_)
    rw [sum_sum_const_fst]
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  calc A1 R X Y = ((boxZ X).card : ℝ) * Uweight R Y :=
        hcollapse.trans (hcollapse2.trans hconst)
    _ ≤ 3 * (X : ℝ) * Uweight R Y := by
        rw [card_boxZ]
        have h : 2 * (X : ℝ) + 1 ≤ 3 * (X : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_right h (Uweight_nonneg R Y)

/-- `A2 ≤ 3Y · Uweight R X`: the `u2 = 0`, `u1 ≠ 0` slice. -/
lemma A2_le (R X Y : ℕ) (hY : 1 ≤ Y) :
    A2 R X Y ≤ 3 * (Y : ℝ) * Uweight R X := by
  have hcollapse : A2 R X Y
      = ∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
          (if u1 ≠ 0 then gcdZ u1 0 else 0) * tauZ (u1 * h1 ^ 2 - 0 * h2 ^ 2) ^ 4 := by
    rw [A2]
    refine Finset.sum_congr rfl (fun u1 _ => ?_)
    refine (Finset.sum_eq_single (0 : ℤ) ?_ ?_).trans ?_
    · intro b _ hbne
      have hb0 : b ≠ 0 := hbne
      simp [hb0]
    · intro h0; exact absurd (zero_mem_boxZ R) h0
    · simp
  have hcollapse2 : (∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
        (if u1 ≠ 0 then gcdZ u1 0 else 0) * tauZ (u1 * h1 ^ 2 - 0 * h2 ^ 2) ^ 4)
      = ∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
          (if u1 ≠ 0 then (u1.natAbs : ℝ) else 0) * tauZ (u1 * h1 ^ 2) ^ 4 := by
    refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun h1 _ =>
      Finset.sum_congr rfl (fun h2 _ => ?_)))
    by_cases h : u1 ≠ 0
    · rw [if_pos h, if_pos h, gcdZ_zero_right]
      congr 1
      rw [show u1 * h1 ^ 2 - (0 : ℤ) * h2 ^ 2 = u1 * h1 ^ 2 by ring]
    · rw [if_neg h, if_neg h]; ring
  have hdrop : (∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
        (if u1 ≠ 0 then (u1.natAbs : ℝ) else 0) * tauZ (u1 * h1 ^ 2) ^ 4)
      ≤ ∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
          (u1.natAbs : ℝ) * tauZ (u1 * h1 ^ 2) ^ 4 := by
    refine Finset.sum_le_sum (fun u1 _ => Finset.sum_le_sum (fun h1 _ =>
      Finset.sum_le_sum (fun h2 _ => ?_)))
    by_cases h : u1 ≠ 0
    · rw [if_pos h]
    · rw [if_neg h]
      have hu0 : u1 = 0 := not_not.mp h
      rw [hu0]; simp
  have hconst : (∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
        (u1.natAbs : ℝ) * tauZ (u1 * h1 ^ 2) ^ 4)
      = ((boxZ Y).card : ℝ) * Uweight R X := by
    rw [Uweight, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u1 _ => ?_)
    rw [sum_sum_const_snd]
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  calc A2 R X Y ≤ (∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
        (u1.natAbs : ℝ) * tauZ (u1 * h1 ^ 2) ^ 4) :=
        (hcollapse.trans hcollapse2).le.trans hdrop
    _ = ((boxZ Y).card : ℝ) * Uweight R X := hconst
    _ ≤ 3 * (Y : ℝ) * Uweight R X := by
        rw [card_boxZ]
        have h : 2 * (Y : ℝ) + 1 ≤ 3 * (Y : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_right h (Uweight_nonneg R X)

/-- `A3 ≤ 3R · Bp 5 R · Bp 8 Y`: the `h1 = 0` slice with `u1, u2 ≠ 0`. -/
lemma A3_le (R X Y : ℕ) (hR : 1 ≤ R) :
    A3 R X Y ≤ 3 * (R : ℝ) * Bp 5 R * Bp 8 Y := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by linarith
  have hcollapse : A3 R X Y
      = ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
          (if u1 ≠ 0 ∧ u2 ≠ 0 then gcdZ u1 u2 * tauZ (u2 * h2 ^ 2) ^ 4 else 0) := by
    rw [A3]
    refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun u2 _ => ?_))
    have hx := sum_ite_and_zero_mul (boxZ X) (u1 ≠ 0 ∧ u2 ≠ 0) (zero_mem_boxZ X)
      (gcdZ u1 u2) (fun h1 => ∑ h2 ∈ boxZ Y, tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4)
    have hy : (∑ h2 ∈ boxZ Y,
          (if u1 ≠ 0 ∧ u2 ≠ 0 then gcdZ u1 u2 * tauZ (u2 * h2 ^ 2) ^ 4 else 0))
        = (if u1 ≠ 0 ∧ u2 ≠ 0 then
            gcdZ u1 u2 * (∑ h2 ∈ boxZ Y, tauZ (u2 * h2 ^ 2) ^ 4) else 0) := by
      rw [sum_ite_const]
      by_cases hA : u1 ≠ 0 ∧ u2 ≠ 0
      · rw [if_pos hA, if_pos hA, Finset.mul_sum]
      · rw [if_neg hA, if_neg hA]
    have he : (∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
          (if (u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 = 0 then gcdZ u1 u2 else 0)
            * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4)
        = ∑ h1 ∈ boxZ X, (if (u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 = 0 then gcdZ u1 u2 else 0)
            * ∑ h2 ∈ boxZ Y, tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4 := by
      refine Finset.sum_congr rfl (fun h1 _ => ?_)
      rw [Finset.mul_sum]
    rw [he, hx, hy]
    by_cases hA : u1 ≠ 0 ∧ u2 ≠ 0
    · rw [if_pos hA, if_pos hA]
      congr 1
      refine Finset.sum_congr rfl (fun h2 _ => ?_)
      rw [show u1 * 0 ^ 2 - u2 * h2 ^ 2 = -(u2 * h2 ^ 2) by ring, tauZ_neg]
    · rw [if_neg hA, if_neg hA]
  have hd : (∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
        (if u1 ≠ 0 ∧ u2 ≠ 0 then gcdZ u1 u2 * tauZ (u2 * h2 ^ 2) ^ 4 else 0))
      ≤ ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
          (if u2 ≠ 0 then gcdZ u1 u2 * tauZ (u2 * h2 ^ 2) ^ 4 else 0) := by
    refine Finset.sum_le_sum (fun u1 _ => Finset.sum_le_sum (fun u2 _ =>
      Finset.sum_le_sum (fun h2 _ => ?_)))
    exact ite_and_le_ite (u1 ≠ 0) (u2 ≠ 0)
      (mul_nonneg (gcdZ_nonneg _ _) (pow_nonneg (tauZ_nonneg _) _))
  have hswap : (∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
        (if u2 ≠ 0 then gcdZ u1 u2 * tauZ (u2 * h2 ^ 2) ^ 4 else 0))
      = ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y, ∑ u1 ∈ boxZ R,
          (if u2 ≠ 0 then gcdZ u1 u2 * tauZ (u2 * h2 ^ 2) ^ 4 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u2 _ => Finset.sum_comm)
  have hfac : (∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y, ∑ u1 ∈ boxZ R,
        (if u2 ≠ 0 then gcdZ u1 u2 * tauZ (u2 * h2 ^ 2) ^ 4 else 0))
      = ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
          (if u2 ≠ 0 then (∑ u1 ∈ boxZ R, gcdZ u1 u2) * tauZ (u2 * h2 ^ 2) ^ 4
            else 0) := by
    refine Finset.sum_congr rfl (fun u2 _ => Finset.sum_congr rfl (fun h2 _ => ?_))
    rw [sum_ite_const]
    by_cases h : u2 ≠ 0
    · rw [if_pos h, if_pos h, Finset.sum_mul]
    · rw [if_neg h, if_neg h]
  have hgcd : (∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
        (if u2 ≠ 0 then (∑ u1 ∈ boxZ R, gcdZ u1 u2) * tauZ (u2 * h2 ^ 2) ^ 4 else 0))
      ≤ ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
          (if u2 ≠ 0 then (3 * (R : ℝ) * tauZ u2) * tauZ (u2 * h2 ^ 2) ^ 4 else 0) := by
    refine Finset.sum_le_sum (fun u2 hu2 => Finset.sum_le_sum (fun h2 _ => ?_))
    by_cases h : u2 ≠ 0
    · rw [if_pos h, if_pos h]
      exact mul_le_mul_of_nonneg_right (gcd_slice R u2 hR hu2 h)
        (pow_nonneg (tauZ_nonneg _) _)
    · rw [if_neg h, if_neg h]
  have htau : (∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
        (if u2 ≠ 0 then (3 * (R : ℝ) * tauZ u2) * tauZ (u2 * h2 ^ 2) ^ 4 else 0))
      ≤ ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
          (if u2 ≠ 0 then (3 * (R : ℝ) * tauZ u2) * (tauZ u2 ^ 4 * tauZ h2 ^ 8)
            else 0) := by
    refine Finset.sum_le_sum (fun u2 _ => Finset.sum_le_sum (fun h2 _ => ?_))
    by_cases h : u2 ≠ 0
    · rw [if_pos h, if_pos h]
      exact mul_le_mul_of_nonneg_left (tauZ_mul_sq_pow4_le u2 h2)
        (mul_nonneg (mul_nonneg (by norm_num) hR0) (tauZ_nonneg u2))
    · rw [if_neg h, if_neg h]
  have hfin : (∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
        (if u2 ≠ 0 then (3 * (R : ℝ) * tauZ u2) * (tauZ u2 ^ 4 * tauZ h2 ^ 8) else 0))
      = 3 * (R : ℝ) * (∑ u2 ∈ boxZ R, (if u2 ≠ 0 then tauZ u2 ^ 5 else 0))
          * Bp 8 Y := by
    rw [Bp]
    have hpt : ∀ u2 h2 : ℤ,
        (if u2 ≠ 0 then (3 * (R : ℝ) * tauZ u2) * (tauZ u2 ^ 4 * tauZ h2 ^ 8) else 0)
          = (3 * (R : ℝ)) * ((if u2 ≠ 0 then tauZ u2 ^ 5 else 0) * tauZ h2 ^ 8) := by
      intro u2 h2
      by_cases h : u2 ≠ 0
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h, zero_mul, mul_zero]
    rw [Finset.sum_congr rfl (fun u2 _ => Finset.sum_congr rfl (fun h2 _ => hpt u2 h2)),
      sum_sum_mul_const]
    ring
  have hBp : (∑ u2 ∈ boxZ R, (if u2 ≠ 0 then tauZ u2 ^ 5 else 0)) ≤ Bp 5 R := by
    rw [Bp, ← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => pow_nonneg (tauZ_nonneg i) 5)
  calc A3 R X Y
      ≤ ∑ u2 ∈ boxZ R, ∑ h2 ∈ boxZ Y,
          (if u2 ≠ 0 then (3 * (R : ℝ) * tauZ u2) * (tauZ u2 ^ 4 * tauZ h2 ^ 8)
            else 0) :=
        (hcollapse.le.trans hd).trans ((le_of_eq hswap).trans ((le_of_eq hfac).trans
          (hgcd.trans htau)))
    _ = 3 * (R : ℝ) * (∑ u2 ∈ boxZ R, (if u2 ≠ 0 then tauZ u2 ^ 5 else 0)) * Bp 8 Y := hfin
    _ ≤ 3 * (R : ℝ) * Bp 5 R * Bp 8 Y := by
        refine mul_le_mul_of_nonneg_right ?_ (Bp_nonneg 8 Y)
        exact mul_le_mul_of_nonneg_left hBp (mul_nonneg (by norm_num) hR0)

/-- `A4 ≤ 3R · Bp 5 R · Bp 8 X`: the `h2 = 0` slice with `u1, u2, h1 ≠ 0`. -/
lemma A4_le (R X Y : ℕ) (hR : 1 ≤ R) :
    A4 R X Y ≤ 3 * (R : ℝ) * Bp 5 R * Bp 8 X := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by linarith
  have hcollapse : A4 R X Y
      = ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X,
          (if (u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 ≠ 0
            then gcdZ u1 u2 * tauZ (u1 * h1 ^ 2) ^ 4 else 0) := by
    rw [A4]
    refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun u2 _ =>
      Finset.sum_congr rfl (fun h1 _ => ?_)))
    have hx := sum_ite_and_zero_mul (boxZ Y) ((u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 ≠ 0) (zero_mem_boxZ Y)
      (gcdZ u1 u2) (fun h2 => tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4)
    rw [hx]
    rw [show u1 * h1 ^ 2 - u2 * (0 : ℤ) ^ 2 = u1 * h1 ^ 2 by ring]
  have hd : (∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X,
        (if (u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 ≠ 0 then gcdZ u1 u2 * tauZ (u1 * h1 ^ 2) ^ 4 else 0))
      ≤ ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X,
          (if u1 ≠ 0 then gcdZ u1 u2 * tauZ (u1 * h1 ^ 2) ^ 4 else 0) := by
    refine Finset.sum_le_sum (fun u1 _ => Finset.sum_le_sum (fun u2 _ =>
      Finset.sum_le_sum (fun h1 _ => ?_)))
    exact ite_le_ite_of (mul_nonneg (gcdZ_nonneg _ _) (pow_nonneg (tauZ_nonneg _) _))
      (fun h => h.1.1)
  have hswap : (∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X,
        (if u1 ≠ 0 then gcdZ u1 u2 * tauZ (u1 * h1 ^ 2) ^ 4 else 0))
      = ∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ u2 ∈ boxZ R,
          (if u1 ≠ 0 then gcdZ u1 u2 * tauZ (u1 * h1 ^ 2) ^ 4 else 0) := by
    refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_comm)
  have hfac : (∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ u2 ∈ boxZ R,
        (if u1 ≠ 0 then gcdZ u1 u2 * tauZ (u1 * h1 ^ 2) ^ 4 else 0))
      = ∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X,
          (if u1 ≠ 0 then (∑ u2 ∈ boxZ R, gcdZ u1 u2) * tauZ (u1 * h1 ^ 2) ^ 4
            else 0) := by
    refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun h1 _ => ?_))
    rw [sum_ite_const]
    by_cases h : u1 ≠ 0
    · rw [if_pos h, if_pos h, Finset.sum_mul]
    · rw [if_neg h, if_neg h]
  have hgcd : (∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X,
        (if u1 ≠ 0 then (∑ u2 ∈ boxZ R, gcdZ u1 u2) * tauZ (u1 * h1 ^ 2) ^ 4 else 0))
      ≤ ∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X,
          (if u1 ≠ 0 then (3 * (R : ℝ) * tauZ u1) * tauZ (u1 * h1 ^ 2) ^ 4 else 0) := by
    refine Finset.sum_le_sum (fun u1 hu1 => Finset.sum_le_sum (fun h1 _ => ?_))
    by_cases h : u1 ≠ 0
    · rw [if_pos h, if_pos h]
      have hslice : (∑ u2 ∈ boxZ R, gcdZ u1 u2) ≤ 3 * (R : ℝ) * tauZ u1 := by
        rw [show (∑ u2 ∈ boxZ R, gcdZ u1 u2) = ∑ u2 ∈ boxZ R, gcdZ u2 u1 by
          refine Finset.sum_congr rfl (fun u2 _ => gcdZ_comm u1 u2)]
        exact gcd_slice R u1 hR hu1 h
      exact mul_le_mul_of_nonneg_right hslice (pow_nonneg (tauZ_nonneg _) _)
    · rw [if_neg h, if_neg h]
  have htau : (∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X,
        (if u1 ≠ 0 then (3 * (R : ℝ) * tauZ u1) * tauZ (u1 * h1 ^ 2) ^ 4 else 0))
      ≤ ∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X,
          (if u1 ≠ 0 then (3 * (R : ℝ) * tauZ u1) * (tauZ u1 ^ 4 * tauZ h1 ^ 8)
            else 0) := by
    refine Finset.sum_le_sum (fun u1 _ => Finset.sum_le_sum (fun h1 _ => ?_))
    by_cases h : u1 ≠ 0
    · rw [if_pos h, if_pos h]
      exact mul_le_mul_of_nonneg_left (tauZ_mul_sq_pow4_le u1 h1)
        (mul_nonneg (mul_nonneg (by norm_num) hR0) (tauZ_nonneg u1))
    · rw [if_neg h, if_neg h]
  have hfin : (∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X,
        (if u1 ≠ 0 then (3 * (R : ℝ) * tauZ u1) * (tauZ u1 ^ 4 * tauZ h1 ^ 8) else 0))
      = 3 * (R : ℝ) * (∑ u1 ∈ boxZ R, (if u1 ≠ 0 then tauZ u1 ^ 5 else 0))
          * Bp 8 X := by
    rw [Bp]
    have hpt : ∀ u1 h1 : ℤ,
        (if u1 ≠ 0 then (3 * (R : ℝ) * tauZ u1) * (tauZ u1 ^ 4 * tauZ h1 ^ 8) else 0)
          = (3 * (R : ℝ)) * ((if u1 ≠ 0 then tauZ u1 ^ 5 else 0) * tauZ h1 ^ 8) := by
      intro u1 h1
      by_cases h : u1 ≠ 0
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h, zero_mul, mul_zero]
    rw [Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun h1 _ => hpt u1 h1)),
      sum_sum_mul_const]
    ring
  have hBp : (∑ u1 ∈ boxZ R, (if u1 ≠ 0 then tauZ u1 ^ 5 else 0)) ≤ Bp 5 R := by
    rw [Bp, ← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => pow_nonneg (tauZ_nonneg i) 5)
  calc A4 R X Y
      ≤ ∑ u1 ∈ boxZ R, ∑ h1 ∈ boxZ X,
          (if u1 ≠ 0 then (3 * (R : ℝ) * tauZ u1) * (tauZ u1 ^ 4 * tauZ h1 ^ 8)
            else 0) :=
        (hcollapse.le.trans hd).trans ((le_of_eq hswap).trans ((le_of_eq hfac).trans
          (hgcd.trans htau)))
    _ = 3 * (R : ℝ) * (∑ u1 ∈ boxZ R, (if u1 ≠ 0 then tauZ u1 ^ 5 else 0)) * Bp 8 X := hfin
    _ ≤ 3 * (R : ℝ) * Bp 5 R * Bp 8 X := by
        refine mul_le_mul_of_nonneg_right ?_ (Bp_nonneg 8 X)
        exact mul_le_mul_of_nonneg_left hBp (mul_nonneg (by norm_num) hR0)

end Hbox6Axis

open Hbox6Axis in
theorem hbox6_axis :
    ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℕ), 1 ≤ R → ∀ (X : ℕ), 1 ≤ X → ∀ (Y : ℕ), 1 ≤ Y →
        (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
          ∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
               then (Nat.gcd u1.natAbs u2.natAbs : ℝ) else 0)
              * (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4))
          ≤ C * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
              * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
  obtain ⟨Cu, hCupos, hCu⟩ := Uweight_bound
  obtain ⟨C5, hC5pos, hC5⟩ := Bp_bound 5 (by norm_num)
  obtain ⟨C8, hC8pos, hC8⟩ := Bp_bound 8 (by norm_num)
  have h1 : ∀ (R X Y : ℕ), 1 ≤ R → 1 ≤ X → 1 ≤ Y →
      A1 R X Y ≤ 3 * Cu * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
    intro R X Y hR hX hY
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
    have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
    have hRY : (0 : ℝ) ≤ (R : ℝ) + (Y : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (Y : ℝ) := by positivity
      linarith
    have hlog : (Real.log ((R : ℝ) + (Y : ℝ) + 2)) ^ 300
        ≤ (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
      refine pow_le_pow_left₀ (Real.log_nonneg (by linarith)) ?_ 300
      exact Real.log_le_log (by linarith) (by linarith)
    calc A1 R X Y ≤ 3 * (X : ℝ) * Uweight R Y := A1_le R X Y hX
      _ ≤ 3 * (X : ℝ) * (Cu * (R : ℝ) ^ 2 * (Y : ℝ)
            * (Real.log ((R : ℝ) + (Y : ℝ) + 2)) ^ 300) :=
          mul_le_mul_of_nonneg_left (hCu R Y hR hY) (by positivity)
      _ = 3 * Cu * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (Real.log ((R : ℝ) + (Y : ℝ) + 2)) ^ 300 := by ring
      _ ≤ 3 * Cu * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : ∀ (R X Y : ℕ), 1 ≤ R → 1 ≤ X → 1 ≤ Y →
      A2 R X Y ≤ 3 * Cu * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
    intro R X Y hR hX hY
    have hlog : (Real.log ((R : ℝ) + (X : ℝ) + 2)) ^ 300
        ≤ (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
      refine pow_le_pow_left₀ (Real.log_nonneg (by linarith)) ?_ 300
      exact Real.log_le_log (by linarith) (by linarith)
    calc A2 R X Y ≤ 3 * (Y : ℝ) * Uweight R X := A2_le R X Y hY
      _ ≤ 3 * (Y : ℝ) * (Cu * (R : ℝ) ^ 2 * (X : ℝ)
            * (Real.log ((R : ℝ) + (X : ℝ) + 2)) ^ 300) :=
          mul_le_mul_of_nonneg_left (hCu R X hR hX) (by positivity)
      _ = 3 * Cu * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (Real.log ((R : ℝ) + (X : ℝ) + 2)) ^ 300 := by ring
      _ ≤ 3 * Cu * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
  have h3 : ∀ (R X Y : ℕ), 1 ≤ R → 1 ≤ X → 1 ≤ Y →
      A3 R X Y ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
    intro R X Y hR hX hY
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := by linarith
    have hY0 : (0 : ℝ) ≤ (Y : ℝ) := by linarith
    set L : ℝ := Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) with hLdef
    have hL : (1 : ℝ) ≤ L := by
      rw [hLdef]
      exact one_le_log_arg R X Y hR hX hY
    have hL0 : (0 : ℝ) ≤ L := by linarith
    have hlogR0 : 0 ≤ Real.log ((R : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlogY0 : 0 ≤ Real.log ((Y : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlogR : Real.log ((R : ℝ) + 2) ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
    have hlogY : Real.log ((Y : ℝ) + 2) ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
    have hp : (Real.log ((R : ℝ) + 2)) ^ 32 * (Real.log ((Y : ℝ) + 2)) ^ 256 ≤ L ^ 300 := by
      have e1 := pow_le_pow_left₀ hlogR0 hlogR 32
      have e2 := pow_le_pow_left₀ hlogY0 hlogY 256
      have hs : Real.log ((R : ℝ) + 2) ^ 32 * Real.log ((Y : ℝ) + 2) ^ 256
          ≤ L ^ 32 * L ^ 256 := mul_le_mul e1 e2 (pow_nonneg hlogY0 256) (pow_nonneg hL0 32)
      have he : L ^ 32 * L ^ 256 = L ^ 288 := by rw [← pow_add]
      have hm : L ^ 288 ≤ L ^ 300 := pow_le_pow_right₀ hL (by norm_num)
      linarith [hs, he.le, he.ge, hm]
    have hb3 : (0 : ℝ) ≤ C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32 :=
      mul_nonneg (mul_nonneg hC5pos.le hR0) (pow_nonneg hlogR0 32)
    have hprod := mul_le_mul (hC5 R hR) (hC8 Y hY) (Bp_nonneg 8 Y) hb3
    have s1 : 3 * (R : ℝ) * Bp 5 R * Bp 8 Y
        ≤ 3 * (R : ℝ) * (C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
            * (C8 * (Y : ℝ) * (Real.log ((Y : ℝ) + 2)) ^ 256) := by
      calc 3 * (R : ℝ) * Bp 5 R * Bp 8 Y
          = (3 * (R : ℝ)) * (Bp 5 R * Bp 8 Y) := by ring
        _ ≤ (3 * (R : ℝ)) * ((C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
              * (C8 * (Y : ℝ) * (Real.log ((Y : ℝ) + 2)) ^ 256)) :=
            mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) hR0)
        _ = 3 * (R : ℝ) * (C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
              * (C8 * (Y : ℝ) * (Real.log ((Y : ℝ) + 2)) ^ 256) := by ring
    have s2 : 3 * (R : ℝ) * (C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
            * (C8 * (Y : ℝ) * (Real.log ((Y : ℝ) + 2)) ^ 256)
        = (3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ))
            * ((Real.log ((R : ℝ) + 2)) ^ 32 * (Real.log ((Y : ℝ) + 2)) ^ 256) := by ring
    have s3 : (0 : ℝ) ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ) := by positivity
    have s4 : (3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ))
            * ((Real.log ((R : ℝ) + 2)) ^ 32 * (Real.log ((Y : ℝ) + 2)) ^ 256)
        ≤ (3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ)) * L ^ 300 :=
      mul_le_mul_of_nonneg_left hp s3
    have s5 : 3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ) * L ^ 300
        ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ 300 := by
      have hfac : (0 : ℝ) ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ) * L ^ 300 := by positivity
      calc 3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ) * L ^ 300
          = (3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ) * L ^ 300) * 1 := by ring
        _ ≤ (3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ) * L ^ 300) * (X : ℝ) :=
            mul_le_mul_of_nonneg_left hX1 hfac
        _ = 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ 300 := by ring
    calc A3 R X Y ≤ 3 * (R : ℝ) * Bp 5 R * Bp 8 Y := A3_le R X Y hR
      _ ≤ 3 * (R : ℝ) * (C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
            * (C8 * (Y : ℝ) * (Real.log ((Y : ℝ) + 2)) ^ 256) := s1
      _ = (3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ))
            * ((Real.log ((R : ℝ) + 2)) ^ 32 * (Real.log ((Y : ℝ) + 2)) ^ 256) := s2
      _ ≤ (3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ)) * L ^ 300 := s4
      _ = 3 * C5 * C8 * (R : ℝ) ^ 2 * (Y : ℝ) * L ^ 300 := by ring
      _ ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ 300 := s5
      _ = 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by rw [← hLdef]
  have h4 : ∀ (R X Y : ℕ), 1 ≤ R → 1 ≤ X → 1 ≤ Y →
      A4 R X Y ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
    intro R X Y hR hX hY
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := by linarith
    have hX0 : (0 : ℝ) ≤ (X : ℝ) := by linarith
    set L : ℝ := Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) with hLdef
    have hL : (1 : ℝ) ≤ L := by
      rw [hLdef]
      exact one_le_log_arg R X Y hR hX hY
    have hL0 : (0 : ℝ) ≤ L := by linarith
    have hlogR0 : 0 ≤ Real.log ((R : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlogX0 : 0 ≤ Real.log ((X : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlogR : Real.log ((R : ℝ) + 2) ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
    have hlogX : Real.log ((X : ℝ) + 2) ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
    have hp : (Real.log ((R : ℝ) + 2)) ^ 32 * (Real.log ((X : ℝ) + 2)) ^ 256 ≤ L ^ 300 := by
      have e1 := pow_le_pow_left₀ hlogR0 hlogR 32
      have e2 := pow_le_pow_left₀ hlogX0 hlogX 256
      have hs : Real.log ((R : ℝ) + 2) ^ 32 * Real.log ((X : ℝ) + 2) ^ 256
          ≤ L ^ 32 * L ^ 256 := mul_le_mul e1 e2 (pow_nonneg hlogX0 256) (pow_nonneg hL0 32)
      have he : L ^ 32 * L ^ 256 = L ^ 288 := by rw [← pow_add]
      have hm : L ^ 288 ≤ L ^ 300 := pow_le_pow_right₀ hL (by norm_num)
      linarith [hs, he.le, he.ge, hm]
    have hb3 : (0 : ℝ) ≤ C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32 :=
      mul_nonneg (mul_nonneg hC5pos.le hR0) (pow_nonneg hlogR0 32)
    have hprod := mul_le_mul (hC5 R hR) (hC8 X hX) (Bp_nonneg 8 X) hb3
    have s1 : 3 * (R : ℝ) * Bp 5 R * Bp 8 X
        ≤ 3 * (R : ℝ) * (C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
            * (C8 * (X : ℝ) * (Real.log ((X : ℝ) + 2)) ^ 256) := by
      calc 3 * (R : ℝ) * Bp 5 R * Bp 8 X
          = (3 * (R : ℝ)) * (Bp 5 R * Bp 8 X) := by ring
        _ ≤ (3 * (R : ℝ)) * ((C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
              * (C8 * (X : ℝ) * (Real.log ((X : ℝ) + 2)) ^ 256)) :=
            mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) hR0)
        _ = 3 * (R : ℝ) * (C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
              * (C8 * (X : ℝ) * (Real.log ((X : ℝ) + 2)) ^ 256) := by ring
    have s2 : 3 * (R : ℝ) * (C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
            * (C8 * (X : ℝ) * (Real.log ((X : ℝ) + 2)) ^ 256)
        = (3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ))
            * ((Real.log ((R : ℝ) + 2)) ^ 32 * (Real.log ((X : ℝ) + 2)) ^ 256) := by ring
    have s3 : (0 : ℝ) ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) := by positivity
    have s4 : (3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ))
            * ((Real.log ((R : ℝ) + 2)) ^ 32 * (Real.log ((X : ℝ) + 2)) ^ 256)
        ≤ (3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ)) * L ^ 300 :=
      mul_le_mul_of_nonneg_left hp s3
    have s5 : 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * L ^ 300
        ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ 300 := by
      have hfac : (0 : ℝ) ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * L ^ 300 := by positivity
      calc 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * L ^ 300
          = (3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * L ^ 300) * 1 := by ring
        _ ≤ (3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * L ^ 300) * (Y : ℝ) :=
            mul_le_mul_of_nonneg_left hY1 hfac
        _ = 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ 300 := by ring
    calc A4 R X Y ≤ 3 * (R : ℝ) * Bp 5 R * Bp 8 X := A4_le R X Y hR
      _ ≤ 3 * (R : ℝ) * (C5 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ 32)
            * (C8 * (X : ℝ) * (Real.log ((X : ℝ) + 2)) ^ 256) := s1
      _ = (3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ))
            * ((Real.log ((R : ℝ) + 2)) ^ 32 * (Real.log ((X : ℝ) + 2)) ^ 256) := s2
      _ ≤ (3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ)) * L ^ 300 := s4
      _ = 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * L ^ 300 := by ring
      _ ≤ 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ 300 := s5
      _ = 3 * C5 * C8 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by rw [← hLdef]
  refine ⟨(3 * Cu + 3 * Cu) + (3 * C5 * C8 + 3 * C5 * C8), by positivity, ?_⟩
  intro R hR X hX Y hY
  have hs := axis_split R X Y
  have key1 := h1 R X Y hR hX hY
  have key2 := h2 R X Y hR hX hY
  have key3 := h3 R X Y hR hX hY
  have key4 := h4 R X Y hR hX hY
  have hfin : AxisSum R X Y ≤ ((3 * Cu + 3 * Cu) + (3 * C5 * C8 + 3 * C5 * C8))
      * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
      * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
    rw [hs]
    linarith [key1, key2, key3, key4]
  simpa only [AxisSum, boxZ, gcdZ, tauZ] using hfin

end

end Work.FIArea2.R6
