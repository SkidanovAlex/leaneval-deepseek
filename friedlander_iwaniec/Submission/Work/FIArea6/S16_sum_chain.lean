import Mathlib
import Submission.Work.FIArea6.S16UDefs

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

theorem S16_sum_chain (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (E B0 M : ℝ)
    (hX : 1 ≤ X)
    (hchar : ∀ d ∈ Finset.Icc 1 X,
      ∀ k ∈ Finset.Icc (-(2 * (Work.FIArea6.Kcut X) : ℤ)) (2 * (Work.FIArea6.Kcut X) : ℤ),
        |(k : ℝ)| ≤ E → ‖Work.FIArea6.DetSum Pa d k β‖ ≤ 4 * (d : ℝ) * B0 ^ (2 : ℕ))
    (htriv : ∀ d ∈ Finset.Icc 1 X,
      ∀ k ∈ Finset.Icc (-(2 * (Work.FIArea6.Kcut X) : ℤ)) (2 * (Work.FIArea6.Kcut X) : ℤ),
        ‖Work.FIArea6.DetSum Pa d k β‖ ≤ 4 * (d : ℝ) * M ^ (2 : ℕ)) :
    ‖Work.FIArea6.Umain Pa X β‖
      ≤ 8 * (∑ k ∈ Finset.Icc (-(2 * (Work.FIArea6.Kcut X) : ℤ)) (2 * (Work.FIArea6.Kcut X) : ℤ),
              |Work.FIArea6.fcoeff k|)
          * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ)) * B0 ^ (2 : ℕ)
        + 8 * (∑ k ∈ (Finset.Icc (-(2 * (Work.FIArea6.Kcut X) : ℤ))
                (2 * (Work.FIArea6.Kcut X) : ℤ)).filter (fun k : ℤ => ¬ |(k : ℝ)| ≤ E),
              |Work.FIArea6.fcoeff k|)
          * M ^ (2 : ℕ) * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ)) := by
  classical
  set J : Finset ℤ := Finset.Icc (-(2 * (Kcut X) : ℤ)) (2 * (Kcut X) : ℤ) with hJ
  set J2 : Finset ℤ := J.filter (fun k : ℤ => ¬ |(k : ℝ)| ≤ E) with hJ2
  have htri : ‖Umain Pa X β‖ ≤
      2 * ∑ d ∈ Finset.Icc 1 X,
        ((Nat.totient d : ℝ) / (d : ℝ)) * ‖MainSum Pa X d β‖ := by
    unfold Umain
    calc ‖2 * ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * MainSum Pa X d β‖
        = 2 * ‖∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * MainSum Pa X d β‖ := by
          rw [norm_mul]; norm_num
      _ ≤ 2 * ∑ d ∈ Finset.Icc 1 X,
            ‖((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * MainSum Pa X d β‖ := by
          gcongr
          exact norm_sum_le _ _
      _ = 2 * ∑ d ∈ Finset.Icc 1 X,
            ((Nat.totient d : ℝ) / (d : ℝ)) * ‖MainSum Pa X d β‖ := by
          congr 1
          apply Finset.sum_congr rfl
          intro d _
          have hc : ‖((Nat.totient d : ℝ) / (d : ℝ) : ℂ)‖ = (Nat.totient d : ℝ) / (d : ℝ) := by
            rw [norm_div]
            rw [show ‖((Nat.totient d : ℝ) : ℂ)‖ = |(Nat.totient d : ℝ)| from by simp,
                show ‖((d : ℝ) : ℂ)‖ = |(d : ℝ)| from by simp,
                abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
          rw [norm_mul, hc]
  have hmid : ∀ d ∈ Finset.Icc 1 X,
      ‖MainSum Pa X d β‖ ≤
        (∑ k ∈ J, |fcoeff k|) * (4 * (d : ℝ) * B0 ^ (2 : ℕ))
        + (∑ k ∈ J2, |fcoeff k|) * (4 * (d : ℝ) * M ^ (2 : ℕ)) := by
    intro d hd
    have hbase : ‖MainSum Pa X d β‖ ≤ ∑ k ∈ J, |fcoeff k| * ‖DetSum Pa d k β‖ := by
      unfold MainSum
      rw [← hJ]
      calc ‖∑ k ∈ J, (fcoeff k : ℂ) * DetSum Pa d k β‖
          ≤ ∑ k ∈ J, ‖(fcoeff k : ℂ) * DetSum Pa d k β‖ := norm_sum_le _ _
        _ = ∑ k ∈ J, |fcoeff k| * ‖DetSum Pa d k β‖ := by
            apply Finset.sum_congr rfl
            intro k _
            rw [norm_mul, show ‖((fcoeff k) : ℂ)‖ = |fcoeff k| from by simp]
    have hsplit : ∑ k ∈ J, |fcoeff k| * ‖DetSum Pa d k β‖
        = (∑ k ∈ J.filter (fun k : ℤ => |(k : ℝ)| ≤ E), |fcoeff k| * ‖DetSum Pa d k β‖)
          + (∑ k ∈ J2, |fcoeff k| * ‖DetSum Pa d k β‖) := by
      rw [← Finset.sum_filter_add_sum_filter_not J (fun k : ℤ => |(k : ℝ)| ≤ E)
        (fun k => |fcoeff k| * ‖DetSum Pa d k β‖), ← hJ2]
    have hb1 : (∑ k ∈ J.filter (fun k : ℤ => |(k : ℝ)| ≤ E),
          |fcoeff k| * ‖DetSum Pa d k β‖)
        ≤ (∑ k ∈ J, |fcoeff k|) * (4 * (d : ℝ) * B0 ^ (2 : ℕ)) := by
      calc _ ≤ ∑ k ∈ J.filter (fun k : ℤ => |(k : ℝ)| ≤ E),
              |fcoeff k| * (4 * (d : ℝ) * B0 ^ (2 : ℕ)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkJ : k ∈ J := (Finset.mem_filter.mp hk).1
            have hkE : |(k : ℝ)| ≤ E := (Finset.mem_filter.mp hk).2
            exact mul_le_mul_of_nonneg_left (hchar d hd k hkJ hkE) (abs_nonneg _)
        _ = (∑ k ∈ J.filter (fun k : ℤ => |(k : ℝ)| ≤ E), |fcoeff k|)
              * (4 * (d : ℝ) * B0 ^ (2 : ℕ)) := by
            rw [Finset.sum_mul]
        _ ≤ (∑ k ∈ J, |fcoeff k|) * (4 * (d : ℝ) * B0 ^ (2 : ℕ)) := by
            apply mul_le_mul_of_nonneg_right
            · apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro k hk; exact (Finset.mem_filter.mp hk).1
              · intro k _ _; exact abs_nonneg _
            · positivity
    have hb2 : (∑ k ∈ J2, |fcoeff k| * ‖DetSum Pa d k β‖)
        ≤ (∑ k ∈ J2, |fcoeff k|) * (4 * (d : ℝ) * M ^ (2 : ℕ)) := by
      calc _ ≤ ∑ k ∈ J2, |fcoeff k| * (4 * (d : ℝ) * M ^ (2 : ℕ)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkJ : k ∈ J := (Finset.mem_filter.mp (hJ2 ▸ hk)).1
            exact mul_le_mul_of_nonneg_left (htriv d hd k hkJ) (abs_nonneg _)
        _ = (∑ k ∈ J2, |fcoeff k|) * (4 * (d : ℝ) * M ^ (2 : ℕ)) := by
            rw [Finset.sum_mul]
    calc ‖MainSum Pa X d β‖ ≤ ∑ k ∈ J, |fcoeff k| * ‖DetSum Pa d k β‖ := hbase
      _ = (∑ k ∈ J.filter (fun k : ℤ => |(k : ℝ)| ≤ E), |fcoeff k| * ‖DetSum Pa d k β‖)
          + (∑ k ∈ J2, |fcoeff k| * ‖DetSum Pa d k β‖) := hsplit
      _ ≤ (∑ k ∈ J, |fcoeff k|) * (4 * (d : ℝ) * B0 ^ (2 : ℕ))
          + (∑ k ∈ J2, |fcoeff k|) * (4 * (d : ℝ) * M ^ (2 : ℕ)) := by
          linarith [hb1, hb2]
  have hstep : ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ‖MainSum Pa X d β‖
      ≤ (4 * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ))) *
          ((∑ k ∈ J, |fcoeff k|) * B0 ^ (2 : ℕ) + (∑ k ∈ J2, |fcoeff k|) * M ^ (2 : ℕ)) := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
              ((∑ k ∈ J, |fcoeff k|) * (4 * (d : ℝ) * B0 ^ (2 : ℕ))
               + (∑ k ∈ J2, |fcoeff k|) * (4 * (d : ℝ) * M ^ (2 : ℕ))) := by
          apply Finset.sum_le_sum
          intro d hd
          exact mul_le_mul_of_nonneg_left (hmid d hd)
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = ∑ d ∈ Finset.Icc 1 X, (4 * (Nat.totient d : ℝ)) *
              ((∑ k ∈ J, |fcoeff k|) * B0 ^ (2 : ℕ)
               + (∑ k ∈ J2, |fcoeff k|) * M ^ (2 : ℕ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd0 : (d : ℝ) ≠ 0 := by
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            positivity
          field_simp
      _ = (4 * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ))) *
              ((∑ k ∈ J, |fcoeff k|) * B0 ^ (2 : ℕ)
               + (∑ k ∈ J2, |fcoeff k|) * M ^ (2 : ℕ)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  calc ‖Umain Pa X β‖
      ≤ 2 * ∑ d ∈ Finset.Icc 1 X,
          ((Nat.totient d : ℝ) / (d : ℝ)) * ‖MainSum Pa X d β‖ := htri
    _ ≤ 2 * ((4 * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ))) *
          ((∑ k ∈ J, |fcoeff k|) * B0 ^ (2 : ℕ) + (∑ k ∈ J2, |fcoeff k|) * M ^ (2 : ℕ))) := by
          apply mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 8 * (∑ k ∈ J, |fcoeff k|) * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ)) * B0 ^ (2 : ℕ)
        + 8 * (∑ k ∈ J2, |fcoeff k|) * M ^ (2 : ℕ)
          * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ)) := by
          ring

end Work.FIArea6
