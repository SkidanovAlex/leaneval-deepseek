import Mathlib

set_option autoImplicit false

namespace Work.FIArea1

open scoped BigOperators
open Finset

/-- **One-dimensional reflection bound.**

For `R : ℤ` with `0 ≤ R` and a nonnegative function `u : ℕ → ℝ`, the sum of
`u x.natAbs` over the integer box `x ∈ [-R, R]` is at most twice the sum of `u`
over `n ∈ [0, R.natAbs]`.

Indeed `natAbs` is injective both on `[-R, R] ∩ [0, ∞)` and on
`[-R, R] ∩ (-∞, 0)`, and each of the two images lies in `[0, R.natAbs]`. -/
lemma sum_natAbs_le (R : ℤ) (hR : 0 ≤ R) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    ∑ x ∈ Finset.Icc (-R) R, u x.natAbs ≤ 2 * ∑ n ∈ Finset.Icc 0 R.natAbs, u n := by
  have hmem_pos :
      ∀ x ∈ (Finset.Icc (-R) R).filter (fun x => 0 ≤ x), x.natAbs ∈ Finset.Icc 0 R.natAbs := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, hx2⟩, hx0⟩ := hx
    rw [Finset.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    have hcast : (x.natAbs : ℤ) ≤ (R.natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg hx0, Int.natAbs_of_nonneg hR]
      exact hx2
    exact_mod_cast hcast
  have hmem_neg :
      ∀ x ∈ (Finset.Icc (-R) R).filter (fun x => ¬ 0 ≤ x), x.natAbs ∈ Finset.Icc 0 R.natAbs := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, hx2⟩, hx0⟩ := hx
    have hx0' : x ≤ 0 := le_of_lt (not_le.mp hx0)
    rw [Finset.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    have hcast : (x.natAbs : ℤ) ≤ (R.natAbs : ℤ) := by
      rw [← Int.natAbs_neg, Int.natAbs_of_nonneg (neg_nonneg.mpr hx0'), Int.natAbs_of_nonneg hR]
      omega
    exact_mod_cast hcast
  have himg_pos :
      Finset.image Int.natAbs ((Finset.Icc (-R) R).filter (fun x => 0 ≤ x)) ⊆
        Finset.Icc 0 R.natAbs :=
    Finset.image_subset_iff.mpr hmem_pos
  have himg_neg :
      Finset.image Int.natAbs ((Finset.Icc (-R) R).filter (fun x => ¬ 0 ≤ x)) ⊆
        Finset.Icc 0 R.natAbs :=
    Finset.image_subset_iff.mpr hmem_neg
  have hpos :
      ∑ x ∈ (Finset.Icc (-R) R).filter (fun x => 0 ≤ x), u x.natAbs
        ≤ ∑ n ∈ Finset.Icc 0 R.natAbs, u n := by
    rw [← Finset.sum_image (f := u) (g := Int.natAbs)]
    · exact Finset.sum_le_sum_of_subset_of_nonneg himg_pos (fun i _ _ => hu i)
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact (Int.natAbs_inj_of_nonneg_of_nonneg ha.2 hb.2).mp hab
  have hneg :
      ∑ x ∈ (Finset.Icc (-R) R).filter (fun x => ¬ 0 ≤ x), u x.natAbs
        ≤ ∑ n ∈ Finset.Icc 0 R.natAbs, u n := by
    rw [← Finset.sum_image (f := u) (g := Int.natAbs)]
    · exact Finset.sum_le_sum_of_subset_of_nonneg himg_neg (fun i _ _ => hu i)
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact (Int.natAbs_inj_of_nonpos_of_nonpos (le_of_lt (not_le.mp ha.2))
        (le_of_lt (not_le.mp hb.2))).mp hab
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (Finset.Icc (-R) R) (fun x => 0 ≤ x) (fun x => u x.natAbs)
  rw [← hsplit]
  linarith

/-- **The pair reflection bound.**

The sum of `F a.natAbs b.natAbs` over the integer square `[-R, R]²` is at most
`4` times the sum of `F m n` over `[0, R.natAbs]²`, because the map
`(a, b) ↦ (a.natAbs, b.natAbs)` is at most `2`-to-`1` in each coordinate. -/
theorem pair_natAbs_le (R : ℤ) (hR : 0 ≤ R) (F : ℕ → ℕ → ℝ) (hF : ∀ m n, 0 ≤ F m n) :
    (∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, F a.natAbs b.natAbs)
      ≤ 4 * ∑ m ∈ Finset.Icc 0 R.natAbs, ∑ n ∈ Finset.Icc 0 R.natAbs, F m n := by
  have step1 : (∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, F a.natAbs b.natAbs)
      ≤ 2 * ∑ a ∈ Finset.Icc (-R) R, ∑ n ∈ Finset.Icc 0 R.natAbs, F a.natAbs n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ =>
      sum_natAbs_le R hR (fun n => F a.natAbs n) (fun n => hF _ _))
  have hswap : (∑ a ∈ Finset.Icc (-R) R, ∑ n ∈ Finset.Icc 0 R.natAbs, F a.natAbs n)
      = ∑ n ∈ Finset.Icc 0 R.natAbs, ∑ a ∈ Finset.Icc (-R) R, F a.natAbs n :=
    Finset.sum_comm
  have step2 : (∑ a ∈ Finset.Icc (-R) R, ∑ n ∈ Finset.Icc 0 R.natAbs, F a.natAbs n)
      ≤ 2 * ∑ n ∈ Finset.Icc 0 R.natAbs, ∑ m ∈ Finset.Icc 0 R.natAbs, F m n := by
    rw [hswap, Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ =>
      sum_natAbs_le R hR (fun m => F m n) (fun m => hF _ _))
  calc (∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, F a.natAbs b.natAbs)
      ≤ 2 * ∑ a ∈ Finset.Icc (-R) R, ∑ n ∈ Finset.Icc 0 R.natAbs, F a.natAbs n := step1
    _ ≤ 2 * (2 * ∑ n ∈ Finset.Icc 0 R.natAbs, ∑ m ∈ Finset.Icc 0 R.natAbs, F m n) :=
        mul_le_mul_of_nonneg_left step2 (by norm_num)
    _ = 4 * ∑ n ∈ Finset.Icc 0 R.natAbs, ∑ m ∈ Finset.Icc 0 R.natAbs, F m n := by ring
    _ = 4 * ∑ m ∈ Finset.Icc 0 R.natAbs, ∑ n ∈ Finset.Icc 0 R.natAbs, F m n := by
        rw [Finset.sum_comm]

end Work.FIArea1
