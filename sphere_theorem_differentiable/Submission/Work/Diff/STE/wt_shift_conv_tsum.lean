import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.wt_pow_le
import Submission.Work.Diff.STE.summable_conv_nonneg_tsum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weighted Young inequality for the slowly varying weight `wt`

For coefficient families `a, f : (ι → ℤ) → ℂ` on the lattice `ℤ^ι` with `∑_l wt(l)^s ‖a l‖ < ∞`
and `∑_m wt(m)^s ‖f m‖² < ∞`, the convolution-type family

  `k ↦ wt(k)^s * ∑_m ‖a (k - m)‖ ‖f m‖²`

is summable, and its total mass is bounded by `2^s (∑ wt^s ‖a‖) (∑ wt^s ‖f‖²)`.

The point is the submultiplicativity of the weight, `wt k ≤ 2 · wt (k - m) · wt m`
(`Work.Diff.STE.wt_pow_le`), which unwinds the shift `k ↦ k - m` at the cost of the factor
`2^s`.  The double sum is then identified with the product of the two masses by discrete
Tonelli (`Work.Diff.STE.summable_conv_nonneg_tsum`).
-/

namespace Work.Diff.STE

open scoped BigOperators

theorem wt_shift_conv_tsum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a f : (ι → ℤ) → ℂ) (s : ℕ)
    (ha : Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ s * ‖a l‖))
    (hf : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖f m‖ ^ 2)) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ∑' m, ‖a (k - m)‖ * ‖f m‖ ^ 2) ∧
    (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ∑' m, ‖a (k - m)‖ * ‖f m‖ ^ 2)
      ≤ 2 ^ s * (∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ s * ‖a l‖)
        * (∑' m : ι → ℤ, (Work.Diff.STE.wt m) ^ s * ‖f m‖ ^ 2) := by
  classical
  have hA0 : ∀ l : ι → ℤ, 0 ≤ (wt l) ^ s * ‖a l‖ :=
    fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) s) (norm_nonneg _)
  have hB0 : ∀ m : ι → ℤ, 0 ≤ (wt m) ^ s * ‖f m‖ ^ 2 :=
    fun m => mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) s) (sq_nonneg _)
  obtain ⟨hslice, hiter, htot⟩ :=
    summable_conv_nonneg_tsum (fun l : ι → ℤ => (wt l) ^ s * ‖a l‖)
      (fun m : ι → ℤ => (wt m) ^ s * ‖f m‖ ^ 2) hA0 hB0 ha hf
  -- Slowly varying / submultiplicativity of the weight, against the convolution.
  have hpt : ∀ k m : ι → ℤ,
      (wt k) ^ s * (‖a (k - m)‖ * ‖f m‖ ^ 2)
        ≤ 2 ^ s * (((wt (k - m)) ^ s * ‖a (k - m)‖) * ((wt m) ^ s * ‖f m‖ ^ 2)) := by
    intro k m
    have hx : 0 ≤ ‖a (k - m)‖ * ‖f m‖ ^ 2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
    calc (wt k) ^ s * (‖a (k - m)‖ * ‖f m‖ ^ 2)
        ≤ (2 ^ s * ((wt m) ^ s * (wt (k - m)) ^ s)) * (‖a (k - m)‖ * ‖f m‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (wt_pow_le s k m) hx
      _ = 2 ^ s * (((wt (k - m)) ^ s * ‖a (k - m)‖) * ((wt m) ^ s * ‖f m‖ ^ 2)) := by ring
  -- Bound of the inner sum, slice by slice.
  have hleb : ∀ k : ι → ℤ,
      (wt k) ^ s * ∑' m : ι → ℤ, ‖a (k - m)‖ * ‖f m‖ ^ 2
        ≤ 2 ^ s * ∑' m : ι → ℤ,
            ((wt (k - m)) ^ s * ‖a (k - m)‖) * ((wt m) ^ s * ‖f m‖ ^ 2) := by
    intro k
    have hR2 : Summable fun m : ι → ℤ =>
        2 ^ s * (((wt (k - m)) ^ s * ‖a (k - m)‖) * ((wt m) ^ s * ‖f m‖ ^ 2)) :=
      (hslice k).mul_left _
    have hLsum : Summable fun m : ι → ℤ => (wt k) ^ s * (‖a (k - m)‖ * ‖f m‖ ^ 2) :=
      Summable.of_nonneg_of_le
        (fun m => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s)
          (mul_nonneg (norm_nonneg _) (sq_nonneg _)))
        (fun m => hpt k m) hR2
    calc (wt k) ^ s * ∑' m : ι → ℤ, ‖a (k - m)‖ * ‖f m‖ ^ 2
        = ∑' m : ι → ℤ, (wt k) ^ s * (‖a (k - m)‖ * ‖f m‖ ^ 2) := by rw [tsum_mul_left]
      _ ≤ ∑' m : ι → ℤ,
            2 ^ s * (((wt (k - m)) ^ s * ‖a (k - m)‖) * ((wt m) ^ s * ‖f m‖ ^ 2)) :=
          Summable.tsum_le_tsum (fun m => hpt k m) hLsum hR2
      _ = 2 ^ s * ∑' m : ι → ℤ,
            ((wt (k - m)) ^ s * ‖a (k - m)‖) * ((wt m) ^ s * ‖f m‖ ^ 2) := tsum_mul_left
  have hfinal : Summable fun k : ι → ℤ =>
      (wt k) ^ s * ∑' m : ι → ℤ, ‖a (k - m)‖ * ‖f m‖ ^ 2 :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s)
        (tsum_nonneg fun m => mul_nonneg (norm_nonneg _) (sq_nonneg _)))
      (fun k => hleb k) (hiter.mul_left (2 ^ s))
  refine ⟨hfinal, ?_⟩
  calc (∑' k : ι → ℤ, (wt k) ^ s * ∑' m : ι → ℤ, ‖a (k - m)‖ * ‖f m‖ ^ 2)
      ≤ ∑' k : ι → ℤ, 2 ^ s * ∑' m : ι → ℤ,
          ((wt (k - m)) ^ s * ‖a (k - m)‖) * ((wt m) ^ s * ‖f m‖ ^ 2) :=
        Summable.tsum_le_tsum (fun k => hleb k) hfinal (hiter.mul_left _)
    _ = 2 ^ s * (∑' k : ι → ℤ, ∑' m : ι → ℤ,
          ((wt (k - m)) ^ s * ‖a (k - m)‖) * ((wt m) ^ s * ‖f m‖ ^ 2)) := tsum_mul_left
    _ = 2 ^ s * ((∑' l : ι → ℤ, (wt l) ^ s * ‖a l‖)
          * (∑' m : ι → ℤ, (wt m) ^ s * ‖f m‖ ^ 2)) := by rw [htot]
    _ = 2 ^ s * (∑' l : ι → ℤ, (wt l) ^ s * ‖a l‖)
          * (∑' m : ι → ℤ, (wt m) ^ s * ‖f m‖ ^ 2) := by ring

end Work.Diff.STE
