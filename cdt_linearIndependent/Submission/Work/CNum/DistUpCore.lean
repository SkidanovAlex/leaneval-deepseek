import Mathlib
import Submission.Work.CNum.SmallBox
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.AbsMaxSpec

/-!
# `Work.CNum.DistUpCore` — soundness of `distUp`

`distUp a b` is the mantissa of an upper bound of `‖z - w‖` for `z ∈ a`, `w ∈ b`, valid when the
two boxes are `Small` (so that the mantissa sum of squares of the coordinate widths stays inside
the `70`-step range of the integer square root `sqUp`).

The proof is the complex-interval analogue of `Work.ANum.distUp_spec`: the two coordinates
`A = z.re - w.re`, `B = z.im - w.im` are bounded by `m2r dx`, `m2r dy` (`absMax_mem` applied to
the difference intervals, `Iv.mem_sub`), so after scaling by `SC`,
`(SC·‖z - w‖)² = (SC·A)² + (SC·B)² ≤ dx² + dy² = (dx*dx + dy*dy).toNat`, and
`√(dx*dx+dy*dy).toNat ≤ isqrt (dx*dx+dy*dy).toNat + 1` (`sqrt_toNat_le_sqUp`, using `Small`).
-/

namespace Work.CNum

open Work.ANum

theorem DistUpCore : ∀ (a b : Work.CNum.Cpx) (z w : ℂ), Work.CNum.Small a → Work.CNum.Small b → a.Mem z → b.Mem w → ‖z - w‖ ≤ Work.ANum.m2r (Work.CNum.distUp a b) := by
  intro a b z w ha hb hz hw
  set A : ℝ := z.re - w.re with hA
  set B : ℝ := z.im - w.im with hB
  set dx : ℤ := Work.CNum.absMax (Work.ANum.Iv.sub a.re b.re) with hdx
  set dy : ℤ := Work.CNum.absMax (Work.ANum.Iv.sub a.im b.im) with hdy
  have hx : |A| ≤ Work.ANum.m2r dx := by
    have h := Work.CNum.absMax_mem (Work.ANum.Iv.sub a.re b.re) (z.re - w.re)
      (Work.ANum.Iv.mem_sub hz.1 hw.1)
    simpa [hA, hdx] using h
  have hy : |B| ≤ Work.ANum.m2r dy := by
    have h := Work.CNum.absMax_mem (Work.ANum.Iv.sub a.im b.im) (z.im - w.im)
      (Work.ANum.Iv.mem_sub hz.2 hw.2)
    simpa [hB, hdy] using h
  have hlt : (dx * dx + dy * dy).toNat < 2 ^ 70 := by
    have h := Work.CNum.absMax_sub_small a b ha hb
    simpa [hdx, hdy] using h
  have hmul : ∀ (n : ℤ), (SC : ℝ) * m2r n = (n : ℝ) := by
    intro n
    simp only [m2r]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ (ne_of_gt SC_posR)
  have hX : (SC : ℝ) * |A| ≤ (dx : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hx SC_posR.le
    rwa [hmul] at h
  have hY : (SC : ℝ) * |B| ≤ (dy : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hy SC_posR.le
    rwa [hmul] at h
  have hS1 : ((SC : ℝ) * A) ^ 2 ≤ (dx : ℝ) ^ 2 := by
    have h : ((SC : ℝ) * |A|) ^ 2 ≤ (dx : ℝ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg SC_posR.le (abs_nonneg A)) hX 2
    rw [mul_pow, sq_abs] at h
    simpa [mul_pow] using h
  have hS2 : ((SC : ℝ) * B) ^ 2 ≤ (dy : ℝ) ^ 2 := by
    have h : ((SC : ℝ) * |B|) ^ 2 ≤ (dy : ℝ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg SC_posR.le (abs_nonneg B)) hY 2
    rw [mul_pow, sq_abs] at h
    simpa [mul_pow] using h
  have hsq : ((SC : ℝ) * Real.sqrt (A ^ 2 + B ^ 2)) ^ 2
      ≤ ((dx * dx + dy * dy).toNat : ℝ) := by
    have h1 : ((SC : ℝ) * Real.sqrt (A ^ 2 + B ^ 2)) ^ 2
        = ((SC : ℝ) * A) ^ 2 + ((SC : ℝ) * B) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [h1, Work.CNum.cast_sq_add]
    nlinarith
  have hle : (SC : ℝ) * Real.sqrt (A ^ 2 + B ^ 2)
      ≤ Real.sqrt (((dx * dx + dy * dy).toNat : ℕ) : ℝ) := by
    rw [Real.le_sqrt (mul_nonneg SC_posR.le (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)]
    simpa using hsq
  have hfinal : Real.sqrt (A ^ 2 + B ^ 2)
      ≤ Work.ANum.m2r (Work.CNum.sqUp (dx * dx + dy * dy)) := by
    rw [Work.ANum.m2r, le_div_iff₀ SC_posR]
    have h2 := Work.CNum.sqrt_toNat_le_sqUp hlt
    have h3 : ((Work.CNum.sqUp (dx * dx + dy * dy) : ℤ) : ℝ)
        = ((Work.CNum.isqrt (dx * dx + dy * dy).toNat : ℕ) : ℝ) + 1 := by
      simp [Work.CNum.sqUp]
    rw [h3]
    have h4 : (SC : ℝ) * Real.sqrt (A ^ 2 + B ^ 2)
        ≤ ((Work.CNum.isqrt (dx * dx + dy * dy).toNat : ℕ) : ℝ) + 1 := le_trans hle h2
    linarith
  have hnorm : ‖z - w‖ = Real.sqrt (A ^ 2 + B ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [← hA, ← hB]
  rw [hnorm]
  have hdist : Work.CNum.distUp a b = Work.CNum.sqUp (dx * dx + dy * dy) := by
    simp only [Work.CNum.distUp]
    rw [← hdx, ← hdy]
  rw [hdist]
  exact hfinal

end Work.CNum
