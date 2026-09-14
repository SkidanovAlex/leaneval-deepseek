import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.Height.NumberField.infinitePlace_val_le_mulHeight
import Submission.Commons.NumberTheory.Height.NumberField.finitePlace_val_le_mulHeight

namespace Commons.NumberTheory.Height.NumberField

open _root_.NumberField

theorem one_le_mulHeight_sq_mul_abv {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (x : K) (hx : x ≠ 0) :
    1 ≤ (Height.mulHeight₁ x) ^ 2 * w.val x ^ w.mult := by
  classical
  have hy : w.val x ≠ 0 := w.val.ne_zero_iff.mpr hx
  have hnonneg : 0 ≤ w.val x := w.val.nonneg x
  -- the commutativity of the height gives `H ≥ (w.val x)^{-1}`
  have hHinv : (w.val x)⁻¹ ≤ Height.mulHeight₁ x := by
    have h := infinitePlace_val_le_mulHeight w x⁻¹
    rw [Height.mulHeight₁_inv] at h
    simpa using h
  have hH1 : 1 ≤ Height.mulHeight₁ x := Height.one_le_mulHeight₁ x
  have hn2 : w.mult ≤ 2 := by
    rw [InfinitePlace.mult]; split_ifs <;> norm_num
  -- `(w.val x)^{-mult} ≤ H^{mult} ≤ H^2`
  have h1 : (w.val x)⁻¹ ^ w.mult ≤ (Height.mulHeight₁ x) ^ 2 :=
    (pow_le_pow_left₀ (inv_nonneg.mpr hnonneg) hHinv w.mult).trans
      (pow_le_pow_right₀ hH1 hn2)
  have step : (w.val x) ^ w.mult * (w.val x)⁻¹ ^ w.mult
      ≤ (w.val x) ^ w.mult * (Height.mulHeight₁ x) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (pow_nonneg hnonneg _)
  rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hy)] at step
  calc (1 : ℝ) ≤ (w.val x) ^ w.mult * (Height.mulHeight₁ x) ^ 2 := step
    _ = (Height.mulHeight₁ x) ^ 2 * w.val x ^ w.mult := mul_comm _ _

end Commons.NumberTheory.Height.NumberField