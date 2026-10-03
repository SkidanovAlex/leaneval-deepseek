import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# Separation of two distinct `q`-torsion points of `Circle = ℝ ⧸ ℤ`

Two distinct elements of the circle group `Circle = AddCircle (1 : ℝ) = ℝ ⧸ ℤ` which are
both killed by the same positive integer `q` (i.e. two distinct `q`-th roots of unity, in
additive notation) are separated by `1/q` in the quotient norm of `ℝ ⧸ ℤ`.

The proof is the standard torsion-point argument.  If `u = α - β`, then `u ≠ 0` is still
killed by `q`, so it has finite additive order `d ∣ q`; hence `d ≤ q`.  The Mathlib lemma
`AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder` gives `1 ≤ d • ‖u‖` for the unit
period, and therefore `1 ≤ d * ‖u‖ ≤ q * ‖u‖`, i.e. `1 / q ≤ ‖α - β‖`.

## Main result

* `Work.Analysis.IonescuWainger.one_div_le_norm_of_ne`
-/

set_option autoImplicit false

namespace Work.Analysis.IonescuWainger

/-- Two distinct elements of `Circle = ℝ ⧸ ℤ` killed by the same positive `q` are at norm
distance at least `1 / q` from each other. -/
theorem one_div_le_norm_of_ne {q : ℕ} (hq : 0 < q) {α β : Circle} (hα : q • α = 0)
    (hβ : q • β = 0) (hne : α ≠ β) : (1 : ℝ) / q ≤ ‖α - β‖ := by
  have hu : α - β ≠ 0 := sub_ne_zero.mpr hne
  have hsmul : q • (α - β) = 0 := by
    rw [smul_sub, hα, hβ, sub_self]
  have hfin : IsOfFinAddOrder (α - β) := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨q, hq, hsmul⟩
  have hle : (1 : ℝ) ≤ addOrderOf (α - β) • ‖α - β‖ :=
    AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder (p := (1 : ℝ)) hfin hu
  rw [nsmul_eq_mul] at hle
  have hdvd : addOrderOf (α - β) ∣ q := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsmul
  have hleQ : ((addOrderOf (α - β) : ℕ) : ℝ) ≤ (q : ℝ) :=
    Nat.cast_le.mpr (Nat.le_of_dvd hq hdvd)
  have hnn : (0 : ℝ) ≤ ‖α - β‖ := norm_nonneg _
  have hmul : (1 : ℝ) ≤ (q : ℝ) * ‖α - β‖ :=
    hle.trans (mul_le_mul_of_nonneg_right hleQ hnn)
  rw [div_le_iff₀ (by exact_mod_cast hq)]
  linarith [hmul]

end Work.Analysis.IonescuWainger
