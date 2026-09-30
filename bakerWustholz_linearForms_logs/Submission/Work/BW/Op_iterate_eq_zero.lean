import Mathlib
import Submission.Work.BW.expPoly_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- If `w ≠ 1`, the finite-difference operator `Op w` is injective on complex
polynomials: it has no nonzero kernel. Indeed `Op w Q = 0` means
`C w * taylor 1 Q = Q`, and comparing leading coefficients (the translation
`taylor 1` preserves the leading coefficient) gives `w * lc(Q) = lc(Q)`, whence
`lc(Q) = 0`, i.e. `Q = 0`, as soon as `w ≠ 1`. -/
lemma Op_eq_zero_of_ne_one {w : ℂ} (hw : w ≠ 1) {Q : Polynomial ℂ}
    (h : Op w Q = 0) : Q = 0 := by
  rw [Op] at h
  have hQ : C w * taylor (1 : ℂ) Q = Q := sub_eq_zero.mp h
  by_contra hne
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have hc : w * Q.leadingCoeff = Q.leadingCoeff := by
    have h1 := congrArg Polynomial.leadingCoeff hQ
    rwa [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_taylor] at h1
  exact hw (mul_right_cancel₀ hlc (by rw [one_mul]; exact hc))

/-- `Op w` is additive in the polynomial argument. -/
lemma Op_sub_apply (w : ℂ) (P R : Polynomial ℂ) :
    Op w (P - R) = Op w P - Op w R := by
  simp only [Op, taylor_apply, sub_comp]
  ring

/-- For `w ≠ 1` the finite-difference operator `Op w` is injective. -/
lemma Op_injective_of_ne_one {w : ℂ} (hw : w ≠ 1) : Function.Injective (Op w) := by
  intro P R hPR
  have hz : Op w (P - R) = 0 := by
    rw [Op_sub_apply, hPR, sub_self]
  exact sub_eq_zero.mp (Op_eq_zero_of_ne_one hw hz)

theorem Op_iterate_eq_zero {w : ℂ} (hw : w ≠ 1) (Q : Polynomial ℂ) (k : ℕ)
    (h : ((Work.BW.Op w)^[k]) Q = 0) : Q = 0 := by
  have hk0 : ((Work.BW.Op w)^[k]) 0 = 0 :=
    Function.iterate_fixed (Work.BW.Op_zero w) k
  have hinj := Function.Injective.iterate (Op_injective_of_ne_one hw) k
  exact hinj (h.trans hk0.symm)

end Work.BW
