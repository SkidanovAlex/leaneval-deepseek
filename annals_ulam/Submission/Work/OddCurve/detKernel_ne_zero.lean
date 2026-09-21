import Mathlib
import Submission.Work.OddCurve.Defs
import Submission.Work.OddVolterra.Defs

/-!
# Non-vanishing of the diagonal Abel kernel determinant

The paper's transition-slope argument needs the `2 × 2` block

`[K₁(s,s,-x s)  K₁(s,s,y s); K₂(s,s,-x s)  K₂(s,s,y s)]`

to be invertible (this is what lets the Abel system be solved for `x'`, `y'`).
On the diagonal `σ = s` the kernels collapse to the closed forms

* `K₁(s,s,t) = (2n+1)!! · (-L_t · ∂_sL_t)^{n+1} / √((∂_sL_t)(2L_t))`
* `K₂(s,s,t) = (2n-1)!! · (-L_t · ∂_sL_t)^{n} · ∂_sL_t / √((∂_sL_t)(2L_t))`

with `L_t = L(s,t) = s t + h s` and `∂_sL_t = t + h'(s)`.  The determinant is

`(2n+1)!! (2n-1)!! · (A_a A_b)^n · (∂_sL_a)(∂_sL_b)(L_b - L_a) / (√(…)√(…))`,

so it suffices that `L`, `∂_sL` have opposite signs at `t = -x s` and
`t = y s` (the line cuts the body in the correct direction) --- which is
exactly the hypothesis list of `detKernel_ne_zero`.
-/

namespace Work.OddCurve

open Work.OddVolterra

noncomputable section

/-- The diagonal value of the common denominator `Kden`. -/
private lemma kden_diag (h : ℝ → ℝ) (s t : ℝ) :
    Kden h s s t = Real.sqrt (lineSlope h s t * (2 * line h s t)) := by
  unfold Kden lineSlope line
  rw [hquot_self]
  congr 1
  ring

/-- The diagonal value of the first Abel kernel. -/
private lemma K1_diag (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    K1 n h s s t =
      (Nat.doubleFactorial (2 * n + 1) : ℝ) *
        (-(line h s t * lineSlope h s t)) ^ (n + 1) / Kden h s s t := by
  unfold K1 J1
  rw [if_pos rfl]

/-- The diagonal value of the second Abel kernel. -/
private lemma K2_diag (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    K2 n h s s t =
      (Nat.doubleFactorial (2 * n - 1) : ℝ) *
        (-(line h s t * lineSlope h s t)) ^ n * lineSlope h s t / Kden h s s t := by
  unfold K2 J2
  rw [if_pos rfl]

/-- The algebraic factorisation of the diagonal determinant. -/
private lemma diagDet_eq (n : ℕ) (c1 c2 La Lb Da Db ka kb : ℝ)
    (hka : ka ≠ 0) (hkb : kb ≠ 0) :
    c1 * (-(La * Da)) ^ (n + 1) / ka * (c2 * (-(Lb * Db)) ^ n * Db / kb) -
      c1 * (-(Lb * Db)) ^ (n + 1) / kb * (c2 * (-(La * Da)) ^ n * Da / ka) =
    c1 * c2 * ((-(La * Da)) ^ n * (-(Lb * Db)) ^ n) * (Da * Db * (Lb - La)) /
      (ka * kb) := by
  field_simp
  ring

/-- **The diagonal Abel determinant is nonzero.**  Written with the sign data
`L_a < 0 < L_b` and `∂_sL_a < 0 < ∂_sL_b` for the two chord endpoints. -/
private lemma diag_det_ne_zero (n : ℕ) {h : ℝ → ℝ} {s a b : ℝ}
    (hLa : line h s a < 0) (hDa : lineSlope h s a < 0)
    (hLb : 0 < line h s b) (hDb : 0 < lineSlope h s b) :
    K1 n h s s a * K2 n h s s b - K1 n h s s b * K2 n h s s a ≠ 0 := by
  have hka : Kden h s s a ≠ 0 := by
    rw [kden_diag]
    exact ne_of_gt (Real.sqrt_pos_of_pos (by nlinarith [hLa, hDa]))
  have hkb : Kden h s s b ≠ 0 := by
    rw [kden_diag]
    exact ne_of_gt (Real.sqrt_pos_of_pos (by nlinarith [hLb, hDb]))
  have hAa : (-(line h s a * lineSlope h s a)) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (mul_pos_of_neg_of_neg hLa hDa))
  have hAb : (-(line h s b * lineSlope h s b)) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (mul_pos hLb hDb))
  have hc1 : ((Nat.doubleFactorial (2 * n + 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.doubleFactorial_pos (2 * n + 1)))
  have hc2 : ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.doubleFactorial_pos (2 * n - 1)))
  have hsub : line h s b - line h s a ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (show line h s a < line h s b by linarith))
  have hDab : lineSlope h s a * lineSlope h s b * (line h s b - line h s a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_lt hDa) (ne_of_gt hDb)) hsub
  rw [K1_diag, K2_diag, K1_diag, K2_diag]
  have key := diagDet_eq n ((Nat.doubleFactorial (2 * n + 1) : ℕ) : ℝ)
    ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℝ) (line h s a) (line h s b)
    (lineSlope h s a) (lineSlope h s b) (Kden h s s a) (Kden h s s b) hka hkb
  rw [key]
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hc1 hc2)
    (mul_ne_zero (pow_ne_zero _ hAa) (pow_ne_zero _ hAb))) hDab) (mul_ne_zero hka hkb)

theorem detKernel_ne_zero (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) h)
    {s x y : ℝ} (hs : 0 < s) (hx : 0 < x) (hy : 0 < y)
    (hLx : s * (-x) + h s < 0) (hLy : 0 < s * y + h s)
    (hDx : -x + deriv h s < 0) (hDy : 0 < y + deriv h s) :
    Work.OddVolterra.K1 n h s s (-x) * Work.OddVolterra.K2 n h s s y -
      Work.OddVolterra.K1 n h s s y * Work.OddVolterra.K2 n h s s (-x) ≠ 0 := by
  have _ : 0 < s := hs
  have _ : 0 < x := hx
  have _ : 0 < y := hy
  have _ := hh
  have hLa : line h s (-x) < 0 := by simpa [line] using hLx
  have hDa : lineSlope h s (-x) < 0 := by simpa [lineSlope] using hDx
  have hLb : 0 < line h s y := by simpa [line] using hLy
  have hDb : 0 < lineSlope h s y := by simpa [lineSlope] using hDy
  exact diag_det_ne_zero n hLa hDa hLb hDb

end

end Work.OddCurve
