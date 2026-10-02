import Mathlib
import Submission.Work.Implosion.Ecalle
import Submission.Work.PARIMPL2.Direct.ecalPt_norm_sq_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-!
# The bound `‖ecalPt (iλ) u‖² ≤ λ² / sin²(λ Re u)` on the half strip `0 < Re u < π/λ`

For `a = iλ` (`λ > 0`) the Écalle point map is `ζ(u) = a·coth(a u)`, and the
closed form `ecalPt_norm_sq_eq` gives, with `t = λ·Re u`, `s = λ·Im u`,

  `‖ζ(u)‖² = λ² · (cos²t + sinh²s) / (sin²t + sinh²s)`.

Since `cos² t ≤ 1` and `sinh² s ≥ 0`, the family of ratios is monotone in the
second argument and maximal at `s = 0`:

  `(cos²t + S)/(sin²t + S) ≤ 1/sin²t`   for every `S ≥ 0` and `sin t > 0`;

equivalently `((sin²t + S) − (cos²t + S) sin²t) = sin⁴t + S cos²t ≥ 0`.
The half strip `0 < Re u < π/λ` is exactly the range on which `sin(λ Re u) > 0`.
At the punctures `ecalE (iλ) u = 1` both sides of the closed form degenerate but
`ecalPt (iλ) u = 0`, so the bound still holds; no hypothesis on `Im u` is used.
-/

/-- For `sin t > 0` and `S ≥ 0` one has `(cos²t + S)/(sin²t + S) ≤ 1/sin²t`. -/
private lemma div_cos_sq_add_le_inv_sin_sq (t S : ℝ) (hS : 0 ≤ S)
    (hsin : 0 < Real.sin t) :
    (Real.cos t ^ 2 + S) / (Real.sin t ^ 2 + S) ≤ 1 / Real.sin t ^ 2 := by
  have hden : 0 < Real.sin t ^ 2 + S := by nlinarith [pow_pos hsin 2]
  have hmain : (Real.cos t ^ 2 + S) * Real.sin t ^ 2 ≤ Real.sin t ^ 2 + S := by
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.sin t), sq_nonneg (Real.cos t),
      sq_nonneg (S * Real.cos t), sq_nonneg (Real.sin t ^ 2)]
  rw [div_le_iff₀ hden]
  have hrw : (1 / Real.sin t ^ 2) * (Real.sin t ^ 2 + S)
      = (Real.sin t ^ 2 + S) / Real.sin t ^ 2 := by ring
  rw [hrw, le_div_iff₀ (pow_pos hsin 2)]
  exact hmain

theorem norm_ecalPt_sq_le (lam : ℝ) (u : ℂ) (hlam : 0 < lam)
    (h1 : 0 < u.re) (h2 : u.re < Real.pi / lam) :
    ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2
      ≤ lam ^ 2 / (Real.sin (lam * u.re)) ^ 2 := by
  have hlt_pi : lam * u.re < Real.pi := by
    have h : lam * (Real.pi / lam) = Real.pi := by field_simp
    calc lam * u.re < lam * (Real.pi / lam) := mul_lt_mul_of_pos_left h2 hlam
      _ = Real.pi := h
  have hsin_pos : 0 < Real.sin (lam * u.re) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos hlam h1) hlt_pi
  by_cases hE : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u = 1
  · -- puncture: the point map vanishes
    have hpt : Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u = 0 := by
      rw [Work.Implosion.ecalPt_apply, hE]
      norm_num
    rw [hpt, norm_zero, zero_pow (by norm_num)]
    positivity
  · rw [ecalPt_norm_sq_eq lam hlam u hE]
    have hS : 0 ≤ Real.sinh (lam * u.im) ^ 2 := sq_nonneg _
    have hkey := div_cos_sq_add_le_inv_sin_sq (lam * u.re) (Real.sinh (lam * u.im) ^ 2)
      hS hsin_pos
    have h2' : lam ^ 2 * ((Real.cos (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2) /
        (Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2))
        ≤ lam ^ 2 * (1 / Real.sin (lam * u.re) ^ 2) :=
      mul_le_mul_of_nonneg_left hkey (sq_nonneg lam)
    have hrhs : lam ^ 2 * (1 / Real.sin (lam * u.re) ^ 2)
        = lam ^ 2 / (Real.sin (lam * u.re)) ^ 2 := by ring
    linarith [h2', hrhs.le, hrhs.ge]

end Work.PARIMPL2.Direct
