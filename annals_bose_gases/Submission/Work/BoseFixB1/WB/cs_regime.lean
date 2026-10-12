import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

/-- Dilute-regime consequence of the Cauchy–Schwarz type inequality.

Given `W * |s - μ| ≤ √Ct * √(W * (1 + s/μ))`, `Ct ≤ β W μ² γ²` and the
smallness `3 β γ² ≤ 1`, one has `|s - μ| ≤ √(3β) μ γ`.

The proof squares the Cauchy–Schwarz bound, uses `Ct ≤ β W μ² γ²` to get
`(s/μ - 1)² ≤ β γ² (1 + s/μ)`, then combines `3 β γ² ≤ 1` with
`0 ≤ 1 + s/μ` to deduce `3 (s/μ - 1)² ≤ 1 + s/μ`, which forces `s/μ ≤ 2`
(equivalently `1 + s/μ ≤ 3`).  Hence `(s - μ)² ≤ 3 β μ² γ²` and taking
square roots gives the claim. -/
theorem cs_regime {W Ct s μ γ β : ℝ}
    (hW : 0 < W) (hμ : 0 < μ) (hCt : 0 ≤ Ct) (hs0 : 0 ≤ s) (hγ : 0 ≤ γ) (hβ : 0 ≤ β)
    (hCS : W * |s - μ| ≤ Real.sqrt Ct * Real.sqrt (W * (1 + s / μ)))
    (hbound : Ct ≤ β * W * μ ^ 2 * γ ^ 2)
    (hsmall : 3 * β * γ ^ 2 ≤ 1) :
    |s - μ| ≤ Real.sqrt (3 * β) * μ * γ := by
  have hμle : (0 : ℝ) ≤ μ := hμ.le
  have hsdiv : 0 ≤ s / μ := div_nonneg hs0 hμle
  have hs1 : 0 ≤ 1 + s / μ := by linarith
  have hX : 0 ≤ W * (1 + s / μ) := mul_nonneg hW.le hs1
  have hL : 0 ≤ W * |s - μ| := mul_nonneg hW.le (abs_nonneg _)
  -- Square the Cauchy–Schwarz type hypothesis.
  have hsq : (W * |s - μ|) ^ 2 ≤ Ct * (W * (1 + s / μ)) := by
    have h1 : W * |s - μ| ≤ Real.sqrt (Ct * (W * (1 + s / μ))) := by
      rw [Real.sqrt_mul hCt]; exact hCS
    have h2 : (W * |s - μ|) * (W * |s - μ|) ≤
        Real.sqrt (Ct * (W * (1 + s / μ))) * Real.sqrt (Ct * (W * (1 + s / μ))) :=
      mul_self_le_mul_self hL h1
    have h3 := Real.sq_sqrt (mul_nonneg hCt hX)
    nlinarith [h2, h3]
  have hsq' : W ^ 2 * (s - μ) ^ 2 ≤ Ct * (W * (1 + s / μ)) := by
    have h := hsq
    rw [mul_pow, sq_abs] at h
    exact h
  have hW2 : W * (s - μ) ^ 2 ≤ Ct * (1 + s / μ) := by nlinarith [hsq', hW]
  -- Use the bound on `Ct`.
  have hmem : (s - μ) ^ 2 ≤ β * μ ^ 2 * γ ^ 2 * (1 + s / μ) := by
    have hb : Ct * (1 + s / μ) ≤ β * W * μ ^ 2 * γ ^ 2 * (1 + s / μ) :=
      mul_le_mul_of_nonneg_right hbound hs1
    nlinarith [hW2, hb, hW]
  have hkey : (s / μ - 1) ^ 2 = (s - μ) ^ 2 / μ ^ 2 := by
    field_simp
  have h6 : (s / μ - 1) ^ 2 ≤ β * γ ^ 2 * (1 + s / μ) := by
    rw [hkey]
    have hcan : β * μ ^ 2 * γ ^ 2 * (1 + s / μ) / μ ^ 2 = β * γ ^ 2 * (1 + s / μ) := by
      field_simp
    calc (s - μ) ^ 2 / μ ^ 2 ≤ (β * μ ^ 2 * γ ^ 2 * (1 + s / μ)) / μ ^ 2 :=
          div_le_div_of_nonneg_right hmem (by positivity)
      _ = β * γ ^ 2 * (1 + s / μ) := hcan
  -- The smallness hypothesis forces `s / μ ≤ 2`.
  have hvle : s / μ ≤ 2 := by
    by_contra hc
    rw [not_le] at hc
    have hprod : 0 ≤ (1 - 3 * β * γ ^ 2) * (1 + s / μ) :=
      mul_nonneg (by linarith [hsmall]) hs1
    have h3v : 0 ≤ 3 * (s / μ) - 1 := by linarith [hc]
    have hprod2 : 0 ≤ (s / μ - 2) * (3 * (s / μ) - 1) :=
      mul_nonneg (by linarith [hc]) h3v
    nlinarith [h6, hprod, hprod2]
  have hfinal : (s - μ) ^ 2 ≤ 3 * β * μ ^ 2 * γ ^ 2 := by
    have h13 : 1 + s / μ ≤ 3 := by linarith [hvle]
    have hbb : β * μ ^ 2 * γ ^ 2 * (1 + s / μ) ≤ β * μ ^ 2 * γ ^ 2 * 3 := by
      apply mul_le_mul_of_nonneg_left h13; positivity
    linarith [hmem, hbb]
  have h8 : |s - μ| ≤ Real.sqrt (3 * β * μ ^ 2 * γ ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hfinal
  have h9 : Real.sqrt (3 * β * μ ^ 2 * γ ^ 2) = Real.sqrt (3 * β) * μ * γ := by
    have harg : 3 * β * μ ^ 2 * γ ^ 2 = (3 * β) * (μ * γ) ^ 2 := by ring
    rw [harg, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3 * β),
      Real.sqrt_sq (mul_nonneg hμle hγ)]
    ring
  rw [h9] at h8
  exact h8

end Work.BoseFixB1.WB
