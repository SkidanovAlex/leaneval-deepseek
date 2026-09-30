import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- Packaging of the horizontal-edge bound of the twisted Perron rectangle
(`Work.BMF.liouville.norm_horiz_edge_le`): with `T ≥ L^2 exp(L^{1/10})`, `y = exp L`,
`0 < σ₁ < 1` and `log (|u| + T + 3) ≤ 2 L^{5/4}`, the raw bound
`B log²(|u|+T+3) y^{1+1/log y} ((1+1/log y) - σ₁)/T`
is at most `8 e B L^{1/2} y exp(-L^{1/10})`.  Pure real inequality:
`log² ≤ (2L^{5/4})² = 4L^{5/2}`, `(1+1/log y) - σ₁ ≤ 1 + 1/log y ≤ 2` (using `0 < σ₁`),
`y^{1+1/log y} = y·e`, `1/T ≤ 1/(L² exp(L^{1/10}))`. -/
lemma zetaTwTopEdge_absorb {B L T y σ₁ u : ℝ} (hB : 0 ≤ B) (hL1 : 1 ≤ L) (hT : 0 < T)
    (hTge : L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) ≤ T) (hy : y = Real.exp L)
    (hσ₁pos : 0 < σ₁) (hσ₁ : σ₁ < 1)
    (hlog : Real.log (|u| + T + 3) ≤ 2 * L ^ (5 / 4 : ℝ)) :
    B * (Real.log (|u| + T + 3)) ^ 2 * y ^ (1 + 1 / Real.log y) *
        ((1 + 1 / Real.log y) - σ₁) / T
      ≤ 8 * Real.exp 1 * B * L ^ (1 / 2 : ℝ) * y * Real.exp (-(L ^ (1 / 10 : ℝ))) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLnonneg : (0 : ℝ) ≤ L := le_of_lt hLpos
  have hlogy : Real.log y = L := by rw [hy, Real.log_exp]
  have hypos : 0 < y := by rw [hy]; exact Real.exp_pos L
  have hlogy_ge1 : 1 ≤ Real.log y := by rw [hlogy]; exact hL1
  have hlogy_pos : 0 < Real.log y := lt_of_lt_of_le zero_lt_one hlogy_ge1
  have hlogy_ne : Real.log y ≠ 0 := ne_of_gt hlogy_pos
  -- `y^{1 + 1/log y} = y · e`
  have hyrw : y ^ (1 + 1 / Real.log y) = y * Real.exp 1 := by
    rw [Real.rpow_add hypos, Real.rpow_one, Real.rpow_def_of_pos hypos]
    congr 1
    field_simp
  -- nonnegativity of the logarithm
  have hℓnn : 0 ≤ Real.log (|u| + T + 3) := by
    apply Real.log_nonneg
    have := abs_nonneg u
    linarith
  -- `log²(|u|+T+3) ≤ 4 L^{5/2}`
  have hℓ2 : (Real.log (|u| + T + 3)) ^ 2 ≤ 4 * L ^ (5 / 2 : ℝ) := by
    have h45 : (0 : ℝ) ≤ L ^ (5 / 4 : ℝ) := Real.rpow_nonneg hLnonneg _
    have hb : 0 ≤ 2 * L ^ (5 / 4 : ℝ) := by linarith
    have h1 : (Real.log (|u| + T + 3)) ^ 2 ≤ (2 * L ^ (5 / 4 : ℝ)) ^ 2 := by
      nlinarith [hlog, hℓnn, hb]
    have h2 : (2 * L ^ (5 / 4 : ℝ)) ^ 2 = 4 * L ^ (5 / 2 : ℝ) := by
      have hx : (L ^ (5 / 4 : ℝ)) ^ 2 = L ^ (5 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (L ^ (5 / 4 : ℝ)) 2, ← Real.rpow_mul hLnonneg]
        norm_num
      rw [mul_pow, hx]
      norm_num
    linarith
  -- `(1 + 1/log y) - σ₁ ≤ 2` and `≥ 0`
  have hc2 : (1 + 1 / Real.log y) - σ₁ ≤ 2 := by
    have h : 1 / Real.log y ≤ 1 := by rw [div_le_one hlogy_pos]; linarith
    linarith
  have hc0 : 0 ≤ (1 + 1 / Real.log y) - σ₁ := by
    have h : 0 ≤ 1 / Real.log y := by positivity
    linarith
  have hye : 0 < y * Real.exp 1 := mul_pos hypos (Real.exp_pos 1)
  have h4L52 : (0 : ℝ) ≤ 4 * L ^ (5 / 2 : ℝ) := by
    have : (0 : ℝ) ≤ L ^ (5 / 2 : ℝ) := Real.rpow_nonneg hLnonneg _
    linarith
  -- the numerator is at most `8 e B y L^{5/2}`
  have hstep : B * (Real.log (|u| + T + 3)) ^ 2 * y ^ (1 + 1 / Real.log y) *
        ((1 + 1 / Real.log y) - σ₁) ≤ 8 * Real.exp 1 * B * y * L ^ (5 / 2 : ℝ) := by
    rw [hyrw]
    have hA : (Real.log (|u| + T + 3)) ^ 2 * (y * Real.exp 1) ≤
        (4 * L ^ (5 / 2 : ℝ)) * (y * Real.exp 1) :=
      mul_le_mul_of_nonneg_right hℓ2 (le_of_lt hye)
    have hAB : (Real.log (|u| + T + 3)) ^ 2 * (y * Real.exp 1) * ((1 + 1 / Real.log y) - σ₁)
        ≤ (4 * L ^ (5 / 2 : ℝ)) * (y * Real.exp 1) * 2 :=
      mul_le_mul hA hc2 hc0 (mul_nonneg h4L52 (le_of_lt hye))
    have hC := mul_le_mul_of_nonneg_left hAB hB
    calc B * (Real.log (|u| + T + 3)) ^ 2 * (y * Real.exp 1) * ((1 + 1 / Real.log y) - σ₁)
        = B * ((Real.log (|u| + T + 3)) ^ 2 * (y * Real.exp 1) *
            ((1 + 1 / Real.log y) - σ₁)) := by ring
      _ ≤ B * ((4 * L ^ (5 / 2 : ℝ)) * (y * Real.exp 1) * 2) := hC
      _ = 8 * Real.exp 1 * B * y * L ^ (5 / 2 : ℝ) := by ring
  -- clear the denominator `T`
  rw [div_le_iff₀ hT]
  refine le_trans hstep ?_
  have hkey1 : L ^ (1 / 2 : ℝ) * L ^ 2 = L ^ (5 / 2 : ℝ) := by
    rw [show L ^ 2 = L ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_add hLpos]
    norm_num
  have hkey2 : Real.exp (-(L ^ (1 / 10 : ℝ))) * Real.exp (L ^ (1 / 10 : ℝ)) = 1 := by
    rw [Real.exp_neg, inv_mul_cancel₀ (ne_of_gt (Real.exp_pos _))]
  have hcoef : 0 ≤ 8 * Real.exp 1 * B * L ^ (1 / 2 : ℝ) * y *
      Real.exp (-(L ^ (1 / 10 : ℝ))) := by
    have h1 : 0 ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hLnonneg _
    have h2 : 0 ≤ Real.exp (-(L ^ (1 / 10 : ℝ))) := (Real.exp_pos _).le
    positivity
  have hle := mul_le_mul_of_nonneg_left hTge hcoef
  have hkey : 8 * Real.exp 1 * B * L ^ (1 / 2 : ℝ) * y * Real.exp (-(L ^ (1 / 10 : ℝ))) *
        (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)))
      = 8 * Real.exp 1 * B * y * L ^ (5 / 2 : ℝ) := by
    calc 8 * Real.exp 1 * B * L ^ (1 / 2 : ℝ) * y * Real.exp (-(L ^ (1 / 10 : ℝ))) *
          (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)))
        = 8 * Real.exp 1 * B * y * (L ^ (1 / 2 : ℝ) * L ^ 2) *
          (Real.exp (-(L ^ (1 / 10 : ℝ))) * Real.exp (L ^ (1 / 10 : ℝ))) := by ring
      _ = 8 * Real.exp 1 * B * y * L ^ (5 / 2 : ℝ) := by rw [hkey1, hkey2]; ring
  rwa [hkey] at hle

end Work.BMF.liouville
