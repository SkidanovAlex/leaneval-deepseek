import Mathlib
import Submission.Work.OtherCharRepel.LFunctionShiftedReEqTsum
import Submission.Work.LinnikAreas.repelOtherAux.twistedNonneg

/-!
# The four-term pointwise positivity in the other-character case

`Work.LinnikAreas.OtherCharRepel.fourTermPointwise` is the pointwise inequality

`0 ≤ (5/4)·(-ζ′/ζ)(σ) + 2·(-L′/L)(σ+iγ,χ) + 1·(-L′/L)(σ+2iγ,χ²) + (1/4)·(-L′/L)(σ+3iγ,χ³)`

for every Dirichlet character `χ` modulo `q` and every real `σ > 1`.  It is the
Landau/Turán-type positivity input for the λ₁-uniform Deuring–Heilbronn repulsion
in the "other character" case.

The proof is the von Mangoldt expansion.  For `Re s > 1` the logarithmic derivatives
are absolutely convergent Dirichlet series,

`(-ζ′/ζ)(σ) = Σ_n Λ(n) n^{-σ}`,
`(-L′/L)(σ+ijγ,χ^j) = Σ_n Λ(n)·(χ(n)^j · n^{-ijγ})·n^{-σ} = Σ_n Λ(n)·(χ(n) n^{-iγ})^j·n^{-σ}`,

so the four-term expression is

`Σ_n Λ(n) n^{-σ} · [5/4 + 2 Re z_n + Re(z_n²) + (1/4) Re(z_n³)]`, with `z_n = χ(n)·n^{-iγ}`.

Since `‖χ(n)‖ ≤ 1` and `‖n^{-iγ}‖ ≤ 1` we have `‖z_n‖ ≤ 1`, and for every complex `u`
with `‖u‖ ≤ 1` the bracket is nonnegative: writing `u = c + i s`,

`5/4 + 2c + Re(u²) + (1/4) Re(u³) = (1/4)(1+c)(2c+1)² + (1 + 3c/4)(1 - c² - s²) ≥ 0`.

The termwise nonnegativity then gives the asserted inequality.
-/

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter

/-- For `‖u‖ ≤ 1` the Landau quartic combination `5/4 + 2 Re u + Re u² + (1/4) Re u³` is
nonnegative.  With `u = c + i s` the expression equals
`(1/4)(1+c)(2c+1)² + (1 + 3c/4)(1 - c² - s²)`. -/
private lemma quart_nonneg {u : ℂ} (hu : ‖u‖ ≤ 1) :
    0 ≤ (5/4 : ℝ) + 2 * u.re + (u^2).re + (1/4) * (u^3).re := by
  have h1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u, hu]
  have h2 : ‖u‖ ^ 2 = u.re^2 + u.im^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs : u.re^2 + u.im^2 ≤ 1 := by rw [← h2]; exact h1
  have hc : -1 ≤ u.re := by
    have h3 : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
    have h4 : |u.re| ≤ 1 := le_trans h3 hu
    have := abs_le.mp h4
    linarith [this.1]
  have h2re : (u^2).re = u.re^2 - u.im^2 := by rw [pow_two, Complex.mul_re]; ring
  have h3re : (u^3).re = u.re^3 - 3 * u.re * u.im^2 := by
    rw [show u^3 = u^2 * u by ring, Complex.mul_re, h2re]
    have h2im : (u^2).im = 2 * u.re * u.im := by rw [pow_two, Complex.mul_im]; ring
    rw [h2im]; ring
  rw [h2re, h3re]
  have hfact : (5/4 : ℝ) + 2 * u.re + (u.re^2 - u.im^2) + (1/4) * (u.re^3 - 3*u.re*u.im^2)
      = (1/4) * ((1 + u.re) * (2*u.re + 1)^2) + (1 + 3*u.re/4) * (1 - u.re^2 - u.im^2) := by
    ring
  rw [hfact]
  refine add_nonneg ?_ ?_
  · exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) (sq_nonneg _))
  · exact mul_nonneg (by linarith) (by linarith)

/-- `‖n^{-iγ}‖ ≤ 1` for every natural `n` (with the convention `0^z = 0` for `z ≠ 0`). -/
private lemma norm_cpow_imI_le_one (n : ℕ) (γ : ℝ) : ‖(n : ℂ)^(-(Complex.I * (γ : ℂ)))‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rcases eq_or_ne (-(Complex.I * (γ : ℂ))) 0 with hw | hw
    · rw [Nat.cast_zero, hw]; norm_num
    · rw [Nat.cast_zero, Complex.zero_cpow hw, norm_zero]; norm_num
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [Complex.norm_natCast_cpow_of_pos hpos]
    have hzero : (-(Complex.I * (γ : ℂ))).re = 0 := by simp
    rw [hzero]; norm_num

/-- `‖χ(n)·n^{-iγ}‖ ≤ 1`. -/
private lemma norm_z_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (γ : ℝ) (n : ℕ) :
    ‖(χ (n : ZMod q)) * (n : ℂ)^(-(Complex.I * (γ : ℂ)))‖ ≤ 1 := by
  calc ‖(χ (n : ZMod q)) * (n : ℂ)^(-(Complex.I * (γ : ℂ)))‖
      ≤ ‖χ (n : ZMod q)‖ * ‖(n : ℂ)^(-(Complex.I * (γ : ℂ)))‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (χ.norm_le_one _) (norm_cpow_imI_le_one n γ) (norm_nonneg _)
        (by norm_num)
    _ = 1 := mul_one 1

/-- `χ²(n)·n^{-2iγ} = (χ(n)·n^{-iγ})²`. -/
private lemma pow2_cpow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) (γ : ℝ) :
    ((χ^2) (n : ZMod q)) * (n : ℂ)^(-(Complex.I * ((2*γ : ℝ) : ℂ)))
      = ((χ (n : ZMod q)) * (n : ℂ)^(-(Complex.I * (γ : ℂ))))^2 := by
  rw [MulChar.pow_apply' χ (n := 2) (by norm_num)]
  have h : (-(Complex.I * ((2*γ : ℝ) : ℂ))) = ((2:ℕ):ℂ) * (-(Complex.I * (γ : ℂ))) := by
    push_cast; ring
  rw [h, Complex.cpow_nat_mul (n := 2), mul_pow]

/-- `χ³(n)·n^{-3iγ} = (χ(n)·n^{-iγ})³`. -/
private lemma pow3_cpow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) (γ : ℝ) :
    ((χ^3) (n : ZMod q)) * (n : ℂ)^(-(Complex.I * ((3*γ : ℝ) : ℂ)))
      = ((χ (n : ZMod q)) * (n : ℂ)^(-(Complex.I * (γ : ℂ))))^3 := by
  rw [MulChar.pow_apply' χ (n := 3) (by norm_num)]
  have h : (-(Complex.I * ((3*γ : ℝ) : ℂ))) = ((3:ℕ):ℂ) * (-(Complex.I * (γ : ℂ))) := by
    push_cast; ring
  rw [h, Complex.cpow_nat_mul (n := 3), mul_pow]

/-- Associating a sum of four absolutely convergent series into a single series. -/
private lemma tsum_four_add {a b c d : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (hc : Summable c) (hd : Summable d) :
    tsum a + tsum b + tsum c + tsum d = tsum (fun n : ℕ => ((a n + b n) + c n) + d n) := by
  rw [← Summable.tsum_add ha hb, ← Summable.tsum_add (ha.add hb) hc,
    ← Summable.tsum_add ((ha.add hb).add hc) hd]

/-- **The four-term pointwise positivity.**  For every Dirichlet character `χ` modulo `q` and
every real `σ > 1`,

`0 ≤ (5/4)·Re(-ζ′/ζ)(σ) + 2·Re(-L′/L)(σ+iγ,χ) + Re(-L′/L)(σ+2iγ,χ²) + (1/4)·Re(-L′/L)(σ+3iγ,χ³)`. -/
theorem fourTermPointwise {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ γ : ℝ} (hσ : 1 < σ) :
    0 ≤ (5 / 4 : ℝ) * (-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))).re
      + 2 * (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
      + 1 * (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
          ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re
      + (1 / 4 : ℝ) * (-logDeriv (DirichletCharacter.LFunction (χ ^ 3))
          ((σ : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).re := by
  -- normalise the three shifted points to the shape `σ + I·t`
  rw [show (σ : ℂ) + (γ : ℂ) * Complex.I = (σ : ℂ) + Complex.I * (γ : ℂ) from by rw [mul_comm],
      show (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I
        = (σ : ℂ) + Complex.I * ((2 * γ : ℝ) : ℂ) from by rw [mul_comm],
      show (σ : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I
        = (σ : ℂ) + Complex.I * ((3 * γ : ℝ) : ℂ) from by rw [mul_comm]]
  -- normalise the `ζ` term to the `-logDeriv` shape
  rw [show (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        = (-(logDeriv riemannZeta (σ : ℂ))).re from by rw [logDeriv_apply, neg_div]]
  -- the four von Mangoldt series identities
  have hz : (-(logDeriv riemannZeta (σ : ℂ))).re
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
    have h1 : (-(logDeriv riemannZeta (σ : ℂ))).re
        = (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
      rw [logDeriv_apply, neg_div]
    exact h1.trans (Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re σ hσ).symm
  have hL1 : (-(logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (γ : ℂ)))).re
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * ((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re := by
    rw [Work.OtherCharRepel.LFunctionShiftedReEqTsum χ γ hσ]
    exact tsum_congr (fun n => by ring)
  have hL2 : (-(logDeriv (DirichletCharacter.LFunction (χ^2))
        ((σ : ℂ) + Complex.I * ((2 * γ : ℝ) : ℂ)))).re
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * (((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))^2).re := by
    rw [Work.OtherCharRepel.LFunctionShiftedReEqTsum (χ^2) (2*γ) hσ]
    refine tsum_congr (fun n => ?_)
    rw [pow2_cpow χ n γ]
    ring
  have hL3 : (-(logDeriv (DirichletCharacter.LFunction (χ^3))
        ((σ : ℂ) + Complex.I * ((3 * γ : ℝ) : ℂ)))).re
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * (((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))^3).re := by
    rw [Work.OtherCharRepel.LFunctionShiftedReEqTsum (χ^3) (3*γ) hσ]
    refine tsum_congr (fun n => ?_)
    rw [pow3_cpow χ n γ]
    ring
  rw [hz, hL1, hL2, hL3]
  -- summability of the four series
  have hsmA : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
    refine (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow (σ := σ) hσ).congr
      (fun n => ?_)
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hsm_of : ∀ (z : ℕ → ℂ), (∀ n, ‖z n‖ ≤ 1) →
      Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        * (z n).re) := by
    intro z hzle
    refine Summable.of_norm_bounded hsmA (fun n => ?_)
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hn : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hb : |(z n).re| ≤ 1 := le_trans (Complex.abs_re_le_norm _) (hzle n)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΛ, abs_of_nonneg hn]
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * |(z n).re|
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * 1 :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg hΛ hn)
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by ring
  have hzn : ∀ n : ℕ, ‖(χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ ≤ 1 :=
    fun n => norm_z_le_one χ γ n
  have hsmB := hsm_of _ hzn
  have hsmC : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
      * (((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))^2).re) :=
    hsm_of _ (fun n => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hzn n))
  have hsmD : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
      * (((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))^3).re) :=
    hsm_of _ (fun n => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hzn n))
  -- fold the coefficients into the series and combine into a single series
  rw [← Summable.tsum_mul_left (5/4) hsmA, ← Summable.tsum_mul_left 2 hsmB,
      ← Summable.tsum_mul_left 1 hsmC, ← Summable.tsum_mul_left (1/4) hsmD]
  rw [tsum_four_add (hsmA.mul_left (5/4)) (hsmB.mul_left 2) (hsmC.mul_left 1)
      (hsmD.mul_left (1/4))]
  -- termwise nonnegativity
  refine tsum_nonneg (fun n => ?_)
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hn : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hq := quart_nonneg (hzn n)
  have hsplit : ((5/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
        + 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * ((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re))
      + 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * (((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))^2).re)
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * (((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))^3).re)
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        * ((5/4 : ℝ) + 2 * ((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re
          + (((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))^2).re
          + (1/4) * (((χ (n : ZMod q)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))^3).re) := by ring
  rw [hsplit]
  exact mul_nonneg (mul_nonneg hΛ hn) hq

end Work.LinnikAreas.OtherCharRepel
