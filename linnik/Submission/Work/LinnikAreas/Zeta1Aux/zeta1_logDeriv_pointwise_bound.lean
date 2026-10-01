import Mathlib
import Submission.Work.LinnikAreas.Zeta1Aux.CommonsImports
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_exists_goodR_segment
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_growth_disk6
import Submission.Work.LinnikAreas.Zeta1Aux.log_one_add_mul_pow_le
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_divisor_sum_bound

namespace Work.LinnikAreas.Zeta1Aux

open Complex Filter Metric Set
open scoped Real Topology BigOperators

/-- Elementary arithmetic glue: for `a, b, L, d ≥ 0`-ish as below,
`a·L + (b/d)·L ≤ (a+b+1)·L·(L + 1/d)`. -/
private lemma arith_glue {a b L d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hL0 : 0 ≤ L) (hL1 : 1 ≤ L)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    a * L + b / d * L ≤ (a + b + 1) * L * (L + 1 / d) := by
  have hdpos : 0 < 1 / d := one_div_pos.mpr hd
  have h1d : 1 ≤ 1 / d := by rw [one_div]; exact (one_le_inv₀ hd).mpr hd1
  have hY1 : 1 ≤ L + 1 / d := by linarith
  have hY0 : 0 ≤ L + 1 / d := by linarith
  have key1 : a * L ≤ a * L * (L + 1 / d) := by
    have := mul_nonneg ha hL0
    nlinarith [this, hY1]
  have key2 : b / d * L ≤ b * L * (L + 1 / d) := by
    have hbd : b / d * L = b * (1 / d) * L := by ring
    rw [hbd]
    have hbL : 0 ≤ b * L := mul_nonneg hb hL0
    calc b * (1 / d) * L = (b * L) * (1 / d) := by ring
      _ ≤ (b * L) * (L + 1 / d) := mul_le_mul_of_nonneg_left (by linarith) hbL
      _ = b * L * (L + 1 / d) := by ring
  have key3 : a * L * (L + 1 / d) + b * L * (L + 1 / d) ≤ (a + b + 1) * L * (L + 1 / d) := by
    nlinarith [mul_nonneg hL0 hY0]
  linarith

/-- **Pointwise bound for `ζ₁'/ζ₁` on the segment `[-1/2, 2]` at a good height.**

There is `C > 0` such that for every `v` with `|v| ≥ 7` and every `δ ∈ (0,1]` such that no
zero of `riemannZeta₁` has `|Im ρ - v| < δ`, one has, for every `x ∈ [-1/2, 2]`,

  `‖ζ₁'/ζ₁ (x + i v)‖ ≤ C * log (|v| + 3) * (log (|v| + 3) + 1/δ)`.

Route: choose `R ∈ [11/2, 6]` such that neither circle `‖w - c‖ = R` nor `‖w - c‖ = R/2`
(`c := 2 + i v`) contains a zero of `ζ₁` (finite evasion, cf.
`Commons.NumberTheory.Linnik.goodRadius_pair` / `exists_notMem_Ioc_of_finite`; the zeros in
`closedBall c 6` are finite since `ζ₁` is entire and not identically zero — e.g. via
`Commons.NumberTheory.Zeta.zetaZeroBall`).  On the outer
circle one has `Re w ∈ [-4, 8]` and `|Im w| ≥ 1`, hence
`‖ζ₁ w‖ = ‖w - 1‖ * ‖ζ w‖ ≤ (|v| + 15) * C * (|v| + 9)^12` by `zeta_strip_polyGrowth`
(`-2 ≤ Re ≤ 3`), `hgrowth` (`-4 ≤ Re ≤ -1`) and `zeta_norm_le_const_of_three_le_re`
(`Re ≥ 3`); together with `‖ζ₁ c‖ ≥ 1/4` (`zeta1_re_two_lower`) this gives
`log A ≪ log (|v| + 3)` where `A` is the ratio of the sup on the circle to `‖ζ₁ c‖`.
Then `Commons.Analysis.Complex.logDeriv_sub_divisor_le` with `α := 5/11`
(note `‖s - c‖ = |x - 2| ≤ 5/2 = α * 11/2 ≤ α * R` and `α < 1/2`) gives

  `‖ζ₁'/ζ₁ s‖ ≤ 4 * log A / (R * (1/11)^2) + ∑ᶠ u, divisor(ζ₁, closedBall c (R/2)) u / ‖s - u‖`

for `s = x + i v` with `ζ₁ s ≠ 0` (if `ζ₁ s = 0` then `logDeriv ζ₁ s = 0` and there is nothing
to prove).  Every zero `u` of the divisor sum satisfies `|u.im - v| ≤ R/2 ≤ 3`, hence
`‖s - u‖ ≥ |u.im - v| ≥ δ`, and the number of such zeros with multiplicity is at most
`C₀ * log (|v| + 3)` by `hcount` (a zero in `closedBall c (R/2)` lies in `closedBall 0 (|v| + 6)`
since `‖u‖ ≤ R/2 + |2 + iv| ≤ 3 + |v| + 2`, so
`Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le` compares the divisors).
This yields `‖ζ₁'/ζ₁ s‖ ≤ C₁ * log (|v| + 3) + (C₀ / δ) * log (|v| + 3)`, which is of the
announced shape since `log (|v| + 3) ≥ 1` and `1/δ ≥ 1`. -/
theorem zeta1_logDeriv_pointwise_bound
    (hcount : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0)) ≤ C₀ * Real.log (|t| + 3))
    (hgrowth : ∃ Cg : ℝ, 0 < Cg ∧ ∀ σ t : ℝ, -4 ≤ σ → σ ≤ -1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ Cg * (|t| + 3) ^ 12) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, 7 ≤ |v| → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - v|) →
      ∀ x : ℝ, x ∈ Set.Icc (-(1 / 2)) 2 →
        ‖logDeriv riemannZeta₁ ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤
          C * Real.log (|v| + 3) * (Real.log (|v| + 3) + 1 / δ) := by
  rcases hcount with ⟨C₀, hC₀pos, hcountspec⟩
  rcases zeta1_growth_disk6 hgrowth with ⟨G, hGpos, hGspec⟩
  rcases log_one_add_mul_pow_le G hGpos with ⟨C₂, hC₂pos, hC₂spec⟩
  refine ⟨88 * C₂ + C₀ + 1, by positivity, ?_⟩
  intro v hv δ hδpos hδle1 hsep x hx
  rcases zeta1_exists_goodR_segment v with ⟨R, hRlo, hRhi, hcirc, hcirc2⟩
  have hRpos : 0 < R := by linarith
  set c : ℂ := (2 : ℂ) + Complex.I * (v : ℂ) with hcdef
  set s : ℂ := (x : ℂ) + (v : ℂ) * Complex.I with hsdef
  set A : ℝ := 1 + 4 * G * (|v| + 9) ^ 13 with hAdef
  have hA1 : (1 : ℝ) ≤ A := by
    rw [hAdef]
    have : (0 : ℝ) ≤ 4 * G * (|v| + 9) ^ 13 := by positivity
    linarith
  have hζclow : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ c‖ := by
    rw [hcdef]; exact Commons.NumberTheory.Zeta.zeta1_re_two_lower v
  have hζcne : riemannZeta₁ c ≠ 0 := by
    intro h0; rw [h0] at hζclow; simp at hζclow; linarith
  have hAb : ∀ w : ℂ, ‖w - c‖ = R → ‖riemannZeta₁ w‖ ≤ A * ‖riemannZeta₁ c‖ := by
    intro w hw
    have hw6 : ‖w - c‖ ≤ 6 := by rw [hw]; exact hRhi
    have hgw : ‖riemannZeta₁ w‖ ≤ G * (|v| + 9) ^ 13 :=
      hGspec v hv w hw6
    have h4A : 4 * G * (|v| + 9) ^ 13 ≤ A := by rw [hAdef]; linarith
    calc ‖riemannZeta₁ w‖ ≤ G * (|v| + 9) ^ 13 := hgw
      _ = 4 * G * (|v| + 9) ^ 13 * (1 / 4) := by ring
      _ ≤ A * ‖riemannZeta₁ c‖ := mul_le_mul h4A hζclow (by norm_num) (by linarith)
  have hlogA : Real.log A ≤ C₂ * Real.log (|v| + 3) := by
    rw [hAdef]; exact hC₂spec v hv
  have hs_dist : ‖s - c‖ ≤ (5 / 11) * R := by
    have h1 : s - c = ((x - 2 : ℝ) : ℂ) := by
      rw [hsdef, hcdef]; apply Complex.ext <;> simp <;> ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    have hx2 : |x - 2| ≤ 5 / 2 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have h5 : (5 : ℝ) / 2 < (5 / 11) * R := by nlinarith [hRlo]
    linarith
  rcases eq_or_ne (riemannZeta₁ s) 0 with hzero | hne
  · have hs_log : logDeriv riemannZeta₁ s = 0 := by
      rw [logDeriv_apply, hzero, div_zero]
    have hL0 : 0 ≤ Real.log (|v| + 3) := Real.log_nonneg (by linarith [abs_nonneg v])
    have h1dpos : 0 < 1 / δ := one_div_pos.mpr hδpos
    have hCpos : (0 : ℝ) ≤ 88 * C₂ + C₀ + 1 := by positivity
    have hprod : 0 ≤ (88 * C₂ + C₀ + 1) * Real.log (|v| + 3) *
        (Real.log (|v| + 3) + 1 / δ) :=
      mul_nonneg (mul_nonneg hCpos hL0) (by linarith)
    rw [hs_log, norm_zero]
    exact hprod
  · have hb := Commons.Analysis.Complex.logDeriv_sub_divisor_le (f := riemannZeta₁)
      (c := c) (R := R) (A := A) (α := 5 / 11) hRpos hA1 (by norm_num) (by norm_num)
      (fun z _ => differentiable_riemannZeta₁.analyticAt z) hζcne hcirc hcirc2 hAb hs_dist hne
    set S : ℂ := ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (R / 2))) u : ℤ) : ℂ) *
        (1 / (s - u)) with hSdef
    have hSbound : ‖S‖ ≤ C₀ / δ * Real.log (|v| + 3) := by
      have h := zeta1_divisor_sum_bound (C₀ := C₀) hC₀pos hcountspec
        (v := v) (δ := δ) (R := R) (x := x) hv hδpos hRpos hRhi hsep
      simpa [hSdef, hsdef, hcdef] using h
    have hBC : ‖logDeriv riemannZeta₁ s - S‖ ≤ 4 * Real.log A / (R * (1 - 2 * (5 / 11)) ^ 2) := by
      simpa [hSdef] using hb
    have hL0 : 0 ≤ Real.log (|v| + 3) := Real.log_nonneg (by linarith [abs_nonneg v])
    have hL1 : 1 ≤ Real.log (|v| + 3) := by
      have hexp : Real.exp 1 ≤ |v| + 3 := by
        have he := Real.exp_one_lt_three
        have h0 : (0 : ℝ) ≤ |v| := abs_nonneg v
        linarith
      exact (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < |v| + 3)).mpr hexp
    have hBC' : 4 * Real.log A / (R * (1 - 2 * (5 / 11)) ^ 2) ≤ 88 * C₂ * Real.log (|v| + 3) := by
      have hnum : 0 ≤ 484 * C₂ * Real.log (|v| + 3) := by positivity
      have hR2 : (11 / 2 : ℝ) ≤ R := le_of_lt hRlo
      have hden : (1 - 2 * (5 / 11)) ^ 2 = (1 / 121 : ℝ) := by norm_num
      calc 4 * Real.log A / (R * (1 - 2 * (5 / 11)) ^ 2)
          = 484 * Real.log A / R := by rw [hden]; ring
        _ ≤ 484 * (C₂ * Real.log (|v| + 3)) / R := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hRpos)
            nlinarith [hlogA]
        _ = 484 * C₂ * Real.log (|v| + 3) / R := by ring
        _ ≤ 484 * C₂ * Real.log (|v| + 3) / (11 / 2) :=
            div_le_div_of_nonneg_left hnum (by norm_num) hR2
        _ = 88 * C₂ * Real.log (|v| + 3) := by ring
    have hmain : ‖logDeriv riemannZeta₁ s‖ ≤
        88 * C₂ * Real.log (|v| + 3) + C₀ / δ * Real.log (|v| + 3) := by
      have hnorm : ‖logDeriv riemannZeta₁ s‖ ≤ ‖logDeriv riemannZeta₁ s - S‖ + ‖S‖ := by
        simpa using norm_add_le (logDeriv riemannZeta₁ s - S) S
      linarith [hBC, hBC', hSbound, hnorm]
    have hfinal := arith_glue (a := 88 * C₂) (b := C₀) (L := Real.log (|v| + 3)) (d := δ)
      (by positivity) (le_of_lt hC₀pos) hL0 hL1 hδpos hδle1
    have hgoal : ‖logDeriv riemannZeta₁ s‖ ≤ (88 * C₂ + C₀ + 1) * Real.log (|v| + 3) *
        (Real.log (|v| + 3) + 1 / δ) := by
      linarith [hmain, hfinal]
    exact hgoal

end Work.LinnikAreas.Zeta1Aux
